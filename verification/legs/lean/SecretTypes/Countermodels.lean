/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

Lean leg (PROOF-POLICY §2, route `re-proved`) of secret-types N-8: each law
generic TINI uses is necessary.  Mirrors src/SecretTypes/Countermodels.agda
module by module: drop one law, keep the typing rules, and a well-typed
program leaks, so `TINI` is refuted at that signature.  Lean core only, no
axioms.
-/
import SecretTypes.Two

namespace SecretTypes.Countermodels
open SecretTypes SecretTypes.Two Label Var

/-- `std`: `lo` public, `hi` secret. -/
def std : two.Var → Label
  | lo => L
  | hi => H

/-- The two-point signature with a given join. -/
def withJoin (j : Label → Label → Label) : Signature where
  Carrier := Label
  le := le
  join := j
  bot := L

/-- Seen by the observer at `L`: exactly the labels below `L`. -/
def belowL : Label → Type := fun x => le x L

theorem agree_s₀_s₁ (S : Signature) (hS : S.Carrier = Label) (lab' : two.Var → S.Carrier)
    (sees : S.Carrier → Type) (hhi : sees (lab' hi) → False) :
    Agree S lab' sees s₀ s₁ := fun
  | lo, _ => rfl
  | hi, v => (hhi v).elim

/-! `NoUpper₁`: the join `x ⊔ʳ y = y` keeps `⊔-upper₂` and drops `⊔-upper₁`. -/
namespace NoUpper₁

def joinR : Label → Label → Label := fun _ y => y

def S : Signature := withJoin joinR

def upper₂ : ∀ x y : Label, le y (joinR x y)
  | _, L => ()
  | _, H => ()

theorem not_upper₁ : (∀ x y : Label, le x (joinR x y)) → False :=
  fun h => nomatch (h H L : Empty)

/-- `implicit = ifz (var hi) (lo ≔ lit 0) (lo ≔ lit 1)`, typed at `L`. -/
def implicitFlow : Cmd two := .ifz (.var hi) (.assign lo (.lit 0)) (.assign lo (.lit 1))

def typed : Typed S std L implicitFlow := .ifz (.assign ()) (.assign ())

theorem refutes : TINI S std belowL → False := fun tini =>
  nomatch (tini 1 1 typed (agree_s₀_s₁ S rfl std belowL (fun v => nomatch (v : Empty)))
    rfl rfl lo () : 0 = 1)

end NoUpper₁

/-! `NoUpper₂`: the join `x ⊔ˡ y = x` keeps `⊔-upper₁` and drops `⊔-upper₂`. -/
namespace NoUpper₂

def joinL : Label → Label → Label := fun x _ => x

def S : Signature := withJoin joinL

def upper₁ : ∀ x y : Label, le x (joinL x y)
  | L, _ => ()
  | H, _ => ()

theorem not_upper₂ : (∀ x y : Label, le y (joinL x y)) → False :=
  fun h => nomatch (h L H : Empty)

/-- `explicit = lo ≔ var hi`, typed at `L`. -/
def explicitFlow : Cmd two := .assign lo (.var hi)

def typed : Typed S std L explicitFlow := .assign ()

theorem refutes : TINI S std belowL → False := fun tini =>
  nomatch (tini 1 1 typed (agree_s₀_s₁ S rfl std belowL (fun v => nomatch (v : Empty)))
    rfl rfl lo () : 0 = 1)

end NoUpper₂

/-! `NoDownClosure`: the observer that sees exactly `H` is not down-closed. -/
namespace NoDownClosure

def sees : Label → Type := fun x => PLift (x = H)

theorem not_down_closed : (∀ {x y : Label}, le x y → sees y → sees x) → False :=
  fun h => nomatch (h (x := L) (y := H) () ⟨rfl⟩).down

def S : Signature := withJoin join

/-- `up = hi ≔ var lo`, typed at `L`. -/
def up : Cmd two := .assign hi (.var lo)

def typed : Typed S std L up := .assign ()

def t₀ : Store two := pair 0 0
def t₁ : Store two := pair 1 0

theorem agree : Agree S std sees t₀ t₁ := fun
  | lo, v => nomatch v.down
  | hi, _ => rfl

theorem refutes : TINI S std sees → False := fun tini =>
  nomatch (tini 1 1 typed agree rfl rfl hi ⟨rfl⟩ : 0 = 1)

end NoDownClosure

/-! `NoTrans`: without `⊑-trans`, "flows to `o`" can fail to be down-closed,
and TINI fails for that principal observer. -/
namespace NoTrans

inductive P where
  | B | H' | M | L' | T

open P

inductive Le : P → P → Type where
  | refl {x} : Le x x
  | bot {x} : Le B x
  | top {x} : Le x T
  | HM : Le H' M
  | ML : Le M L'

def join : P → P → P
  | B, y => y
  | T, _ => T
  | H', B => H'
  | H', H' => H'
  | H', M => M
  | H', L' => T
  | H', T => T
  | M, B => M
  | M, H' => M
  | M, M => M
  | M, L' => L'
  | M, T => T
  | L', B => L'
  | L', H' => T
  | L', M => L'
  | L', L' => L'
  | L', T => T

def upper₁ : ∀ x y : P, Le x (join x y)
  | B, _ => .bot
  | T, _ => .refl
  | H', B => .refl
  | H', H' => .refl
  | H', M => .HM
  | H', L' => .top
  | H', T => .top
  | M, B => .refl
  | M, H' => .refl
  | M, M => .refl
  | M, L' => .ML
  | M, T => .top
  | L', B => .refl
  | L', H' => .top
  | L', M => .refl
  | L', L' => .refl
  | L', T => .top

def upper₂ : ∀ x y : P, Le y (join x y)
  | B, _ => .refl
  | T, _ => .top
  | H', B => .bot
  | H', H' => .refl
  | H', M => .refl
  | H', L' => .top
  | H', T => .refl
  | M, B => .bot
  | M, H' => .HM
  | M, M => .refl
  | M, L' => .refl
  | M, T => .refl
  | L', B => .bot
  | L', H' => .top
  | L', M => .ML
  | L', L' => .refl
  | L', T => .refl

theorem not_trans : (∀ {x y z : P}, Le x y → Le y z → Le x z) → False :=
  fun t => nomatch (t Le.HM Le.ML : Le H' L')

def S : Signature where
  Carrier := P
  le := Le
  join := join
  bot := B

def label : two.Var → P
  | lo => M
  | hi => H'

/-- `explicit = lo ≔ var hi`, typed at `B` (needs only `H′ ≤ M`). -/
def explicitFlow : Cmd two := .assign lo (.var hi)

def typed : Typed S label B explicitFlow := .assign .HM

def belowL' : P → Type := fun x => Le x L'

theorem agree : Agree S label belowL' s₀ s₁ := fun
  | lo, _ => rfl
  | hi, v => nomatch (v : Le H' L')

theorem refutes : TINI S label belowL' → False := fun tini =>
  nomatch (tini 1 1 typed agree rfl rfl lo Le.ML : 0 = 1)

end NoTrans

end SecretTypes.Countermodels
