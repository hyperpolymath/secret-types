/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

Lean leg (PROOF-POLICY §2, route `re-proved`) of secret-types N-1, N-2, N-3
at the two-point lattice and N-9.  Mirrors src/SecretTypes/Lattice.agda,
Lang/Two.agda, Typing.agda, Noninterference.agda, Witness.agda and
Noninterference/OutcomeVisibility.agda.  Lean core only, no axioms.
-/
import SecretTypes.Generic

namespace SecretTypes.Two
open SecretTypes

/-- `Label` of `SecretTypes.Lattice`: `L` public, `H` secret. -/
inductive Label where
  | L
  | H
open Label

/-- `_⊑_` of `SecretTypes.Lattice`: a computed predicate, as there. -/
def le : Label → Label → Type
  | L, _ => Unit
  | H, L => Empty
  | H, H => Unit

def join : Label → Label → Label
  | L, y => y
  | H, _ => H

def le_trans : ∀ {x y z : Label}, le x y → le y z → le x z
  | L, _, _, _, _ => ()
  | H, H, H, _, _ => ()
  | H, H, L, _, k => k
  | H, L, _, h, _ => nomatch h

def upper₁ : ∀ x y : Label, le x (join x y)
  | L, _ => ()
  | H, _ => ()

def upper₂ : ∀ x y : Label, le y (join x y)
  | L, L => ()
  | L, H => ()
  | H, L => ()
  | H, H => ()

/-- `two-point` of `SecretTypes.Lattice`. -/
def twoPoint : Lattice where
  Carrier := Label
  le := le
  join := join
  bot := L
  le_trans := le_trans
  upper₁ := upper₁
  upper₂ := upper₂

/-- `Var` of `SecretTypes.Lang.Two`. -/
inductive Var where
  | lo
  | hi
deriving DecidableEq
open Var

/-- `two : Vars`. -/
def two : Vars where
  Var := Var
  deq := inferInstance

/-- `label` of `SecretTypes.Typing`. -/
def label : two.Var → twoPoint.Carrier
  | lo => L
  | hi => H

/-- `⟨_,_⟩`, `low` and `_≈_` of `SecretTypes.Lang.Two`. -/
def pair (l h : Nat) : Store two
  | lo => l
  | hi => h

def low (s : Store two) : Nat := s lo

def LowEq (s s' : Store two) : Prop := low s = low s'

/-- `public-observer = principal two-point L`. -/
def publicObserver : Observer twoPoint := principal twoPoint L

theorem lowEq_agree {s s' : Store two} (eq : LowEq s s') :
    Agree twoPoint.toSignature label publicObserver.sees s s' := fun
  | lo, _ => eq
  | hi, v => Empty.elim (show Empty from v)

theorem agree_lowEq {s s' : Store two}
    (f : Agree twoPoint.toSignature label publicObserver.sees s s') : LowEq s s' :=
  f lo ()

/-- N-2 at the two-point lattice: a public expression reads the same in
low-equivalent stores. -/
theorem eval_low_two (e : Expr two) {s s' : Store two}
    (p : lab twoPoint.toSignature label e = L) (eq : LowEq s s') : eval s e = eval s' e :=
  eval_low publicObserver e (p ▸ (() : le L L)) (lowEq_agree eq)

/-- N-3 at the two-point lattice: under a secret counter the public variable
is unchanged, loops included. -/
theorem confine_two {c : Cmd two} (fuel : Nat) {s t : Store two}
    (d : Typed twoPoint.toSignature label H c) (h : exec fuel c s = some t) : low t = low s :=
  confine publicObserver fuel (pc := H) (fun v => Empty.elim (show Empty from v)) d h lo ()

/-- N-1, `tini` of `SecretTypes.Noninterference`: TINI at the two-point
lattice, fuels independent. -/
theorem tini_two {pc : Label} {c : Cmd two} (fuel fuel' : Nat) {s s' t t' : Store two}
    (d : Typed twoPoint.toSignature label pc c) (eq : LowEq s s')
    (h : exec fuel c s = some t) (h' : exec fuel' c s' = some t') : LowEq t t' :=
  agree_lowEq (tini publicObserver fuel fuel' d (lowEq_agree eq) h h')

/-! N-9, `SecretTypes.Noninterference.OutcomeVisibility`. -/

/-- `secret-loop = while (var hi) skip` and its typing at `L`. -/
def secretLoop : Cmd two := .«while» (.var hi) .skip

def secretLoopTyped : Typed twoPoint.toSignature label L secretLoop := .«while» .skip

def s₀ : Store two := pair 0 0
def s₁ : Store two := pair 0 1

theorem lowEquivalent : LowEq s₀ s₁ := rfl

/-- `publicOutcome`: whether a run finished, and if so its public result. -/
def publicOutcome (fuel : Nat) (c : Cmd two) (s : Store two) : Option Nat :=
  match exec fuel c s with
  | none => none
  | some t => some (low t)

theorem secretLoop_never_finishes : ∀ fuel, exec fuel secretLoop s₀ = none
  | 0 => rfl
  | f + 1 => by
    show bind (exec f .skip s₀) (exec f secretLoop) = none
    rw [exec_skip]
    exact secretLoop_never_finishes f

theorem secretLoop_stops (fuel : Nat) : exec (fuel + 1) secretLoop s₁ = some s₁ := rfl

theorem outcome_spins : publicOutcome 3 secretLoop s₀ = none := rfl
theorem outcome_stops : publicOutcome 3 secretLoop s₁ = some 0 := rfl

theorem outcome_different : publicOutcome 3 secretLoop s₀ ≠ publicOutcome 3 secretLoop s₁ :=
  fun h => nomatch h

/-- `TSNI`: the stronger two-run statement, with termination observable. -/
def TSNI : Prop :=
  ∀ {pc : Label} {c : Cmd two} (fuel : Nat) {s s' : Store two},
    Typed twoPoint.toSignature label pc c → LowEq s s' →
    publicOutcome fuel c s = publicOutcome fuel c s'

/-- N-9, `termination-sensitive-fails`: TSNI is false for the current
typing rules. -/
theorem termination_sensitive_fails : TSNI → False :=
  fun h => outcome_different (h 3 secretLoopTyped lowEquivalent)

end SecretTypes.Two
