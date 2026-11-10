/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

Lean leg (PROOF-POLICY §2, route `re-proved`) of secret-types N-2, N-3 and N-7:
termination-insensitive noninterference over any lattice record and any
down-closed observer.  The statements mirror, line for line:
  src/SecretTypes/Vars.agda, Lang.agda, Lattice/Record.agda,
  Typing/Generic.agda, Noninterference/Statement.agda, Noninterference/Generic.agda.
Lean core only: no Mathlib, no Std, no classical axioms
(see the `#print axioms` lines at the end of this file).

Universe discipline: Agda's `Set` is Lean's `Type`.  The order, an
observer's `sees` and the typing derivations are `Type`-valued here, as in
Agda, so a proof may not use proof irrelevance that the Agda statement does
not grant.  Equality of naturals is `Prop` in Lean and a set in Agda;
naturals have decidable equality, so the two readings coincide.
-/
namespace SecretTypes

/-- `SecretTypes.Vars`: variables with decidable equality. -/
structure Vars where
  Var : Type
  deq : DecidableEq Var

/-- What `SecretTypes.Noninterference.Statement` and `Typing.Generic` are
parameterised by: a carrier, an order, a join and the label of a literal, with
no laws.  The countermodels (N-8) instantiate the statement at signatures
that lack a law, so the statement cannot ask for one. -/
structure Signature where
  Carrier : Type
  le : Carrier → Carrier → Type
  join : Carrier → Carrier → Carrier
  bot : Carrier

/-- `SecretTypes.Lattice.Record.Lattice`: a signature with the three laws
generic TINI uses (the certified census, N-6). -/
structure Lattice extends Signature where
  le_trans : ∀ {x y z : Carrier}, le x y → le y z → le x z
  upper₁ : ∀ x y : Carrier, le x (join x y)
  upper₂ : ∀ x y : Carrier, le y (join x y)

/-- `SecretTypes.Lattice.Record.Observer`: a down-closed set of labels. -/
structure Observer (L : Lattice) where
  sees : L.Carrier → Type
  down : ∀ {x y : L.Carrier}, L.le x y → sees y → sees x

/-- `principal`: the observer at level `o` sees exactly the labels below it. -/
def principal (L : Lattice) (o : L.Carrier) : Observer L where
  sees x := L.le x o
  down h v := L.le_trans h v

section Lang
variable (V : Vars)

/-- `Store = Var → Nat`. -/
abbrev Store := V.Var → Nat

inductive Expr where
  | lit : Nat → Expr
  | var : V.Var → Expr
  | plus : Expr → Expr → Expr

inductive Cmd where
  | skip : Cmd
  | assign : V.Var → Expr V → Cmd
  | seq : Cmd → Cmd → Cmd
  | ifz : Expr V → Cmd → Cmd → Cmd
  | «while» : Expr V → Cmd → Cmd

variable {V}

def eval (s : Store V) : Expr V → Nat
  | .lit n => n
  | .var x => s x
  | .plus a b => eval s a + eval s b

/-- `update x n s y = select (x ≟ᵥ y) n (s y)`. -/
def update (x : V.Var) (n : Nat) (s : Store V) : Store V := fun y =>
  match V.deq x y with
  | .isTrue _ => n
  | .isFalse _ => s y

/-- `bind` of `SecretTypes.Prelude`. -/
def bind {A : Type} : Option A → (A → Option A) → Option A
  | none, _ => none
  | some a, f => f a

/-- One step of fuel: run a command, using `prev` (the run at one less fuel)
to re-enter a loop.  `none` is fuel zero, where a loop does not finish.
Structural in the command, so `exec` below is structural in both fuel and
command and its equations hold by `rfl` (no well-founded recursion, hence no
`propext` or `funext` in the proofs). -/
def run (prev : Option (Cmd V → Store V → Option (Store V))) :
    Cmd V → Store V → Option (Store V)
  | .skip, s => some s
  | .assign x e, s => some (update x (eval s e) s)
  | .seq c₁ c₂, s => bind (run prev c₁ s) (run prev c₂)
  | .ifz e c₁ c₂, s =>
      match eval s e with
      | 0 => run prev c₁ s
      | _ + 1 => run prev c₂ s
  | .«while» e c, s =>
      match prev with
      | none => none
      | some p =>
        match eval s e with
        | 0 => bind (p c s) (p (.«while» e c))
        | _ + 1 => some s

/-- `exec` of `SecretTypes.Lang`: `exec fuel c s` is `some t` if `c` finishes
within `fuel`, else `none`.  Equal to Agda's `exec`, `execIf` and
`execWhile` clause by clause: sequence and `ifz` keep the fuel, a loop at
`fuel + 1` runs its body and re-enters at `fuel`, a loop at `0` is `none`. -/
def exec : Nat → Cmd V → Store V → Option (Store V)
  | 0 => run none
  | f + 1 => run (some (exec f))

end Lang

section Typing
variable {V : Vars} (L : Signature) (label : V.Var → L.Carrier)

/-- `lab` of `SecretTypes.Typing.Generic`. -/
def lab : Expr V → L.Carrier
  | .lit _ => L.bot
  | .var x => label x
  | .plus a b => L.join (lab a) (lab b)

/-- `_⊢_` of `SecretTypes.Typing.Generic`: Volpano–Smith typing with a
program-counter label. -/
inductive Typed : L.Carrier → Cmd V → Type where
  | skip {pc} : Typed pc .skip
  | assign {pc x e} : L.le (L.join pc (lab L label e)) (label x) → Typed pc (.assign x e)
  | seq {pc c₁ c₂} : Typed pc c₁ → Typed pc c₂ → Typed pc (.seq c₁ c₂)
  | ifz {pc e c₁ c₂} : Typed (L.join pc (lab L label e)) c₁ →
      Typed (L.join pc (lab L label e)) c₂ → Typed pc (.ifz e c₁ c₂)
  | «while» {pc e c} : Typed (L.join pc (lab L label e)) c → Typed pc (.«while» e c)

/-- `_≈[_]_` of `SecretTypes.Noninterference.Statement`. -/
def Agree (sees : L.Carrier → Type) (s s' : Store V) : Prop :=
  ∀ x, sees (label x) → s x = s' x

/-- `TINI` of `SecretTypes.Noninterference.Statement`. -/
def TINI (sees : L.Carrier → Type) : Prop :=
  ∀ {pc : L.Carrier} {c : Cmd V} (fuel fuel' : Nat) {s s' t t' : Store V},
    Typed L label pc c → Agree L label sees s s' →
    exec fuel c s = some t → exec fuel' c s' = some t' → Agree L label sees t t'

end Typing

section Proof
variable {V : Vars} {L : Lattice} {label : V.Var → L.Carrier} (O : Observer L)

/-! Unfolding equations for `exec`, one per command form. -/

/-- The branch an `ifz` takes on guard value `n`. -/
def branch (n : Nat) (c₁ c₂ : Cmd V) : Cmd V :=
  match n with
  | 0 => c₁
  | _ + 1 => c₂

theorem exec_skip (f : Nat) (s : Store V) : exec f .skip s = some s := by
  cases f <;> rfl

theorem exec_assign (f : Nat) (x : V.Var) (e : Expr V) (s : Store V) :
    exec f (.assign x e) s = some (update x (eval s e) s) := by
  cases f <;> rfl

theorem exec_seq (f : Nat) (c₁ c₂ : Cmd V) (s : Store V) :
    exec f (.seq c₁ c₂) s = bind (exec f c₁ s) (exec f c₂) := by
  cases f <;> rfl

theorem exec_ifz (f : Nat) (e : Expr V) (c₁ c₂ : Cmd V) (s : Store V) :
    exec f (.ifz e c₁ c₂) s = exec f (branch (eval s e) c₁ c₂) s := by
  cases f <;> (show run _ _ _ = run _ _ _; simp only [run]; cases eval s e <;> rfl)

theorem exec_while_zero (e : Expr V) (c : Cmd V) (s : Store V) :
    exec 0 (.«while» e c) s = none := rfl

theorem exec_while_succ (f : Nat) (e : Expr V) (c : Cmd V) (s : Store V) :
    exec (f + 1) (.«while» e c) s =
      (match eval s e with
       | 0 => bind (exec f c s) (exec f (.«while» e c))
       | _ + 1 => some s) := rfl

theorem bind_some {A : Type} {m : Option A} {f : A → Option A} {t : A} :
    bind m f = some t → ∃ a, m = some a ∧ f a = some t := by
  cases m with
  | none => intro h; cases h
  | some a => intro h; exact ⟨a, rfl, h⟩

/-- A branch typed under a counter is typed under it, whichever is taken. -/
def branch_typed {pc : L.Carrier} (n : Nat) {c₁ c₂ : Cmd V}
    (d₁ : Typed L.toSignature label pc c₁) (d₂ : Typed L.toSignature label pc c₂) :
    Typed L.toSignature label pc (branch n c₁ c₂) :=
  match n with
  | 0 => d₁
  | _ + 1 => d₂

/-- `unseen-⊔`. -/
theorem unseen_join {pc : L.Carrier} (y : L.Carrier) (np : O.sees pc → False) :
    O.sees (L.join pc y) → False :=
  fun v => np (O.down (L.upper₁ pc y) v)

/-- N-2, `eval-low`: an expression whose label the observer sees reads the
same in agreeing stores. -/
theorem eval_low : ∀ (e : Expr V) {s s' : Store V}, O.sees (lab L.toSignature label e) →
    Agree L.toSignature label O.sees s s' → eval s e = eval s' e
  | .lit _, _, _, _, _ => rfl
  | .var x, _, _, v, eq => eq x v
  | .plus a b, _, _, v, eq => by
      show eval _ a + eval _ b = eval _ a + eval _ b
      rw [eval_low a (O.down (L.upper₁ _ _) v) eq, eval_low b (O.down (L.upper₂ _ _) v) eq]

theorem agree_refl {s : Store V} : Agree L.toSignature label O.sees s s := fun _ _ => rfl

theorem agree_symm {s s' : Store V} (h : Agree L.toSignature label O.sees s s') :
    Agree L.toSignature label O.sees s' s := fun x v => (h x v).symm

theorem agree_trans {s s' s'' : Store V} (h : Agree L.toSignature label O.sees s s')
    (k : Agree L.toSignature label O.sees s' s'') : Agree L.toSignature label O.sees s s'' :=
  fun x v => (h x v).trans (k x v)

/-- `confine-assign`: an assignment allowed under an unseen counter leaves
every seen variable alone. -/
theorem confine_assign {pc : L.Carrier} (x : V.Var) (e : Expr V) (n : Nat) (s : Store V)
    (np : O.sees pc → False) (ok : L.le (L.join pc (lab L.toSignature label e)) (label x)) :
    Agree L.toSignature label O.sees (update x n s) s := by
  intro y v
  show (match V.deq x y with | .isTrue _ => n | .isFalse _ => s y) = s y
  cases V.deq x y with
  | isTrue hxy => subst hxy; exact (unseen_join O (lab L.toSignature label e) np (O.down ok v)).elim
  | isFalse _ => rfl

/-- N-3, `confine`: under a program counter the observer cannot see, a
finishing run changes nothing the observer sees. -/
theorem confine : ∀ (fuel : Nat) {pc : L.Carrier} {c : Cmd V} {s t : Store V},
    (O.sees pc → False) → Typed L.toSignature label pc c → exec fuel c s = some t →
    Agree L.toSignature label O.sees t s := by
  intro fuel
  induction fuel with
  | zero =>
    intro pc c s t np d
    induction d generalizing s t with
    | skip => intro h; rw [exec_skip] at h; cases h; exact agree_refl O
    | @assign pc x e ok =>
      intro h; rw [exec_assign] at h; cases h; exact confine_assign O x e _ s np ok
    | seq d₁ d₂ ih₁ ih₂ =>
      intro h; rw [exec_seq] at h
      obtain ⟨s₁, h₁, h₂⟩ := bind_some h
      exact agree_trans O (ih₂ np h₂) (ih₁ np h₁)
    | @ifz pc e c₁ c₂ d₁ d₂ ih₁ ih₂ =>
      intro h; rw [exec_ifz] at h
      have np' := unseen_join O (lab L.toSignature label e) np
      cases hv : eval s e with
      | zero => rw [hv] at h; exact ih₁ np' h
      | succ _ => rw [hv] at h; exact ih₂ np' h
    | «while» d ih => intro h; rw [exec_while_zero] at h; cases h
  | succ f ihf =>
    intro pc c s t np d
    induction d generalizing s t with
    | skip => intro h; rw [exec_skip] at h; cases h; exact agree_refl O
    | @assign pc x e ok =>
      intro h; rw [exec_assign] at h; cases h; exact confine_assign O x e _ s np ok
    | seq d₁ d₂ ih₁ ih₂ =>
      intro h; rw [exec_seq] at h
      obtain ⟨s₁, h₁, h₂⟩ := bind_some h
      exact agree_trans O (ih₂ np h₂) (ih₁ np h₁)
    | @ifz pc e c₁ c₂ d₁ d₂ ih₁ ih₂ =>
      intro h; rw [exec_ifz] at h
      have np' := unseen_join O (lab L.toSignature label e) np
      cases hv : eval s e with
      | zero => rw [hv] at h; exact ih₁ np' h
      | succ _ => rw [hv] at h; exact ih₂ np' h
    | @«while» pc e c d ih =>
      intro h; rw [exec_while_succ] at h
      have np' := unseen_join O (lab L.toSignature label e) np
      cases hv : eval s e with
      | zero =>
        rw [hv] at h
        obtain ⟨s₁, h₁, h₂⟩ := bind_some h
        exact agree_trans O (ihf np (Typed.«while» d) h₂) (ihf np' d h₁)
      | succ _ => rw [hv] at h; cases h; exact agree_refl O

/-- `confineL`: re-entering a loop whose body is typed under an unseen
counter changes nothing the observer sees.  The loop is not re-typed: `ℓ` is
the body's counter, which need not type the loop itself. -/
theorem confine_loop : ∀ (fuel : Nat) {ℓ : L.Carrier} {e : Expr V} {c : Cmd V}
    {s t : Store V}, (O.sees ℓ → False) → Typed L.toSignature label ℓ c →
    exec fuel (.«while» e c) s = some t → Agree L.toSignature label O.sees t s := by
  intro fuel
  induction fuel with
  | zero => intro ℓ e c s t _ _ h; rw [exec_while_zero] at h; cases h
  | succ f ihf =>
    intro ℓ e c s t np d h
    rw [exec_while_succ] at h
    cases hv : eval s e with
    | zero =>
      rw [hv] at h
      obtain ⟨s₁, h₁, h₂⟩ := bind_some h
      exact agree_trans O (ihf np d h₂) (confine O f np d h₁)
    | succ _ => rw [hv] at h; cases h; exact agree_refl O

/-- Agreement is a family of equations between naturals, hence stable under
double negation: what lets the proof split on whether the observer sees a
branch label without deciding it (as the Agda proof does). -/
theorem agree_stable {s s' : Store V}
    (h : (Agree L.toSignature label O.sees s s' → False) → False) : Agree L.toSignature label O.sees s s' :=
  fun x v => Decidable.byContradiction fun ne => h fun a => ne (a x v)

/-- `¬¬-dec`: excluded middle under double negation, for any type. -/
theorem nn_em (P : Type) (k : PSum P (P → False) → False) : False :=
  k (.inr fun p => k (.inl p))

/-- Either the observer sees label `j` or it does not, under double
negation: the shape the `ifz` and `while` cases use. -/
theorem by_cases_sees {s s' : Store V} (j : L.Carrier)
    (yes : O.sees j → Agree L.toSignature label O.sees s s')
    (no : (O.sees j → False) → Agree L.toSignature label O.sees s s') :
    Agree L.toSignature label O.sees s s' :=
  agree_stable O fun bad => nn_em (O.sees j) fun
    | .inl v => bad (yes v)
    | .inr nv => bad (no nv)

/-- N-7, `tini`: termination-insensitive noninterference for every
down-closed observer of every lattice record. -/
theorem tini : TINI L.toSignature label O.sees := by
  intro pc c fuel
  induction fuel generalizing pc c with
  | zero =>
    intro fuel' s s' t t' d
    induction d generalizing s s' t t' fuel' with
    | skip =>
      intro eq h h'; rw [exec_skip] at h h'; cases h; cases h'; exact eq
    | @assign pc x e ok =>
      intro eq h h'; rw [exec_assign] at h h'; cases h; cases h'
      intro y v
      show (match V.deq x y with | .isTrue _ => eval s e | .isFalse _ => s y) =
           (match V.deq x y with | .isTrue _ => eval s' e | .isFalse _ => s' y)
      cases V.deq x y with
      | isTrue hxy => subst hxy; exact eval_low O e (O.down (L.upper₂ _ _) (O.down ok v)) eq
      | isFalse _ => exact eq y v
    | seq d₁ d₂ ih₁ ih₂ =>
      intro eq h h'; rw [exec_seq] at h h'
      obtain ⟨s₁, h₁, h₂⟩ := bind_some h
      obtain ⟨s₁', h₁', h₂'⟩ := bind_some h'
      exact ih₂ fuel' (ih₁ fuel' eq h₁ h₁') h₂ h₂'
    | @ifz pc e c₁ c₂ d₁ d₂ ih₁ ih₂ =>
      intro eq h h'; rw [exec_ifz] at h h'
      refine by_cases_sees O (L.join pc (lab L.toSignature label e)) (fun v => ?_) (fun nv => ?_)
      · have ge := eval_low O e (O.down (L.upper₂ _ _) v) eq
        rw [← ge] at h'
        cases hv : eval s e with
        | zero => rw [hv] at h h'; exact ih₁ fuel' eq h h'
        | succ _ => rw [hv] at h h'; exact ih₂ fuel' eq h h'
      · exact agree_trans O
          (confine O _ nv (branch_typed _ d₁ d₂) h)
          (agree_trans O eq (agree_symm O (confine O _ nv (branch_typed _ d₁ d₂) h')))
    | «while» d ih => intro eq h; rw [exec_while_zero] at h; cases h
  | succ f ihf =>
    intro fuel' s s' t t' d
    induction d generalizing s s' t t' fuel' with
    | skip =>
      intro eq h h'; rw [exec_skip] at h h'; cases h; cases h'; exact eq
    | @assign pc x e ok =>
      intro eq h h'; rw [exec_assign] at h h'; cases h; cases h'
      intro y v
      show (match V.deq x y with | .isTrue _ => eval s e | .isFalse _ => s y) =
           (match V.deq x y with | .isTrue _ => eval s' e | .isFalse _ => s' y)
      cases V.deq x y with
      | isTrue hxy => subst hxy; exact eval_low O e (O.down (L.upper₂ _ _) (O.down ok v)) eq
      | isFalse _ => exact eq y v
    | seq d₁ d₂ ih₁ ih₂ =>
      intro eq h h'; rw [exec_seq] at h h'
      obtain ⟨s₁, h₁, h₂⟩ := bind_some h
      obtain ⟨s₁', h₁', h₂'⟩ := bind_some h'
      exact ih₂ fuel' (ih₁ fuel' eq h₁ h₁') h₂ h₂'
    | @ifz pc e c₁ c₂ d₁ d₂ ih₁ ih₂ =>
      intro eq h h'; rw [exec_ifz] at h h'
      refine by_cases_sees O (L.join pc (lab L.toSignature label e)) (fun v => ?_) (fun nv => ?_)
      · have ge := eval_low O e (O.down (L.upper₂ _ _) v) eq
        rw [← ge] at h'
        cases hv : eval s e with
        | zero => rw [hv] at h h'; exact ih₁ fuel' eq h h'
        | succ _ => rw [hv] at h h'; exact ih₂ fuel' eq h h'
      · exact agree_trans O
          (confine O _ nv (branch_typed _ d₁ d₂) h)
          (agree_trans O eq (agree_symm O (confine O _ nv (branch_typed _ d₁ d₂) h')))
    | @«while» pc e c d ih =>
      intro eq h h'
      cases fuel' with
      | zero => rw [exec_while_zero] at h'; cases h'
      | succ f' =>
        rw [exec_while_succ] at h h'
        refine by_cases_sees O (L.join pc (lab L.toSignature label e)) (fun v => ?_) (fun nv => ?_)
        · have ge := eval_low O e (O.down (L.upper₂ _ _) v) eq
          rw [← ge] at h'
          cases hv : eval s e with
          | zero =>
            rw [hv] at h h'
            obtain ⟨s₁, h₁, h₂⟩ := bind_some h
            obtain ⟨s₁', h₁', h₂'⟩ := bind_some h'
            exact ihf f' (Typed.«while» d) (ihf f' d eq h₁ h₁') h₂ h₂'
          | succ _ => rw [hv] at h h'; cases h; cases h'; exact eq
        · rw [← exec_while_succ] at h h'
          exact agree_trans O (confine_loop O _ nv d h)
            (agree_trans O eq (agree_symm O (confine_loop O _ nv d h')))

end Proof
end SecretTypes
