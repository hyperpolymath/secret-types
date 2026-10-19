{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Termination-insensitive noninterference over any Lattice record, for
-- every down-closed observer V:
--
--   tini V : TINI (sees V)
--
-- Instantiate with a lattice and a labelling of the variables:
--
--   open import SecretTypes.Noninterference.Generic 𝓛 label
--
-- which also brings the typing rules and the statement into scope.  A
-- principal observer (SecretTypes.Lattice.Record.principal) is the usual
-- "level o" observer.  Structure, as for the two-point proof:
--   eval-low   an expression whose label V sees reads the same in agreeing stores
--   confine    a command typed under a program counter V cannot see changes
--              nothing V sees
--   tini       by induction on fuel and the typing derivation
-- Laws used: ⊔-upper₁, ⊔-upper₂ and V's down-closure; nothing else.  Where
-- the two runs may branch differently the proof case-splits on whether V
-- sees the branch label.  That split needs no decidability: the goal is an
-- equation between naturals, so it is stable, and excluded middle holds
-- under double negation.
open import SecretTypes.Prelude
open import SecretTypes.Lattice.Record
open import SecretTypes.Lang hiding (_≈_)

module SecretTypes.Noninterference.Generic (𝓛 : Lattice) (label : Var → Lattice.Carrier 𝓛) where

open Lattice 𝓛
open import SecretTypes.Noninterference.Statement _⊑_ _⊔_ ⊥ₗ label public

module _ (V : Observer 𝓛) where
  open Observer V

  private
    infix 4 _≈_
    _≈_ : Store → Store → Set
    s ≈ s' = s ≈[ sees ] s'

    ≈-sym : ∀ {s s'} → s ≈ s' → s' ≈ s
    ≈-sym p x v = sym (p x v)

    ≈-trans : ∀ {s s' s''} → s ≈ s' → s' ≈ s'' → s ≈ s''
    ≈-trans p q x v = trans (p x v) (q x v)

    -- A program counter V cannot see stays unseen in any branch it guards.
    unseen-⊔ : ∀ {pc} y → ¬ sees pc → ¬ sees (pc ⊔ y)
    unseen-⊔ y np v = np (sees-↓ (⊔-upper₁ _ y) v)

    -- Agreement is decided pointwise by naturals, so double negation can be
    -- removed from it.
    ≈-stable : ∀ {s s'} → ¬ ¬ (s ≈ s') → s ≈ s'
    ≈-stable {s} {s'} h x v = dec-stable (read s x ≟ read s' x) λ ne → h λ p → ne (p x v)

  ----------------------------------------------------------------------
  -- An expression whose label V sees has equal values in agreeing stores.
  eval-low : ∀ e {s s'} → sees (lab e) → s ≈ s' → eval s e ≡ eval s' e
  eval-low (lit n)    _ _  = refl
  eval-low (var x)    v eq = eq x v
  eval-low (plus a b) v eq =
    cong₂ _+_ (eval-low a (sees-↓ (⊔-upper₁ _ _) v) eq) (eval-low b (sees-↓ (⊔-upper₂ _ _) v) eq)

  ----------------------------------------------------------------------
  -- Confinement: under a program counter V cannot see, nothing V sees
  -- changes.  Requires evidence that execution finishes with the fuel.
  private
    -- An assignment allowed under an unseen counter targets an unseen
    -- variable, so every seen variable keeps its value.
    confine-assign : ∀ {pc} x e n s → ¬ sees pc → (pc ⊔ lab e) ⊑ label x → update x n s ≈ s
    confine-assign lo e n s np ok lo v = ⊥-elim (unseen-⊔ (lab e) np (sees-↓ ok v))
    confine-assign lo e n s np ok hi v = refl
    confine-assign hi e n s np ok lo v = refl
    confine-assign hi e n s np ok hi v = ⊥-elim (unseen-⊔ (lab e) np (sees-↓ ok v))

  confine   : ∀ {pc c} fuel {s t} → ¬ sees pc → pc ⊢ c → exec fuel c s ≡ just t → t ≈ s
  -- Confinement for a finishing conditional with supplied guard value n;
  -- both branches are typed under the same unseen counter ℓ.
  confineIf : ∀ {ℓ c₁ c₂} fuel n {s t} → ¬ sees ℓ → ℓ ⊢ c₁ → ℓ ⊢ c₂
            → execIf fuel n c₁ c₂ s ≡ just t → t ≈ s
  -- Confinement for a finishing loop continuation with remaining fuel and
  -- supplied guard value n, when its body is typed under an unseen ℓ.
  confineW  : ∀ {ℓ e c} fuel n {s t} → ¬ sees ℓ → ℓ ⊢ c
            → execWhile fuel n e c s ≡ just t → t ≈ s
  -- Confinement for re-entering that loop.  The loop is not re-typed: ℓ is
  -- the body's counter, which need not type `while e c` itself.
  confineL  : ∀ {ℓ e c} fuel {s t} → ¬ sees ℓ → ℓ ⊢ c
            → exec fuel (while e c) s ≡ just t → t ≈ s

  confine fuel np skip refl _ _ = refl
  confine fuel {s} np (assign {x = x} {e = e} ok) refl = confine-assign x e (eval s e) s np ok
  confine fuel np (seq t₁ t₂) e with bind-just _ _ e
  ... | s₁ , (e₁ , e₂) = ≈-trans (confine fuel np t₂ e₂) (confine fuel np t₁ e₁)
  confine fuel np (ifz {e = g} t₁ t₂) e = confineIf fuel (eval _ g) (unseen-⊔ (lab g) np) t₁ t₂ e
  confine zero       np (while t) ()
  confine (suc fuel) np (while {e = g} t) e = confineW fuel (eval _ g) (unseen-⊔ (lab g) np) t e

  confineIf fuel zero    np t₁ t₂ e = confine fuel np t₁ e
  confineIf fuel (suc _) np t₁ t₂ e = confine fuel np t₂ e

  confineW fuel zero np t e with bind-just _ _ e
  ... | s₁ , (e₁ , e₂) = ≈-trans (confineL fuel np t e₂) (confine fuel np t e₁)
  confineW fuel (suc _) np t refl _ _ = refl

  confineL           zero       np t ()
  confineL {e = g} (suc fuel) {s} np t e = confineW fuel (eval s g) np t e

  ----------------------------------------------------------------------
  -- Finishing runs of a well-typed command preserve agreement for V.
  -- The fuel bounds may differ; runs returning nothing are not covered.
  private
    -- An allowed assignment to a seen variable assigns an expression whose
    -- label V sees, so both runs assign the same value.
    tini-assign : ∀ {pc} x e {s s'} → (pc ⊔ lab e) ⊑ label x → s ≈ s'
                → update x (eval s e) s ≈ update x (eval s' e) s'
    tini-assign lo e ok eq lo v = eval-low e (sees-↓ (⊔-upper₂ _ _) (sees-↓ ok v)) eq
    tini-assign lo e ok eq hi v = eq hi v
    tini-assign hi e ok eq lo v = eq lo v
    tini-assign hi e ok eq hi v = eval-low e (sees-↓ (⊔-upper₂ _ _) (sees-↓ ok v)) eq

  tini   : TINI sees
  -- Preserve agreement across two finishing conditional evaluations, given
  -- whether V sees the branch label; when it does not, the runs may take
  -- different branches.  Fuel bounds may differ.
  tiniIf : ∀ {pc e c₁ c₂} fuel fuel' {s s' t t'} → Dec (sees (pc ⊔ lab e))
         → (pc ⊔ lab e) ⊢ c₁ → (pc ⊔ lab e) ⊢ c₂ → s ≈ s'
         → execIf fuel (eval s e) c₁ c₂ s ≡ just t → execIf fuel' (eval s' e) c₁ c₂ s' ≡ just t' → t ≈ t'
  -- Preserve agreement across two finishing loop continuations, given
  -- whether V sees the loop label; the fuel bounds are those remaining
  -- after each loop's decrement and may differ.
  tiniW  : ∀ {pc e c} fuel fuel' {s s' t t'} → Dec (sees (pc ⊔ lab e))
         → (pc ⊔ lab e) ⊢ c → s ≈ s'
         → execWhile fuel (eval s e) e c s ≡ just t → execWhile fuel' (eval s' e) e c s' ≡ just t' → t ≈ t'

  tini fuel fuel' skip eq refl refl = eq
  tini fuel fuel' (assign {x = x} {e = g} ok) eq refl refl = tini-assign x g ok eq
  tini fuel fuel' (seq t₁ t₂) eq e e' with bind-just _ _ e | bind-just _ _ e'
  ... | s₁ , (e₁ , e₂) | s₁' , (e₁' , e₂') = tini fuel fuel' t₂ (tini fuel fuel' t₁ eq e₁ e₁') e₂ e₂'
  tini fuel fuel' (ifz {pc} {g} t₁ t₂) eq e e' =
    ≈-stable λ k → ¬¬-dec (sees (pc ⊔ lab g)) λ d → k (tiniIf {pc} {g} fuel fuel' d t₁ t₂ eq e e')
  tini zero       fuel'       (while t) eq () e'
  tini (suc fuel) zero        (while t) eq e  ()
  tini (suc fuel) (suc fuel') (while {pc} {g} t) eq e e' =
    ≈-stable λ k → ¬¬-dec (sees (pc ⊔ lab g)) λ d → k (tiniW {pc} {g} fuel fuel' d t eq e e')

  -- Seen guard: both runs read the same guard, take the same branch.
  tiniIf {pc} {g} {c₁} {c₂} fuel fuel' {s} {s'} {t} {t'} (yes v) t₁ t₂ eq e e' =
    go (eval s g) (eval-low g (sees-↓ (⊔-upper₂ _ _) v) eq) e e'
    where
    -- Equal guard values select the same branch in the two finishing runs.
    go : ∀ n {m} → n ≡ m → execIf fuel n c₁ c₂ s ≡ just t → execIf fuel' m c₁ c₂ s' ≡ just t' → t ≈ t'
    go zero    refl e e' = tini fuel fuel' t₁ eq e e'
    go (suc n) refl e e' = tini fuel fuel' t₂ eq e e'
  -- Unseen guard: whichever branches ran, neither touched what V sees.
  tiniIf {pc} {g} fuel fuel' {s} {s'} (no nv) t₁ t₂ eq e e' =
    ≈-trans (confineIf fuel (eval s g) nv t₁ t₂ e) (≈-trans eq (≈-sym (confineIf fuel' (eval s' g) nv t₁ t₂ e')))

  tiniW {pc} {g} {c} fuel fuel' {s} {s'} {t} {t'} (yes v) tc eq e e' =
    go (eval s g) (eval-low g (sees-↓ (⊔-upper₂ _ _) v) eq) e e'
    where
    -- Equal guard values make both finishing runs continue the loop or stop.
    go : ∀ n {m} → n ≡ m → execWhile fuel n g c s ≡ just t → execWhile fuel' m g c s' ≡ just t' → t ≈ t'
    go zero    refl e e' with bind-just _ _ e | bind-just _ _ e'
    ... | s₁ , (e₁ , e₂) | s₁' , (e₁' , e₂') = tini fuel fuel' (while tc) (tini fuel fuel' tc eq e₁ e₁') e₂ e₂'
    go (suc n) refl refl refl = eq
  tiniW {pc} {g} fuel fuel' {s} {s'} (no nv) tc eq e e' =
    ≈-trans (confineW fuel (eval s g) nv tc e) (≈-trans eq (≈-sym (confineW fuel' (eval s' g) nv tc e')))
