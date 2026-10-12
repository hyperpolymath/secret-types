{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Termination-insensitive noninterference for the two-point lattice.
--
--   tini : pc ⊢ c → s ≈ s' → exec n c s ≡ just t → exec n' c s' ≡ just t' → t ≈ t'
--
-- Two runs of a well-typed command from low-equivalent stores, each of
-- which finishes, end low-equivalent.  Fuel is universally quantified and
-- may differ between the runs; a run that does not finish is simply not a
-- case (that is the "termination-insensitive").  Structure:
--   eval-low   a public expression reads the same in low-equivalent stores
--   confine    a command typed under a secret pc leaves the public variable alone
--   tini       by induction on fuel and the typing derivation
module SecretTypes.Noninterference where

open import SecretTypes.Prelude
open import SecretTypes.Lattice
open import SecretTypes.Lang
open import SecretTypes.Typing

----------------------------------------------------------------------
-- A public expression has equal values in stores that agree on lo.
eval-low : ∀ e {s s'} → lab e ≡ L → s ≈ s' → eval s e ≡ eval s' e
eval-low (lit n)    _ _  = refl
eval-low (var lo)   _ eq = eq
eval-low (var hi)   ()
eval-low (plus a b) p eq = cong₂ _+_ (eval-low a (⊔-L₁ p) eq) (eval-low b (⊔-L₂ p) eq)

----------------------------------------------------------------------
-- Confinement: under a secret program counter the public variable is unchanged.
-- Requires evidence that execution finishes with the supplied fuel.
confine   : ∀ {c} fuel {s t} → H ⊢ c → exec fuel c s ≡ just t → low t ≡ low s
-- Confinement for a finishing conditional with supplied guard value n;
-- both branches must be typed under a secret program counter.
confineIf : ∀ {c₁ c₂} fuel n {s t} → H ⊢ c₁ → H ⊢ c₂ → execIf fuel n c₁ c₂ s ≡ just t → low t ≡ low s
-- Confinement for a finishing loop continuation with remaining fuel and
-- supplied guard value n, when its body is typed under a secret counter.
confineW  : ∀ {e c} fuel n {s t} → H ⊢ c → execWhile fuel n e c s ≡ just t → low t ≡ low s

confine fuel skip                 e = cong low (sym (just-inj e))
confine fuel (assign {x = lo} ())
confine fuel (assign {x = hi} _)  e = cong low (sym (just-inj e))
confine fuel (seq t₁ t₂)          e with bind-just _ _ e
... | s₁ , (e₁ , e₂) = trans (confine fuel t₂ e₂) (confine fuel t₁ e₁)
confine fuel (ifz {e = g} t₁ t₂)  e = confineIf fuel (eval _ g) t₁ t₂ e
confine zero       (while t)      ()
confine (suc fuel) (while {e = g} t) e = confineW fuel (eval _ g) t e

confineIf fuel zero    t₁ t₂ e = confine fuel t₁ e
confineIf fuel (suc _) t₁ t₂ e = confine fuel t₂ e

confineW fuel zero    t e with bind-just _ _ e
... | s₁ , (e₁ , e₂) = trans (confine fuel (while t) e₂) (confine fuel t e₁)
confineW fuel (suc _) t e = cong low (sym (just-inj e))

----------------------------------------------------------------------
-- Finishing runs of a well-typed command preserve low-equivalence.
-- The fuel bounds may differ; runs returning nothing are not covered.
tini   : ∀ {pc c} fuel fuel' {s s' t t'} → pc ⊢ c → s ≈ s'
       → exec fuel c s ≡ just t → exec fuel' c s' ≡ just t' → t ≈ t'
-- Preserve low-equivalence across two finishing conditional evaluations.
-- ℓ is the program-counter label joined with the guard's label; when it
-- is secret, the runs may take different branches.  Fuel bounds may differ.
tiniIf : ∀ {pc e c₁ c₂} fuel fuel' {s s' t t'} ℓ → pc ⊔ lab e ≡ ℓ
       → pc ⊔ lab e ⊢ c₁ → pc ⊔ lab e ⊢ c₂ → s ≈ s'
       → execIf fuel (eval s e) c₁ c₂ s ≡ just t → execIf fuel' (eval s' e) c₁ c₂ s' ≡ just t' → t ≈ t'
-- Preserve low-equivalence across two finishing loop continuations.
-- ℓ is the program-counter label joined with the guard's label; the fuel
-- bounds are those remaining after each loop's decrement and may differ.
tiniW  : ∀ {pc e c} fuel fuel' {s s' t t'} ℓ → pc ⊔ lab e ≡ ℓ
       → pc ⊔ lab e ⊢ c → s ≈ s'
       → execWhile fuel (eval s e) e c s ≡ just t → execWhile fuel' (eval s' e) e c s' ≡ just t' → t ≈ t'

tini fuel fuel' skip eq e e' = trans (cong low (sym (just-inj e))) (trans eq (cong low (just-inj e')))
tini fuel fuel' (assign {pc} {lo} {g} ok) eq e e' =
  trans (cong low (sym (just-inj e)))
  (trans (eval-low g (⊔-L₂ (low-pc ok)) eq)
         (cong low (just-inj e')))
  where
  -- Any label allowed to flow to the public variable must itself be public.
  low-pc : ∀ {x} → x ⊑ L → x ≡ L
  low-pc L⊑L = refl
tini fuel fuel' (assign {x = hi} _) eq e e' =
  trans (cong low (sym (just-inj e))) (trans eq (cong low (just-inj e')))
tini fuel fuel' (seq t₁ t₂) eq e e' with bind-just _ _ e | bind-just _ _ e'
... | s₁ , (e₁ , e₂) | s₁' , (e₁' , e₂') = tini fuel fuel' t₂ (tini fuel fuel' t₁ eq e₁ e₁') e₂ e₂'
tini fuel fuel' (ifz {pc} {g} t₁ t₂) eq e e' = tiniIf {pc} {g} fuel fuel' (pc ⊔ lab g) refl t₁ t₂ eq e e'
tini zero       fuel'       (while t) eq () e'
tini (suc fuel) zero        (while t) eq e  ()
tini (suc fuel) (suc fuel') (while {pc} {g} t) eq e e' = tiniW {pc} {g} fuel fuel' (pc ⊔ lab g) refl t eq e e'

-- Public guard: both runs read the same guard, take the same branch.
tiniIf {pc} {g} {c₁} {c₂} fuel fuel' {s} {s'} {t} {t'} L p t₁ t₂ eq e e' =
  go (eval s g) (eval-low g (⊔-L₂ p) eq) e e'
  where
  -- Equal guard values select the same branch in the two finishing runs.
  go : ∀ n {m} → n ≡ m → execIf fuel n c₁ c₂ s ≡ just t → execIf fuel' m c₁ c₂ s' ≡ just t' → t ≈ t'
  go zero    refl e e' = tini fuel fuel' t₁ eq e e'
  go (suc n) refl e e' = tini fuel fuel' t₂ eq e e'
-- Secret guard: whichever branches ran, neither touched the public variable.
tiniIf {pc} {g} {c₁} {c₂} fuel fuel' {s} {s'} H p t₁ t₂ eq e e' =
  trans (confineIf fuel (eval s g) (subst (_⊢ c₁) p t₁) (subst (_⊢ c₂) p t₂) e)
  (trans eq (sym (confineIf fuel' (eval s' g) (subst (_⊢ c₁) p t₁) (subst (_⊢ c₂) p t₂) e')))

tiniW {pc} {g} {c} fuel fuel' {s} {s'} {t} {t'} L p tc eq e e' =
  go (eval s g) (eval-low g (⊔-L₂ p) eq) e e'
  where
  -- Equal guard values make both finishing runs continue the loop or stop.
  go : ∀ n {m} → n ≡ m → execWhile fuel n g c s ≡ just t → execWhile fuel' m g c s' ≡ just t' → t ≈ t'
  go zero    refl e e' with bind-just _ _ e | bind-just _ _ e'
  ... | s₁ , (e₁ , e₂) | s₁' , (e₁' , e₂') = tini fuel fuel' (while tc) (tini fuel fuel' tc eq e₁ e₁') e₂ e₂'
  go (suc n) refl e e' = trans (cong low (sym (just-inj e))) (trans eq (cong low (just-inj e')))
tiniW {pc} {g} {c} fuel fuel' {s} {s'} H p tc eq e e' =
  trans (confineW fuel (eval s g) (subst (_⊢ c) p tc) e)
  (trans eq (sym (confineW fuel' (eval s' g) (subst (_⊢ c) p tc) e')))
