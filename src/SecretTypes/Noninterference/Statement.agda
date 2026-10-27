{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The statement of termination-insensitive noninterference, for an observer
-- given as the set of labels it sees.  Stated over the operations only, so
-- that SecretTypes.Countermodels can refute it for structures that break a
-- law; SecretTypes.Noninterference.Generic proves it for every Lattice and
-- every down-closed observer.
open import SecretTypes.Prelude
open import SecretTypes.Vars

module SecretTypes.Noninterference.Statement
  (𝓥 : Vars)
  {Carrier : Set}
  (_⊑_ : Carrier → Carrier → Set)
  (_⊔_ : Carrier → Carrier → Carrier)
  (⊥ₗ : Carrier)
  (label : Vars.Var 𝓥 → Carrier)
  where

open import SecretTypes.Lang 𝓥
open import SecretTypes.Typing.Generic 𝓥 _⊑_ _⊔_ ⊥ₗ label public

-- Two stores agree for an observer when they agree on every variable whose
-- label it sees.
infix 4 _≈[_]_
_≈[_]_ : Store → (Carrier → Set) → Store → Set
s ≈[ sees ] s' = ∀ x → sees (label x) → read s x ≡ read s' x

-- Two finishing runs of a well-typed command from stores that agree for the
-- observer end in stores that agree for it.  Fuel may differ between runs.
TINI : (Carrier → Set) → Set
TINI sees = ∀ {pc c} fuel fuel' {s s' t t'} → pc ⊢ c → s ≈[ sees ] s'
          → exec fuel c s ≡ just t → exec fuel' c s' ≡ just t' → t ≈[ sees ] t'
