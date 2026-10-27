{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The language at two variables, lo and hi: the first instance of
-- SecretTypes.Vars, and the fragment the two-point development
-- (SecretTypes.Typing, SecretTypes.Noninterference, SecretTypes.Witness,
-- SecretTypes.Countermodels) is stated in.
module SecretTypes.Lang.Two where

open import SecretTypes.Prelude
open import SecretTypes.Vars

data Var : Set where
  lo hi : Var

infix 4 _≟ᵥ_
-- Decide equality of the two variables.
_≟ᵥ_ : (x y : Var) → Dec (x ≡ y)
lo ≟ᵥ lo = yes refl
lo ≟ᵥ hi = no λ ()
hi ≟ᵥ lo = no λ ()
hi ≟ᵥ hi = yes refl

two : Vars
two = record { Var = Var ; _≟ᵥ_ = _≟ᵥ_ }

open import SecretTypes.Lang two public hiding (Var; _≟ᵥ_)

-- The store with lo at l and hi at h.
⟨_,_⟩ : Nat → Nat → Store
⟨ l , h ⟩ lo = l
⟨ l , h ⟩ hi = h

-- The two variables' values, by name.
low high : Store → Nat
low  s = s lo
high s = s hi

-- Low-equivalence: the public observer sees the same thing.
infix 4 _≈_
_≈_ : Store → Store → Set
s ≈ s' = low s ≡ low s'
