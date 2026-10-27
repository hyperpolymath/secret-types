{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ThirdVariable where
open import SecretTypes.Prelude
open import SecretTypes.Vars
open import SecretTypes.Lattice

-- Three variables: the rules are not tied to lo and hi.
data V : Set where
  a b c : V

_≟V_ : (x y : V) → Dec (x ≡ y)
a ≟V a = yes refl
a ≟V b = no λ ()
a ≟V c = no λ ()
b ≟V a = no λ ()
b ≟V b = yes refl
b ≟V c = no λ ()
c ≟V a = no λ ()
c ≟V b = no λ ()
c ≟V c = yes refl

three : Vars
three = record { Var = V ; _≟ᵥ_ = _≟V_ }

label : V → Label
label a = L
label b = H
label c = L

open import SecretTypes.Lang three
open import SecretTypes.Typing.Generic three _⊑_ _⊔_ L label

-- Must fail: copying the secret b into the public c needs H ⊑ L.
invalid : L ⊢ (c ≔ var b)
invalid = assign L⊑L
