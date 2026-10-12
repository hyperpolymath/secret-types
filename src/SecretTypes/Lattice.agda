{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- The two-point lattice Public ⊑ Secret.  A label is a flow constraint, not
-- an epistemic standpoint (README, "A label is not an epistemic standpoint").
module SecretTypes.Lattice where

open import SecretTypes.Prelude

data Label : Set where
  L H : Label        -- L = Public, H = Secret

infix 4 _⊑_
data _⊑_ : Label → Label → Set where
  L⊑L : L ⊑ L
  L⊑H : L ⊑ H
  H⊑H : H ⊑ H

infixl 6 _⊔_
_⊔_ : Label → Label → Label
L ⊔ y = y
H ⊔ y = H

⊔-L₁ : ∀ {x y} → x ⊔ y ≡ L → x ≡ L
⊔-L₁ {L} _ = refl
⊔-L₁ {H} ()

⊔-L₂ : ∀ {x y} → x ⊔ y ≡ L → y ≡ L
⊔-L₂ {L} e = e
⊔-L₂ {H} ()
