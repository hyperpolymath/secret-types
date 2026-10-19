{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- The two-point lattice Public ⊑ Secret, the first instance of the Lattice
-- record (SecretTypes.Lattice.Record).  A label is a flow constraint, not
-- an epistemic standpoint (README, "A label is not an epistemic standpoint").
module SecretTypes.Lattice where

open import SecretTypes.Prelude
open import SecretTypes.Lattice.Record using (Lattice)

data Label : Set where
  L H : Label        -- L = Public, H = Secret

infix 4 _⊑_
data _⊑_ : Label → Label → Set where
  L⊑L : L ⊑ L
  L⊑H : L ⊑ H
  H⊑H : H ⊑ H

infixl 6 _⊔_
-- Combine flow labels: the result is secret if either input is secret.
_⊔_ : Label → Label → Label
L ⊔ y = y
H ⊔ y = H

-- Two-point facts about public joins.  The generic proof
-- (SecretTypes.Noninterference.Generic) uses the upper-bound laws below
-- instead; these stay as the two-point reading of them.

-- A public join guarantees that its left input is public.
⊔-L₁ : ∀ {x y} → x ⊔ y ≡ L → x ≡ L
⊔-L₁ {L} _ = refl
⊔-L₁ {H} ()

-- A public join guarantees that its right input is public.
⊔-L₂ : ∀ {x y} → x ⊔ y ≡ L → y ≡ L
⊔-L₂ {L} e = e
⊔-L₂ {H} ()

----------------------------------------------------------------------
-- The census laws (SecretTypes.Lattice.Record) at the two-point lattice.

-- Flows compose.
⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans L⊑L q   = q
⊑-trans L⊑H H⊑H = L⊑H
⊑-trans H⊑H H⊑H = H⊑H

-- A join bounds its left input.
⊔-upper₁ : ∀ x y → x ⊑ x ⊔ y
⊔-upper₁ L L = L⊑L
⊔-upper₁ L H = L⊑H
⊔-upper₁ H _ = H⊑H

-- A join bounds its right input.
⊔-upper₂ : ∀ x y → y ⊑ x ⊔ y
⊔-upper₂ L L = L⊑L
⊔-upper₂ L H = H⊑H
⊔-upper₂ H L = L⊑H
⊔-upper₂ H H = H⊑H

-- The two-point lattice as a Lattice record; literals are public.
two-point : Lattice
two-point = record
  { Carrier  = Label
  ; _⊑_      = _⊑_
  ; _⊔_      = _⊔_
  ; ⊥ₗ       = L
  ; ⊑-trans  = ⊑-trans
  ; ⊔-upper₁ = ⊔-upper₁
  ; ⊔-upper₂ = ⊔-upper₂
  }
