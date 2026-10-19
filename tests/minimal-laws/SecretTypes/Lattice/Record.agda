{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The census record for scripts/minimal-laws.sh: SecretTypes.Lattice.Record
-- with ONLY the laws generic TINI is claimed to use (PROOF-STATUS N-6):
-- ⊔-upper₁, ⊔-upper₂ and observer down-closure.  No ⊑-trans (and so no
-- `principal`), no decidability, no ⊥ ⊑ x.  Every field line here must
-- appear verbatim in the real record; the script checks that.
module SecretTypes.Lattice.Record where

record Lattice : Set₁ where
  infix  4 _⊑_
  infixl 6 _⊔_
  field
    Carrier  : Set
    _⊑_      : Carrier → Carrier → Set
    _⊔_      : Carrier → Carrier → Carrier
    ⊥ₗ       : Carrier
    ⊔-upper₁ : ∀ x y → x ⊑ x ⊔ y
    ⊔-upper₂ : ∀ x y → y ⊑ x ⊔ y

record Observer (𝓛 : Lattice) : Set₁ where
  open Lattice 𝓛
  field
    sees   : Carrier → Set
    sees-↓ : ∀ {x y} → x ⊑ y → sees y → sees x
