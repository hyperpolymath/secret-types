{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The Lattice record over which typing and TINI are stated, and observers.
-- The record is defined once, here; instances (the two-point lattice in
-- SecretTypes.Lattice, Lintel's reader-set lattice) are values of it.
--
-- Its fields are the measured census (PROOF-STATUS N-6), not a full
-- algebra: TINI uses both upper-bound laws of ⊔ and, for principal
-- observers only, transitivity of ⊑.  Each is necessary
-- (SecretTypes.Countermodels); nothing else is needed (scripts/minimal-laws.sh):
-- no decidability, no reflexivity, antisymmetry, leastness of ⊔ or top.
-- ⊥ₗ is the label of literals and needs no law.
module SecretTypes.Lattice.Record where

open import SecretTypes.Prelude

record Lattice : Set₁ where
  infix  4 _⊑_
  infixl 6 _⊔_
  field
    Carrier  : Set
    _⊑_      : Carrier → Carrier → Set
    _⊔_      : Carrier → Carrier → Carrier
    ⊥ₗ       : Carrier
    ⊑-trans  : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊔-upper₁ : ∀ x y → x ⊑ x ⊔ y
    ⊔-upper₂ : ∀ x y → y ⊑ x ⊔ y

-- An observer is the set of labels it sees, closed downwards: whatever may
-- flow to a seen label is seen too.
record Observer (𝓛 : Lattice) : Set₁ where
  open Lattice 𝓛
  field
    sees   : Carrier → Set
    sees-↓ : ∀ {x y} → x ⊑ y → sees y → sees x

-- The principal observer at level o sees exactly the labels that flow to o.
-- Down-closure is transitivity; this is the only use of ⊑-trans.
principal : (𝓛 : Lattice) → Lattice.Carrier 𝓛 → Observer 𝓛
principal 𝓛 o = record { sees = _⊑ o ; sees-↓ = ⊑-trans }
  where open Lattice 𝓛
