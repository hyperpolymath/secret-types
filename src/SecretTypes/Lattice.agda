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
-- The order, as a *computed* predicate rather than an indexed family.
--
-- The representation matters here and is not cosmetic.  As an indexed family
-- (`data _⊑_ : Label → Label → Set where L⊑L; L⊑H; H⊑H`), any clause that
-- matches on a proof asks Agda to unify the proof's *indices*, which needs
-- injectivity of the index constructors `L` and `H`.  Cubical Agda does not
-- support that (`-WUnsupportedIndexedMatch`), and PROOF-POLICY §2.1 asks for
-- `--cubical-compatible`.  Recursing on the first label instead keeps
-- everything: `x ⊑ y` still records "may data at x reach y", the laws hold by
-- computation, and no proof is ever matched.  Uninhabited pairs (`H ⊑ L`) are
-- just `⊥`, so an impossible flow is still impossible to prove and the
-- expected-rejection fixtures still fail at their `⊑` obligation.
_⊑_ : Label → Label → Set
L ⊑ _ = ⊤
H ⊑ L = ⊥
H ⊑ H = ⊤

-- The named witnesses of the three inhabitable pairs.
L⊑L : L ⊑ L
L⊑L = tt
L⊑H : L ⊑ H
L⊑H = tt
H⊑H : H ⊑ H
H⊑H = tt

infixl 6 _⊔_
-- Combine flow labels: the result is secret if either input is secret.
_⊔_ : Label → Label → Label
L ⊔ y = y
H ⊔ _ = H

-- Two-point facts about public joins.  The generic proof
-- (SecretTypes.Noninterference.Generic) uses the upper-bound laws below
-- instead; these stay as the two-point reading of them.

-- A public join guarantees that its left input is public.
⊔-L₁ : ∀ {x y} → x ⊔ y ≡ L → x ≡ L
⊔-L₁ {L} _ = refl
⊔-L₁ {H} ()

-- A public join guarantees that its right input is public.
⊔-L₂ : ∀ {x y} → x ⊔ y ≡ L → y ≡ L
⊔-L₂ {L} p = p
⊔-L₂ {H} ()

----------------------------------------------------------------------
-- The census laws (SecretTypes.Lattice.Record) at the two-point lattice.

-- Flows compose.  By computation on the first label, with the impossible
-- `H ⊑ L` case discharged by the empty type.
⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans {L} _ _ = tt
⊑-trans {H} {H} {H} _ _ = tt
⊑-trans {H} {H} {L} _ ()
⊑-trans {H} {L} () _

-- A join bounds its left input.
⊔-upper₁ : ∀ x y → x ⊑ x ⊔ y
⊔-upper₁ L _ = tt
⊔-upper₁ H _ = tt

-- A join bounds its right input.
⊔-upper₂ : ∀ x y → y ⊑ x ⊔ y
⊔-upper₂ L L = tt
⊔-upper₂ L H = tt
⊔-upper₂ H L = tt
⊔-upper₂ H H = tt

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
