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
-- case (that is the "termination-insensitive").
--
-- Each result is the generic one (SecretTypes.Noninterference.Generic) at
-- the two-point lattice and the public observer, the principal observer at
-- L; low-equivalence is exactly agreement for that observer.
--   eval-low   a public expression reads the same in low-equivalent stores
--   confine    a command typed under a secret pc leaves the public variable alone
--   tini       the theorem above
module SecretTypes.Noninterference where

open import SecretTypes.Prelude
open import SecretTypes.Lattice
open import SecretTypes.Lattice.Record using (Observer; principal)
open import SecretTypes.Lang.Two
open import SecretTypes.Typing
import SecretTypes.Noninterference.Generic two two-point label as G

-- The public observer sees exactly the labels that flow to L.
public-observer : Observer two-point
public-observer = principal two-point L

-- Low-equivalence is agreement for the public observer, both ways.
≈→agree : ∀ {s s'} → s ≈ s' → s G.≈[ Observer.sees public-observer ] s'
≈→agree eq lo _ = eq
≈→agree eq hi ()

-- Recover low-equivalence from agreement on the public observer's variables.
agree→≈ : ∀ {s s'} → s G.≈[ Observer.sees public-observer ] s' → s ≈ s'
agree→≈ f = f lo L⊑L

----------------------------------------------------------------------
-- A public expression has equal values in stores that agree on lo.
eval-low : ∀ e {s s'} → lab e ≡ L → s ≈ s' → eval s e ≡ eval s' e
eval-low e p eq = G.eval-low public-observer e (subst (_⊑ L) (sym p) L⊑L) (≈→agree eq)

----------------------------------------------------------------------
-- Confinement: under a secret program counter the public variable is unchanged.
-- Requires evidence that execution finishes with the supplied fuel.
confine : ∀ {c} fuel {s t} → H ⊢ c → exec fuel c s ≡ just t → low t ≡ low s
confine fuel tc e = G.confine public-observer fuel (λ ()) tc e lo L⊑L

----------------------------------------------------------------------
-- Finishing runs of a well-typed command preserve low-equivalence.
-- The fuel bounds may differ; runs returning nothing are not covered.
tini : ∀ {pc c} fuel fuel' {s s' t t'} → pc ⊢ c → s ≈ s'
     → exec fuel c s ≡ just t → exec fuel' c s' ≡ just t' → t ≈ t'
tini fuel fuel' tc eq e e' = agree→≈ (G.tini public-observer fuel fuel' tc (≈→agree eq) e e')
