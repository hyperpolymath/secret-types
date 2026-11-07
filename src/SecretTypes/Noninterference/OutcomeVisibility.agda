{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Making termination observable changes the security statement.  This
-- observation exposes both the public result of a finishing run and whether
-- a run returned a result at all.
module SecretTypes.Noninterference.OutcomeVisibility where

open import SecretTypes.Prelude
open import SecretTypes.Lang.Two
open import SecretTypes.Typing
open import SecretTypes.Witness using
  (secret-loop; secret-loop-typed; s₀; s₁; low-equivalent)

publicOutcome : Nat → Cmd → Store → Maybe Nat
publicOutcome fuel c s with exec fuel c s
... | nothing = nothing
... | just t  = just (low t)

-- The same well-typed command and fuel expose different outcomes from
-- low-equivalent initial stores.  TINI does not compare a run returning
-- nothing against a finishing run.
secret-loop-never-finishes : ∀ fuel → exec fuel secret-loop s₀ ≡ nothing
secret-loop-never-finishes zero = refl
secret-loop-never-finishes (suc fuel) = secret-loop-never-finishes fuel

secret-loop-stops-with-fuel : ∀ fuel →
  exec (suc fuel) secret-loop s₁ ≡ just s₁
secret-loop-stops-with-fuel fuel = refl

outcome-spins : publicOutcome 3 secret-loop s₀ ≡ nothing
outcome-spins = refl

outcome-stops : publicOutcome 3 secret-loop s₁ ≡ just 0
outcome-stops = refl

outcome-different : publicOutcome 3 secret-loop s₀ ≢
                    publicOutcome 3 secret-loop s₁
outcome-different ()

-- This stronger two-run statement is false for the current language.
TSNI : Set
TSNI = ∀ {pc c} fuel {s s'} → pc ⊢ c → s ≈ s' →
       publicOutcome fuel c s ≡ publicOutcome fuel c s'

termination-sensitive-fails : ¬ TSNI
termination-sensitive-fails h =
  outcome-different
    (h {c = secret-loop} 3 {s = s₀} {s' = s₁}
       secret-loop-typed low-equivalent)
