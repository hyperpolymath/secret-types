{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module TerminationSensitiveNI where

open import SecretTypes.Prelude
open import SecretTypes.Witness
open import SecretTypes.Noninterference.OutcomeVisibility

-- Must fail: the secret loop returns nothing from s₀ and a public result
-- from s₁, even though those stores are low-equivalent.
invalid : publicOutcome 3 secret-loop s₀ ≡ publicOutcome 3 secret-loop s₁
invalid = refl
