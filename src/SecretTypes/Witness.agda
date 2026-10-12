{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Computed witnesses (TESTED): the typing side-condition is load-bearing.
module SecretTypes.Witness where

open import SecretTypes.Prelude
open import SecretTypes.Lattice
open import SecretTypes.Lang
open import SecretTypes.Typing
open import SecretTypes.Noninterference

-- An explicit flow and an implicit flow.  Both are refused by the type
-- system (tests/reject/), and both actually leak: from low-equivalent
-- stores they end low-inequivalent.
explicit implicit : Cmd
explicit = lo ≔ var hi
implicit = ifz (var hi) (lo ≔ lit 0) (lo ≔ lit 1)

s₀ s₁ : Store
s₀ = ⟨ 0 , 0 ⟩
s₁ = ⟨ 0 , 1 ⟩

low-equivalent : s₀ ≈ s₁
low-equivalent = refl

explicit-leaks : ¬ (∀ {t t'} → exec 1 explicit s₀ ≡ just t → exec 1 explicit s₁ ≡ just t' → t ≈ t')
explicit-leaks h = absurd (h refl refl)
  where absurd : 0 ≡ 1 → ⊥
        absurd ()

implicit-leaks : ¬ (∀ {t t'} → exec 1 implicit s₀ ≡ just t → exec 1 implicit s₁ ≡ just t' → t ≈ t')
implicit-leaks h = absurd (h refl refl)
  where absurd : 0 ≡ 1 → ⊥
        absurd ()

-- A well-typed program with a secret loop guard: it spins forever when the
-- secret is 0 and stops at once otherwise, touching nothing public.
secret-loop : Cmd
secret-loop = while (var hi) skip

secret-loop-typed : L ⊢ secret-loop
secret-loop-typed = while skip

-- From s₁ the loop does not run (guard 1): finishes.  From s₀ it runs until
-- the fuel is spent: `nothing`, so TINI has nothing to say — and need not.
secret-loop-stops : exec 3 secret-loop s₁ ≡ just s₁
secret-loop-stops = refl

secret-loop-spins : exec 3 secret-loop s₀ ≡ nothing
secret-loop-spins = refl

-- Termination-insensitivity, made explicit: the public observer cannot
-- tell s₀ from s₁ by any finishing run of a well-typed program, but CAN by
-- whether the program finishes.  That is the channel this theorem leaves
-- open, by name.
