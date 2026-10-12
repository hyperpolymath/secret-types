{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ExplicitFlow where
open import SecretTypes.Lattice
open import SecretTypes.Lang
open import SecretTypes.Typing

-- Must fail: assigning the secret variable to the public one needs H ⊑ L.
invalid : L ⊢ (lo ≔ var hi)
invalid = assign L⊑L
