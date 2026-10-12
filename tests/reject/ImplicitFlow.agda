{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ImplicitFlow where
open import SecretTypes.Lattice
open import SecretTypes.Lang
open import SecretTypes.Typing

-- Must fail: branching on the secret raises the program counter to H, so
-- the public assignment inside the branch needs H ⊑ L.
invalid : L ⊢ ifz (var hi) (lo ≔ lit 0) (lo ≔ lit 1)
invalid = ifz (assign L⊑L) (assign L⊑L)
