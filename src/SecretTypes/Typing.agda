{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Volpano–Smith security typing at the two-point lattice: the generic rules
-- (SecretTypes.Typing.Generic) with the public variable labelled L, the
-- secret variable H, and literals L.
module SecretTypes.Typing where

open import SecretTypes.Lattice
open import SecretTypes.Lang.Two

-- Classify the public variable as L and the secret variable as H.
label : Var → Label
label lo = L
label hi = H

-- lab classifies an expression as secret exactly when it mentions hi;
-- literals and expressions using only lo are public.
open import SecretTypes.Typing.Generic two _⊑_ _⊔_ L label public
