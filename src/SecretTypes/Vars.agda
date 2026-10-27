{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The variables of the language: any type with decidable equality.  The
-- language (SecretTypes.Lang), typing and TINI are stated over a value of
-- this record, as they are over the Lattice record; the two-point
-- development uses the two variables lo and hi (SecretTypes.Lang.Two), a
-- consumer names its own.  Decidable equality is what a store update needs
-- to tell the written variable from the others; nothing else is asked of
-- the variables.
module SecretTypes.Vars where

open import SecretTypes.Prelude

record Vars : Set₁ where
  infix 4 _≟ᵥ_
  field
    Var  : Set
    _≟ᵥ_ : (x y : Var) → Dec (x ≡ y)
