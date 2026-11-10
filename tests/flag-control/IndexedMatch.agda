{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module IndexedMatch where
open import SecretTypes.Prelude

-- Must be refused, and only because --cubical-compatible is in force: this
-- is the definition of just-inj that Prelude deliberately does not use.
-- Matching refl here needs injectivity of `just`, which the flag rejects as
-- -WUnsupportedIndexedMatch, made fatal by -W error.  Without the flag it
-- type-checks, so scripts/check.sh fails if this module is ever accepted:
-- that is the evidence the canonical invocation actually ran.
invalid : {A : Set} {a b : A} → just a ≡ just b → a ≡ b
invalid refl = refl
