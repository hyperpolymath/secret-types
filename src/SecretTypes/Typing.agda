{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Volpano–Smith security typing: expressions get the join of their
-- variables' labels; commands are typed under a program-counter label.
module SecretTypes.Typing where

open import SecretTypes.Prelude
open import SecretTypes.Lattice
open import SecretTypes.Lang

lab : Expr → Label
lab (lit _)    = L
lab (var x)    = label x
lab (plus a b) = lab a ⊔ lab b

infix 3 _⊢_
data _⊢_ : Label → Cmd → Set where
  skip   : ∀ {pc} → pc ⊢ skip
  assign : ∀ {pc x e} → pc ⊔ lab e ⊑ label x → pc ⊢ (x ≔ e)
  seq    : ∀ {pc c₁ c₂} → pc ⊢ c₁ → pc ⊢ c₂ → pc ⊢ (c₁ ﹔ c₂)
  ifz    : ∀ {pc e c₁ c₂} → pc ⊔ lab e ⊢ c₁ → pc ⊔ lab e ⊢ c₂ → pc ⊢ ifz e c₁ c₂
  while  : ∀ {pc e c} → pc ⊔ lab e ⊢ c → pc ⊢ while e c
