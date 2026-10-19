{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Volpano–Smith security typing over any order and join: expressions get
-- the join of their variables' labels; commands are typed under a
-- program-counter label.  The rules use the operations only, no laws, so a
-- structure that breaks a law still has these rules
-- (SecretTypes.Countermodels).
open import SecretTypes.Lang

module SecretTypes.Typing.Generic
  {Carrier : Set}
  (_⊑_ : Carrier → Carrier → Set)
  (_⊔_ : Carrier → Carrier → Carrier)
  (⊥ₗ : Carrier)                 -- the label of a literal
  (label : Var → Carrier)        -- the label of each variable
  where

-- Module parameters take no fixity, so joins and flows are parenthesised.

-- Classify expressions with ⊥ₗ for literals and label for variables,
-- joining the operands' labels for addition.
lab : Expr → Carrier
lab (lit _)    = ⊥ₗ
lab (var x)    = label x
lab (plus a b) = lab a ⊔ lab b

infix 3 _⊢_
data _⊢_ : Carrier → Cmd → Set where
  skip   : ∀ {pc} → pc ⊢ skip
  assign : ∀ {pc x e} → (pc ⊔ lab e) ⊑ label x → pc ⊢ (x ≔ e)
  seq    : ∀ {pc c₁ c₂} → pc ⊢ c₁ → pc ⊢ c₂ → pc ⊢ (c₁ ﹔ c₂)
  ifz    : ∀ {pc e c₁ c₂} → (pc ⊔ lab e) ⊢ c₁ → (pc ⊔ lab e) ⊢ c₂ → pc ⊢ ifz e c₁ c₂
  while  : ∀ {pc e c} → (pc ⊔ lab e) ⊢ c → pc ⊢ while e c
