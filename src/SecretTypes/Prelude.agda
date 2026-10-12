{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module SecretTypes.Prelude where

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Sigma public using (Σ; _,_; fst; snd)

data ⊥ : Set where
¬_ : Set → Set
¬ A = A → ⊥
infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q
cong : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl
cong₂ : {A B C : Set} (f : A → B → C) {a b : A} {c d : B} → a ≡ b → c ≡ d → f a c ≡ f b d
cong₂ f refl refl = refl
subst : {A : Set} (P : A → Set) {a b : A} → a ≡ b → P a → P b
subst P refl p = p

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

just-inj : {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl = refl

bind : {A : Set} → Maybe A → (A → Maybe A) → Maybe A
bind nothing  f = nothing
bind (just a) f = f a

infixr 2 _×_
_×_ : Set → Set → Set
P × Q = Σ P (λ _ → Q)

bind-just : {A : Set} (m : Maybe A) (f : A → Maybe A) {t : A}
          → bind m f ≡ just t → Σ A (λ a → (m ≡ just a) × (f a ≡ just t))
bind-just (just a) f e = a , (refl , e)
