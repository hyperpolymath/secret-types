{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Minimal prelude over Agda builtins only (no stdlib): negation, equality
-- lemmas, Maybe with monadic bind, and pairs.  Used by the TINI proof.
module SecretTypes.Prelude where

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Sigma public using (Σ; _,_; fst; snd)

data ⊥ : Set where
-- Negation is evidence that a proposition would imply a contradiction.
¬_ : Set → Set
¬ A = A → ⊥
infix 4 _≢_
-- Express inequality by ruling out evidence of equality.
_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

-- Reverse an equality proof.
sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
-- Chain equality proofs through their shared intermediate value.
trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q
-- Carry equality through application of a function.
cong : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl
-- Carry equalities in both arguments through a binary function.
cong₂ : {A B C : Set} (f : A → B → C) {a b : A} {c d : B} → a ≡ b → c ≡ d → f a c ≡ f b d
cong₂ f refl refl = refl
-- Transport evidence for the predicate P along an equality of its indices.
subst : {A : Set} (P : A → Set) {a b : A} → a ≡ b → P a → P b
subst P refl p = p

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

-- Recover equality of the values inside equal just results.
just-inj : {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl = refl

-- Pass a present value to f and return its result; propagate nothing
-- without applying f when the input is absent.
bind : {A : Set} → Maybe A → (A → Maybe A) → Maybe A
bind nothing  f = nothing
bind (just a) f = f a

infixr 2 _×_
-- Pair evidence for two propositions without a dependency between them.
_×_ : Set → Set → Set
P × Q = Σ P (λ _ → Q)

-- From a successful bind, recover the intermediate value and proofs that
-- both the input and the continuation produced the required just results.
bind-just : {A : Set} (m : Maybe A) (f : A → Maybe A) {t : A}
          → bind m f ≡ just t → Σ A (λ a → (m ≡ just a) × (f a ≡ just t))
bind-just (just a) f e = a , (refl , e)

-- From a contradiction, anything.
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- Evidence for P, or evidence that P is refuted.  Same constructors as
-- Lintel's local copy (metadatastician/lintel, LNT-01), which it drops on
-- re-pin.
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

-- Decide equality of naturals.
infix 4 _≟_
_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc n = no λ ()
suc m ≟ zero  = no λ ()
suc m ≟ suc n with m ≟ n
... | yes refl = yes refl
... | no m≢n   = no λ { refl → m≢n refl }

-- A decidable proposition is stable: double negation can be removed.
dec-stable : {P : Set} → Dec P → ¬ ¬ P → P
dec-stable (yes p) _  = p
dec-stable (no ¬p) h = ⊥-elim (h ¬p)

-- Excluded middle holds under double negation, for every proposition.
¬¬-dec : (P : Set) → ¬ ¬ Dec P
¬¬-dec P k = k (no λ p → k (yes p))
