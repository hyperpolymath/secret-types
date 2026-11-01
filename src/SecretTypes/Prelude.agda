{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Minimal prelude over Agda builtins only (no stdlib): negation, equality
-- lemmas, Maybe with monadic bind, and pairs.  Used by the TINI proof.
module SecretTypes.Prelude where

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Sigma public using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit public using (⊤; tt)

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

-- NOT provided: an injectivity lemma for `just`.  It was here
-- (`just-inj : just a ≡ just b → a ≡ b`) until 2026-11-01 and nothing used it.
-- Under the canonical flag set (scripts/proof-flags.sh, which includes
-- --cubical-compatible per PROOF-POLICY §2.1) it is refused:
--
--   warning: -W[no]UnsupportedIndexedMatch
--   This clause uses pattern-matching features that are not yet supported by
--   Cubical Agda ... Reason: It relies on injectivity of the data constructor
--   just, which is not yet supported
--
-- Deleting an unused lemma is the honest fix; disabling the warning, or the
-- flag, would have bought a green gate with a weaker check.  If a later proof
-- needs it, the way in is a cubical-compatible formulation, not a suppression.

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

-- Predecessor.  `suc` is a constructor, so `pred` computes on `suc k`
-- definitionally — which is what makes the retraction below usable.  The
-- predecessor of zero is zero.
pred : Nat → Nat
pred zero    = zero
pred (suc k) = k

-- Decide an equality of successors by deciding the predecessors' equality.
--
-- This exists because of a real constraint, not for elegance.  Proving
-- injectivity of `suc` directly — matching `suc m ≡ suc n` and returning `refl` —
-- asks for constructor injectivity, which Cubical Agda does not support
-- (`-WUnsupportedIndexedMatch`), and the canonical flag set (scripts/proof-flags.sh)
-- makes that warning fatal.  Here the pullback is a retraction rather than a
-- rule: `cong pred q : pred (suc m) ≡ pred (suc n)`, and both sides *reduce* to
-- `m` and `n`, so the negative case needs no injectivity.
--
-- The helper is deliberately concrete rather than a general "map a decision
-- along a retraction": in the general form `g` is a variable and `g (f x)` does
-- not reduce to `x`, so the negative case would need the retraction law as a
-- hypothesis and a transport.  At `suc`/`pred` the computation is definitional.
suc-dec : {m n : Nat} → Dec (m ≡ n) → Dec (suc m ≡ suc n)
suc-dec (yes p) = yes (cong suc p)
suc-dec (no ¬p) = no λ q → ¬p (cong pred q)

-- Decide equality of naturals.
infix 4 _≟_
_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc n = no λ ()
suc m ≟ zero  = no λ ()
suc m ≟ suc n = suc-dec (m ≟ n)

-- A decidable proposition is stable: double negation can be removed.
dec-stable : {P : Set} → Dec P → ¬ ¬ P → P
dec-stable (yes p) _  = p
dec-stable (no ¬p) h = ⊥-elim (h ¬p)

-- Excluded middle holds under double negation, for every proposition.
¬¬-dec : (P : Set) → ¬ ¬ Dec P
¬¬-dec P k = k (no λ p → k (yes p))
