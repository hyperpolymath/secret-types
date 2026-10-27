{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Each law the generic TINI proof uses is necessary (PROOF-STATUS N-8).
-- For ⊔-upper₁, ⊔-upper₂ and observer down-closure there is a structure
-- that keeps the other two, the typing rules of SecretTypes.Typing.Generic
-- unchanged, and a well-typed program that leaks: TINI
-- (SecretTypes.Noninterference.Statement) is refuted.  NoTrans is of a
-- different kind: it drops ⊑-trans, which generic TINI does not use, and
-- shows that the principal observer then need not be down-closed and TINI
-- fails for it.  That is why `principal` needs ⊑-trans.
--
--   NoUpper₁       x ⊔ y = y         ⊔-upper₂, down-closure, ⊑-trans hold
--   NoUpper₂       x ⊔ y = x         ⊔-upper₁, down-closure, ⊑-trans hold
--   NoDownClosure  sees x = (x ≡ H)  the two-point lattice itself
--   NoTrans        five points       both upper bounds hold; "flows to L"
--                                    is then not down-closed
--
-- The laws the proof does not use (decidability, ⊥ ⊑ x, reflexivity,
-- antisymmetry, leastness of ⊔, a top) need no countermodel: the proof
-- checks without them (scripts/minimal-laws.sh).
module SecretTypes.Countermodels where

open import SecretTypes.Prelude
open import SecretTypes.Lang.Two hiding (_≈_)
open import SecretTypes.Lattice using (Label; L; H; _⊑_; L⊑L; L⊑H; H⊑H; _⊔_)

private
  absurd : 0 ≡ 1 → ⊥
  absurd ()

-- The public variable labelled L, the secret one H, as in SecretTypes.Typing.
std : Var → Label
std lo = L
std hi = H

-- Two stores differing only in the secret variable.
s₀ s₁ : Store
s₀ = ⟨ 0 , 0 ⟩
s₁ = ⟨ 0 , 1 ⟩

----------------------------------------------------------------------
-- ⊔-upper₁ dropped: the join forgets its left input, so a secret program
-- counter vanishes inside a branch and the implicit flow is typable.
module NoUpper₁ where
  -- Combine labels by keeping only the right input.
  _⊔ʳ_ : Label → Label → Label
  x ⊔ʳ y = y

  -- The right projection still bounds its right input in the two-point order.
  upper₂ : ∀ x y → y ⊑ (x ⊔ʳ y)
  upper₂ _ L = L⊑L
  upper₂ _ H = H⊑H

  -- Joining H with L gives L, which cannot bound H.
  not-upper₁ : ¬ (∀ x y → x ⊑ (x ⊔ʳ y))
  not-upper₁ h with h H L
  ... | ()

  open import SecretTypes.Noninterference.Statement two _⊑_ _⊔ʳ_ L std

  -- Reveal whether hi is zero by writing 0 or 1 to lo.
  implicit : Cmd
  implicit = ifz (var hi) (lo ≔ lit 0) (lo ≔ lit 1)

  -- The faulty join admits both public writes under the secret guard.
  typed : L ⊢ implicit
  typed = ifz (assign L⊑L) (assign L⊑L)

  -- The observer at L sees the same lo value despite the different hi values.
  agree : s₀ ≈[ _⊑ L ] s₁
  agree lo _ = refl
  agree hi ()

  -- Refute TINI with two finishing runs that leave lo at 0 and 1.
  refutes : ¬ TINI (_⊑ L)
  refutes tini = absurd (tini 1 1 typed agree refl refl lo L⊑L)

----------------------------------------------------------------------
-- ⊔-upper₂ dropped: the join forgets its right input, so a secret operand
-- vanishes and the explicit flow is typable.
module NoUpper₂ where
  -- Combine labels by keeping only the left input.
  _⊔ˡ_ : Label → Label → Label
  x ⊔ˡ y = x

  -- The left projection still bounds its left input in the two-point order.
  upper₁ : ∀ x y → x ⊑ (x ⊔ˡ y)
  upper₁ L _ = L⊑L
  upper₁ H _ = H⊑H

  -- Joining L with H gives L, which cannot bound H.
  not-upper₂ : ¬ (∀ x y → y ⊑ (x ⊔ˡ y))
  not-upper₂ h with h L H
  ... | ()

  open import SecretTypes.Noninterference.Statement two _⊑_ _⊔ˡ_ L std

  -- Copy the secret value directly into the public variable.
  explicit : Cmd
  explicit = lo ≔ var hi

  -- The faulty join discards the expression's H label, admitting the write.
  typed : L ⊢ explicit
  typed = assign L⊑L

  -- The observer at L sees the same lo value despite the different hi values.
  agree : s₀ ≈[ _⊑ L ] s₁
  agree lo _ = refl
  agree hi ()

  -- Refute TINI with two finishing runs that copy different hi values to lo.
  refutes : ¬ TINI (_⊑ L)
  refutes tini = absurd (tini 1 1 typed agree refl refl lo L⊑L)

----------------------------------------------------------------------
-- Down-closure dropped: an observer that sees H but not L.  The lattice is
-- the genuine two-point one; a flow from lo up to hi reaches the observer
-- from a variable it does not see.
module NoDownClosure where
  -- See only H, leaving values at L unobserved despite their flow to H.
  sees : Label → Set
  sees x = x ≡ H

  -- Down-closure would require seeing L because L flows to the seen label H.
  not-down-closed : ¬ (∀ {x y} → x ⊑ y → sees y → sees x)
  not-down-closed h with h L⊑H refl
  ... | ()

  open import SecretTypes.Noninterference.Statement two _⊑_ _⊔_ L std

  -- Copy the unseen lo value into the seen variable hi.
  up : Cmd
  up = hi ≔ var lo

  -- The two-point order permits this upward flow from L to H.
  typed : L ⊢ up
  typed = assign L⊑H

  -- Two stores differing only in the variable the observer does not see.
  t₀ t₁ : Store
  t₀ = ⟨ 0 , 0 ⟩
  t₁ = ⟨ 1 , 0 ⟩

  -- The observer sees equal hi values while the unseen lo values differ.
  agree : t₀ ≈[ sees ] t₁
  agree lo ()
  agree hi _ = refl

  -- Refute TINI with two finishing runs that copy different lo values to hi.
  refutes : ¬ TINI sees
  refutes tini = absurd (tini 1 1 typed agree refl refl hi refl)

----------------------------------------------------------------------
-- ⊑-trans dropped: H ⊑ M ⊑ L but H ⋢ L, with both upper-bound laws and a
-- least element B.  "Flows to L" then sees M but not H, though H ⊑ M: it is
-- not down-closed, which is what principal observers take from ⊑-trans.
module NoTrans where
  data P : Set where
    B H′ M L′ T : P

  infix 4 _≤_
  data _≤_ : P → P → Set where
    refl≤ : ∀ {x} → x ≤ x
    B≤    : ∀ {x} → B ≤ x
    ≤T    : ∀ {x} → x ≤ T
    H≤M   : H′ ≤ M
    M≤L   : M ≤ L′

  -- The least upper bound where one exists, else T.
  _∨_ : P → P → P
  B  ∨ y  = y
  T  ∨ y  = T
  H′ ∨ B  = H′
  H′ ∨ H′ = H′
  H′ ∨ M  = M
  H′ ∨ L′ = T
  H′ ∨ T  = T
  M  ∨ B  = M
  M  ∨ H′ = M
  M  ∨ M  = M
  M  ∨ L′ = L′
  M  ∨ T  = T
  L′ ∨ B  = L′
  L′ ∨ H′ = T
  L′ ∨ M  = L′
  L′ ∨ L′ = L′
  L′ ∨ T  = T

  -- Every join bounds its left input even though the order is not transitive.
  upper₁ : ∀ x y → x ≤ (x ∨ y)
  upper₁ B  _  = B≤
  upper₁ T  _  = refl≤
  upper₁ H′ B  = refl≤
  upper₁ H′ H′ = refl≤
  upper₁ H′ M  = H≤M
  upper₁ H′ L′ = ≤T
  upper₁ H′ T  = ≤T
  upper₁ M  B  = refl≤
  upper₁ M  H′ = refl≤
  upper₁ M  M  = refl≤
  upper₁ M  L′ = M≤L
  upper₁ M  T  = ≤T
  upper₁ L′ B  = refl≤
  upper₁ L′ H′ = ≤T
  upper₁ L′ M  = refl≤
  upper₁ L′ L′ = refl≤
  upper₁ L′ T  = ≤T

  -- Every join bounds its right input even though the order is not transitive.
  upper₂ : ∀ x y → y ≤ (x ∨ y)
  upper₂ B  _  = refl≤
  upper₂ T  _  = ≤T
  upper₂ H′ B  = B≤
  upper₂ H′ H′ = refl≤
  upper₂ H′ M  = refl≤
  upper₂ H′ L′ = ≤T
  upper₂ H′ T  = refl≤
  upper₂ M  B  = B≤
  upper₂ M  H′ = H≤M
  upper₂ M  M  = refl≤
  upper₂ M  L′ = refl≤
  upper₂ M  T  = refl≤
  upper₂ L′ B  = B≤
  upper₂ L′ H′ = ≤T
  upper₂ L′ M  = M≤L
  upper₂ L′ L′ = refl≤
  upper₂ L′ T  = refl≤

  -- H′ flows to M and M to L′, but H′ does not flow to L′.
  not-trans : ¬ (∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
  not-trans t with t H≤M M≤L
  ... | ()

  -- The public variable is labelled M, the secret one H′.
  label : Var → P
  label lo = M
  label hi = H′

  open import SecretTypes.Noninterference.Statement two _≤_ _∨_ B label

  -- Copy hi at H′ into lo at M, along an allowed flow.
  explicit : Cmd
  explicit = lo ≔ var hi

  -- A counter at B permits the write from H′ to M.
  typed : B ⊢ explicit
  typed = assign H≤M

  -- Flow to L′ reveals lo at M but hides the differing hi values at H′.
  agree : s₀ ≈[ _≤ L′ ] s₁
  agree lo _ = refl
  agree hi ()

  -- Refute TINI for flow to L′ using finishing runs with different lo results.
  refutes : ¬ TINI (_≤ L′)
  refutes tini = absurd (tini 1 1 typed agree refl refl lo M≤L)
