{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- A small while-language with one public and one secret variable, and a
-- fuel-indexed big-step semantics.  Fuel is what makes "termination-
-- insensitive" a real qualifier: a loop that does not finish within the
-- fuel returns `nothing`, and the theorem is stated only for runs that
-- return `just`.
module SecretTypes.Lang where

open import SecretTypes.Prelude
open import SecretTypes.Lattice

data Var : Set where
  lo hi : Var

-- Classify the public variable as L and the secret variable as H.
label : Var → Label
label lo = L
label hi = H

record Store : Set where
  constructor ⟨_,_⟩
  field
    low  : Nat
    high : Nat
open Store public

data Expr : Set where
  lit  : Nat → Expr
  var  : Var → Expr
  plus : Expr → Expr → Expr

infixr 5 _﹔_
data Cmd : Set where
  skip  : Cmd
  _≔_   : Var → Expr → Cmd
  _﹔_   : Cmd → Cmd → Cmd
  ifz   : Expr → Cmd → Cmd → Cmd      -- if e = 0 then c₁ else c₂
  while : Expr → Cmd → Cmd            -- while e = 0 do c

-- Evaluate an expression using the store's current variable values.
eval : Store → Expr → Nat
eval s (lit n)    = n
eval s (var lo)   = low s
eval s (var hi)   = high s
eval s (plus a b) = eval s a + eval s b

-- Return a store with the selected variable replaced, preserving the other.
update : Var → Nat → Store → Store
update lo n ⟨ l , h ⟩ = ⟨ n , h ⟩
update hi n ⟨ l , h ⟩ = ⟨ l , n ⟩

-- exec fuel c s: `just t` if c runs to completion within fuel, else `nothing`.
-- Fuel bounds recursive loop evaluation: each while consumes one unit,
-- even when its guard is non-zero.  At zero fuel, while returns `nothing`.
-- Other commands consume no fuel; sequence reuses it for both commands,
-- and a loop's body and continuation each receive the remaining fuel.
exec      : Nat → Cmd → Store → Maybe Store
-- Run the first branch for guard value zero, otherwise the second, using
-- the supplied fuel unchanged; return the selected branch's result.
execIf    : Nat → Nat → Cmd → Cmd → Store → Maybe Store      -- guard value, branches
-- Continue a loop after its fuel decrement, using the supplied guard value.
-- Non-zero returns `just s`; zero runs the body then repeats the loop with
-- the same remaining fuel, re-evaluating e in the updated store.  Return
-- `nothing` if either the body or the repeated loop exhausts its fuel.
execWhile : Nat → Nat → Expr → Cmd → Store → Maybe Store     -- remaining fuel, guard value

exec fuel skip          s = just s
exec fuel (x ≔ e)       s = just (update x (eval s e) s)
exec fuel (c₁ ﹔ c₂)     s = bind (exec fuel c₁ s) (exec fuel c₂)
exec fuel (ifz e c₁ c₂) s = execIf fuel (eval s e) c₁ c₂ s
exec zero       (while e c) s = nothing
exec (suc fuel) (while e c) s = execWhile fuel (eval s e) e c s

execIf fuel zero    c₁ c₂ s = exec fuel c₁ s
execIf fuel (suc _) c₁ c₂ s = exec fuel c₂ s

execWhile fuel zero    e c s = bind (exec fuel c s) (exec fuel (while e c))
execWhile fuel (suc _) e c s = just s

-- Low-equivalence: the public observer sees the same thing.
infix 4 _≈_
_≈_ : Store → Store → Set
s ≈ s' = low s ≡ low s'
