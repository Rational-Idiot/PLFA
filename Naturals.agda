{-# OPTIONS --exact-split #-}

-- Going through https://plfa.inf.ed.ac.uk/Naturals
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

-- Exercise _^_ (recommended)
-- Define exponentiation, which is given by the following equations:
-- m ^ 0        =  1
-- m ^ (1 + n)  =  m * (m ^ n)
-- Check that 3 ^ 4 is 81.

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl

-- Mah man Monus
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = 0
suc m ∸ suc n = m ∸ n

-- Exercise Bin (stretch)
-- A more efficient representation of natural numbers uses a binary rather than a unary system.
-- We represent a number as a bitstring:

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- Define a function
-- inc : Bin → Bin

-- that converts a bitstring to the bitstring for the next higher number.
-- For example, since 1100 encodes twelve, we should have:
-- inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = inc x O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

-- define a pair of functions to convert between the two representations.
-- to   : ℕ → Bin
-- from : Bin → ℕ

-- For the former, choose the bitstring to have no leading zeros if it represents a positive natural, and represent zero by ⟨⟩ O.
-- Confirm that these both give the correct answer for zero through four.

to : ℕ → Bin
to zero = ⟨⟩
to (suc x) = inc (to x)

_ : to 0 ≡ ⟨⟩
_ = refl

_ : to 1 ≡ (⟨⟩ I)
_ = refl

_ : to 2 ≡ (⟨⟩ I O)
_ = refl

_ : to 3 ≡ (⟨⟩ I I)
_ = refl

_ : to 4 ≡ (⟨⟩ I O O)
_ = refl

from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = 2 * from x
from (x I) = (2 * from x) + 1

_ : from ⟨⟩ ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl
