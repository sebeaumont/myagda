module Naturals where

-- Arithmetic using Peano's numbers.

-- Upto proof of additive (ℕ,+,1) and multiplicative (ℕ,*,0) monoids
-- which (AFAICT) needs distributivity of * over + to prove
-- associativity for the multiplicative monoid.

-- See: README.org for sources and citations.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- So we can use decimal notation in Agda (used for shorthand in identities)
{-# BUILTIN NATURAL ℕ #-}

-- We use a DIY Equality module for now to show how the tools for step
-- by step equational reasoning work.
-- otherwise: import Relation.Binary.PropositionalEquality as Eq

import Equality as Eq 
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

--------------------------------------------------------------------------------
-- The additive monoid (ℕ,+,0)

-- Definition 1. Inductive definition of addition 
_+_ : ℕ → ℕ → ℕ
zero    + y = y
(suc x) + y = suc (x + y)

infixl 6 _+_

-- Theorem 1. Associativity of addition
+-assoc : ∀ (n m k : ℕ) → (n + m) + k ≡ n + (m + k) -- the induction hypothesis
+-assoc zero m k =
  begin
    (zero + m) + k
  ≡⟨⟩
    m + k
  ≡⟨⟩
    zero + (m + k)
  ∎
+-assoc (suc n) m k =
  begin
    (suc n + m) + k             -- using inductive defintion of addition
  ≡⟨⟩
    suc (n + m) + k
  ≡⟨⟩
    suc ((n + m) + k)           -- work down simplifying
  ≡⟨ cong suc (+-assoc n m k) ⟩ -- this step needs some explanation: [1]
    suc (n + (m + k))           -- work up from goal simplifying
  ≡⟨⟩
    suc n + (m + k)             -- goal
  ∎

-- [1] A relation is said to be a congruence relative to a given
-- function if it is preserved by application of the function. The
-- recursive application of the function (+-assoc n m k) has the type
-- of the induction hypotheis and `cong suc` prefaces `suc` to each
-- side of the equation; establishing evidence for the hypotheis.
-- See: plfa Ch 2. Induction.lagda.md

-- Lemma 1.1 additive identity of 0
+-identity⃗ : ∀ (n : ℕ) → (n + zero) ≡ n
+-identity⃗ zero = refl
+-identity⃗ (suc n) = cong suc (+-identity⃗ n)

+-identity⃐ : ∀ (n : ℕ) → zero + n ≡ n
+-identity⃐ zero = refl
+-identity⃐ (suc n) = cong suc (+-identity⃐ n)

-- Lemma 1.2 define suc on second argument of addition
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- Theorem 2 commutativity of addition
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity⃗ m ⟩
    m
  ≡⟨⟩
    (zero + m)
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m
  ∎

-- Corollary 1. rearragement of parenthesis (+ is left associative)
-- no induction just apply +-assoc twice to shift parens R and L
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q 
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩       -- shift parens from R to L
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩     -- shift parens from L to R
    (m + (n + p)) + q
  ∎


----------------------------------------------------------------------------------
-- monoid (ℕ,*,1)

-- Defintion 2. inductive definition of multiplication
_*_ : ℕ → ℕ → ℕ
zero    * _  = zero
(suc n) * m  = m + (n * m) 

-- Lemma 2.1 right multiplicative identity
*-identity⃗ : ∀ (n : ℕ) → n * 1 ≡ n
*-identity⃗ zero = refl
*-identity⃗ (suc n) =
  begin
    (suc n) * 1
  ≡⟨⟩
    suc (n * 1)
  ≡⟨ cong suc (*-identity⃗ n) ⟩
    suc n
  ∎

-- Lemma 2.2 left multiplicative identity
*-identity⃐ : ∀ (n : ℕ) → 1 * n ≡ n
*-identity⃐ zero = refl
*-identity⃐ (suc n) =
  begin
   1 * (suc n) 
  ≡⟨⟩
    suc (n + zero)              -- computer found this for me!
  ≡⟨ cong suc (*-identity⃐ n) ⟩
    suc n
  ∎

--  Theorem 2. multiplication distributes over addition
*-distrib-+ : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨ cong (_* p) (+-comm (suc m) n) ⟩  -- commutativity of +
    (n + (suc m)) * p
  ≡⟨ cong (_* p) (+-suc n m) ⟩         -- suc defined on 2nd arg
    (suc (n + m)) * p
  ≡⟨⟩                                  -- inductive defintion of *
    p + ((n + m) * p)           
  ≡⟨ cong (p +_) (*-distrib-+ n m p) ⟩ -- inductive case of *-distrib-+
    p + (n * p + m * p)         
  ≡⟨ cong (p +_) (+-comm (n * p) (m * p)) ⟩ -- commutativity of +
    p + (m * p + n * p)         
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩ -- move parens L 
    (p + (m * p)) + n * p       
  ≡⟨⟩                                  -- ^ inductive defintion of *
    (suc m) * p + n * p         
  ∎
  
-- Theorem 3. Associativity of multiplication
*-assoc : ∀ (n m l : ℕ) -> (n * m) * l ≡ n * (m * l)
*-assoc zero _ _ = refl
*-assoc (suc n) m l =
  begin
    ((suc n) * m) * l                  
  ≡⟨⟩                                  -- inductive defintion of *
    (m + n * m) * l                    
  ≡⟨ *-distrib-+ m (n * m) l ⟩         -- * distributes over +
    (m * l) + (n * m) * l
  ≡⟨ cong ((m * l) +_) (*-assoc n m l) ⟩ -- inductive case of *-assoc
    (m * l) + n * (m * l)
  ≡⟨⟩                                 -- ^ inductive defintion of *
    suc n * (m * l)
  ∎

--  Are we done here? TODO shorthand versions of these using rewrite?
