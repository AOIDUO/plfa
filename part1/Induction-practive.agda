module plfa.part1.Induction-practive where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = 
    begin
        (suc m + n) + p 
    ≡⟨⟩ 
        suc (m + n) + p 
    ≡⟨⟩
        suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
        suc (m + (n + p))
    ≡⟨⟩
        suc m + (n + p)
    ∎ 

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = begin 
        (suc m) + zero
    ≡⟨ cong suc (+-identityʳ m) ⟩
        suc m   
    ∎

+-identityʳ′ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ′ zero = refl
+-identityʳ′ (suc m) rewrite +-identityʳ′ m = refl 

+-suc : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = begin 
        (suc m) + suc n
    ≡⟨ cong suc (+-suc m n )⟩
        suc ( (suc m) + n)
    ∎

+-suc′ : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin
        m + zero
    ≡⟨ +-identityʳ m ⟩
        m
    ∎

+-comm m (suc n) = begin 
        m + (suc n)
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n ) ⟩
        suc (n + m)
    ≡⟨⟩
        (suc n) + m
    ∎

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identityʳ′ m  = refl
+-comm′ m (suc n) rewrite  +-suc′ m n | +-comm′ m n = refl

+-comm′′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′′ zero n rewrite +-identityʳ′ n = refl
+-comm′′ (suc m) n rewrite +-comm′′ m n | sym (+-suc′ n m )  = refl


+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = 
    begin 
        (m + n) + (p + q)
    ≡⟨ sym ( +-assoc (m + n) p q ) ⟩
        ((m + n) + p) + q
    ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
        (m + (n + p)) + q
    ∎

+-rearrange2 : ∀ (m n p q : ℕ) → m + (n + p) + q ≡ (m + n) + (p + q) 
+-rearrange2 m n p q = 
    begin 
        m + (n + p) + q 
    ≡⟨⟩
        (m + (n + p)) + q   
    ≡⟨ cong (_+ q) (sym (+-assoc m n p)) ⟩
        ((m + n) + p) + q   
    ≡⟨⟩
        (m + n) + p + q   
    ≡⟨ +-assoc (m + n) p q ⟩ 
        (m + n) + (p + q) 
    ∎
  