module plfa.part1.Relations-practice where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

_ : 2 ≤ 4
_ = s≤s {1} {3} ( s≤s {0} {2} (z≤n ) )

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

-- inv-z≤n: m → m ≤ zero → m ≡ zero
-- z≤n : m → zero ≤ m 
-- inv-z≤n z≤n = zero ≡ zero

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s {n} {n} (≤-refl {n})

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans {zero} {n} {p} (z≤n {n}) _ = z≤n {p}
≤-trans {suc m} {suc n} {suc p} (s≤s m≤n) (s≤s {n} {p} n≤p) = s≤s (≤-trans {m} {n} {p} m≤n n≤p)
                                --        ^
                                -- Note: here ≤-trans wants (suc n) ≤ (suc p)
                                -- (s≤s {n} {p} n≤p) ≡ (suc n) ≤ (suc p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym {suc m} {suc n} (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- ≤-antisym {suc m} {suc n} z≤n (s≤s m n) = ?

-- Preorder. Any relation that is reflexive and transitive.
-- Partial order. Any preorder that is also anti-symmetric.
-- Total order. Any partial order that is also total.

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero n = forward z≤n
≤-total′ (suc m) zero = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total′ m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward m≤n) = forward ( s≤s m≤n )
    helper (flipped m≤n) = flipped ( s≤s m≤n )


≤-Total : ∀ (m n : ℕ) → Total m n
≤-Total zero n = forward z≤n
≤-Total (suc m) zero = flipped z≤n
≤-Total (suc m) (suc n) 
    with ≤-Total m n 
... | forward m≤n = forward (s≤s {m} {n} m≤n)
... | flipped n≤m = flipped (s≤s {n} {m} n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n


+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

open import Data.Nat using (_*_)
-- *-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q

*suc : ∀ (m n : ℕ) → suc m * n  ≡ n + (m * n)
*suc m n = refl

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q rewrite 
    *suc n p 
  | *suc n q = +-mono-≤ p q (n * p) (n * q) p≤q n*p≤n*q
  where
    n*p≤n*q = *-monoʳ-≤ n p q p≤q

open import Data.Nat.Properties using (*-comm)
*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)


infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}   → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans {zero} {suc n} {suc p} (z<s {n}) _ = z<s {p}
<-trans {suc m} {suc n} {suc p} (s<s {m} {n} m<n) (s<s n<p) = s<s {m} {p} (<-trans {m} {n} {p} m<n n<p)
--                              ^ suc m < suc n   ^ suc n < suc p

data trichotomy (m n : ℕ) : Set where 
  forward : m < n → trichotomy m n
  eq : m ≡ n → trichotomy m n
  flipped : n < m → trichotomy m n


-- ≡suc : ∀ (m n : ℕ) → m ≡ n → (suc m) ≡ (suc n)
-- ≡suc zero n m≡n = {!   !}
-- ≡suc (suc m) n m≡n = {!   !}


<-trichotomy : ∀ ( m n : ℕ ) → trichotomy m n 
<-trichotomy zero (suc n) = forward z<s
<-trichotomy zero zero = eq refl
<-trichotomy (suc m) zero = flipped z<s
<-trichotomy (suc m) (suc n) 
    with <-trichotomy m n 
...   | forward m<n = forward (s<s {m} {n} m<n)
...   | eq m≡n = eq (cong suc m≡n)
...   | flipped n<m = flipped ( s<s {n} {m} n<m ) 

+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite
    (+-comm m p) 
  | (+-comm n p) = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)


≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-iff-< {zero} {suc n} sm≤n = z<s {n}
≤-iff-< {suc m} {suc n} ssm≤sn = s<s (≤-iff-< {m} {n} ((inv-s≤s ssm≤sn)))

inv-s<s : ∀ {m n : ℕ} → suc m < suc n → m < n
inv-s<s (s<s m<n) = m<n

≤-iff-<` : ∀ {m n : ℕ} → m < n → suc m ≤ n
≤-iff-<` {zero} {suc n} z<s = s≤s {zero} {n} z≤n
≤-iff-<` {suc m} {suc n} sm<sn = s≤s ((≤-iff-<` {m} {n} ((inv-s<s sm<sn))))

<suc : ∀ {m p : ℕ} → m < p → m < (suc p)
<suc {zero} {p} z<n = z<s
<suc {suc m} {suc p} sm<sp = s<s (( <suc {m} {p} (inv-s<s sm<sp) ))

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited {zero} {suc n} {suc (suc p)} z<s n<p = z<s
<-trans-revisited {m} {suc n} {(suc p)} m<sn sn<sp = <suc (≤-iff-< sm≤p)
 where 
    sm≤sn = ≤-iff-<` m<sn
    sn≤p = ≤-iff-<` (inv-s<s sn<sp )
    sm≤p = ≤-trans sm≤sn sn≤p  


data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc  : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)
o+e≡o (suc em) en  = suc (e+e≡e em en)


o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc zero) on = suc on
o+o≡e (suc (suc om)) on = suc (suc (o+o≡e om on))

-- o+o≡e om (suc en) = suc (o+e≡o om en)



