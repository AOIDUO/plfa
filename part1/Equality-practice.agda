module plfa.part1.Equality-practice where


data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  
  
infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym {A} {x} {y} (refl) = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl  =  refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎  =  refl

open ≡-Reasoning



-- {-# BUILTIN NATURAL ℕ #-}
-- _ = 2 ≡⟨⟩ 2
-- type  (x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎) : x ≡ z
-- type x : x
-- type x ≡⟨ x≡y ⟩ y : y

trans′ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
  
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)






postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

-- ≤-Reasoning

  
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
  
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {m} → m ≤ m
≤-refl {zero} = z≤n
≤-refl {suc m} = s≤s ≤-refl

module ≤-Reasoning where
      
  infix  1 ≤begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤∎

  ≤begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  ≤begin x≤y  =  x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y  =  x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z  = ≤-trans x≤y y≤z

  _≤∎ : ∀ (x : ℕ) → x ≤ x
  x ≤∎  =  ≤-refl
open ≤-Reasoning

≤-trans` : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans` {m} {n} {p} m≤n n≤p = ≤begin 
    m 
  ≤⟨ m≤n ⟩
    n
  ≤⟨ n≤p ⟩
    p
  ≤∎