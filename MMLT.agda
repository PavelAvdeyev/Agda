module MMLT where 
  open import MyLevel

  infix 4 _≡_ 
  data _≡_ {α} {A : Set α} (x : A) : A → Set α where
    refl : x ≡ x 

  record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where 
    constructor _,_
    field 
      projl : A 
      projr : B projl 

  open Σ public 

  {-# BUILTIN EQUALITY _≡_ #-} 
  {-# BUILTIN REFL refl #-} 

  _×_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β) 
  A × B = Σ A (λ _ → B) 

--  ×↔∧ : ∀ {α β} {A : Set α} {B : Set β} → (A × B) ↔ (A ∧ B) 
--  ×↔∧ = (λ z → projl z ,' projr z) ,' (λ z → fst z , snd z)

  module ≡-Prop where
    private
      module DummyA {α} {A : Set α} where
        
        sym : {x y : A} → x ≡ y → y ≡ x 
        sym refl = refl 

        trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z 
        trans refl refl = refl 

        subst : ∀ {γ} {P : A → Set γ} {x y} → x ≡ y → P x → P y 
        subst refl p = p 

    private 
      module DummyAB {α β} {A : Set α} {B : Set β} where 
        cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
        cong f refl = refl 

        subst₂ : ∀ {γ} {P : A → B → Set γ} {x y u v} → x ≡ y → u ≡ v → P x u → P y v 
        subst₂ refl refl p = p

    private 
      module DummyABC {α β γ} {A : Set α} {B : Set β} {C : Set γ} where 
        cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v 
        cong₂ f refl refl = refl

    open DummyA public 
    open DummyAB public
    open DummyABC public

