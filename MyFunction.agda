module MyFunction where 
  open import MyLevel 

  infixl 0 _$_
  _$_ : ∀ {α β} → {A : Set α} → {B : A → Set β} → (f : (x : A) → B x) → ((x : A) → B x) 
  f $ x = f x 

  infixl 0 _$'_ 
  _$'_ : ∀ {α β} → {A : Set α} → {B : Set β} → (A → B) → (A → B) 
  f $' x = f $ x

  _∘_ : ∀ {α β γ} → {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ} → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  _∘'_ : ∀ {α β γ} → {A : Set α} {B : Set β} {C : Set γ} → (B → C) → (A → B) → (A → C) 
  f ∘' g = f ∘ g

  flip : ∀ {α β γ} → {A : Set α} {B : Set β} {C : A → B → Set γ} → ((x : A) → (y : B) → C x y) → ((y : B) → (x : A) → C x y) 
  flip f x y = f y x

  id : ∀ {α} {A : Set α} → A → A 
  id x = x

  const : ∀ {α β} → {A : Set α} {B : Set β} → (A → B → A)
  const a b = a

