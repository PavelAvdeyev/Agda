module Logic where
  open import MyLevel
  open import MyFunction 
  open import MMLT 

  -- False proposition
  data ⊥ : Set where 

  -- True proposition
  record ⊤ : Set where 

  ⊥-elim : ∀ {α} → {A : Set α} → ⊥ → A 
  ⊥-elim ()

  ¬ : ∀ {α} → Set α → Set α 
  ¬ P = P → ⊥

  record _∧_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where 
    constructor _,'_
    field 
      fst : A
      snd : B 
  
  open _∧_ public

  data _∨_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where 
    inl : A → A ∨ B 
    inr : B → A ∨ B

  _↔_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β) 
  A ↔ B = (A → B) ∧ (B → A)

  private 
    module Logic-Rule {α β} {A : Set α} {B : Set β} where 
      contradiction : A → ¬ A → B
      contradiction a ¬a = ⊥-elim (¬a a) 

      contraposition : (A → B) → (¬ B → ¬ A) 
      contraposition = flip _∘'_

      contraposition¬ : (A → ¬ B) → (B → ¬ A) 
      contraposition¬ = flip  
  open Logic-Rule 

  private  
    module ↔-prop where       
      open MyFunction
      ref : ∀ {α} → {A : Set α} → A ↔ A → ⊤ 
      ref ab = record { } 

      sym : ∀ {α} → {A B : Set α} → A ↔ B → B ↔ A
      sym equiv = snd equiv ,' fst equiv 

      trans : ∀ {α} → {A B C : Set α} → A ↔ B → B ↔ C → A ↔ C 
      trans f s = ((fst s) ∘' (fst f)) ,' ((snd f) ∘' (snd s))  
  open ↔-prop

  private 
    module Logic-Op where 
      open MyFunction
      open MMLT 

      module DummyA {α} {A : Set α} where 
        →¬² :  A → ¬ (¬ A)
        →¬² = contradiction

        ¬³→¬ :  ¬ (¬ (¬ A)) → ¬ A
        ¬³→¬ ¬³a = ¬³a ∘' →¬² 

        ¬²→ :  ¬ (¬ A) → A 
        ¬²→ ¬²a = {!!} --⊥-elim (¬²a ({!!})) --contradiction {!(¬ ¬²a)!} ¬²a
      open DummyA

      module DummyAB {α} {A B : Set α} where   
        ∧-comm : A ∧ B → B ∧ A 
        ∧-comm ab =  (snd ab) ,' (fst ab) 

        ∨-comm : A ∨ B → B ∨ A 
        ∨-comm (inr y) = inl y 
        ∨-comm (inl y) = inr y 

        ↔-comm : A ↔ B → B ↔ A
        ↔-comm as = snd as ,' fst as 

        ∧-morg : ¬ (A ∧ B) → (¬ A) ∨ (¬ B) 
        ∧-morg as = {!,'!} 
  
        ∨-morg : ¬ (A ∨ B) → (¬ A) ∧ (¬ B) 
        ∨-morg as = ⊥-elim (as (inl {!!}))  

      open DummyAB 

--      ∨-morg : ∀ {α} → {A B : Set α} → ¬ (A ∨ B) → (¬ A) ∧ (¬ B) 
--      ∨-morg {A = a} as = ⊥-elim (as (inl {!!}))  


      module DummyABC {α} {A B C : Set α} where   
        ∧-assoc : (A ∧ B) ∧ C → A ∧ (B ∧ C) 
        ∧-assoc as = fst (fst as) ,' (snd (fst as) ,' snd as) 

        ∨-assoc : (A ∨ B) ∨ C → A ∨ (B ∨ C) 
        ∨-assoc as with as 
        ∨-assoc as | (inl r) with r
        ∨-assoc as | (inl r) | (inl k) = inl k 
        ∨-assoc as | (inl r) | (inr k) = inr (inl k) 
        ∨-assoc as | (inr k) = inr (inr k)  

        ∧-dist : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) 
        ∧-dist as with (snd as) 
        ∧-dist as | (inl k) = inl (fst as ,' k) 
        ∧-dist as | (inr k) = inr (fst as ,' k) 

        ∨-dist : A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C) 
        ∨-dist (inr bs) = inr (fst bs) ,' inr (snd bs) 
        ∨-dist (inl bs) = inl bs ,' inl bs 
      open DummyABC
  open Logic-Op 

 

-- What better (A ∧ B → B ∧ A) or (A ∧ B ≡ B ∧ A) ? 
-- What better A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) OR A ∧ (B ∨ C) ≡ (A ∧ B) ∨ (A ∧ C) 
-- Why explisit argumets when its in module
-- ¬²→ ? 

  ×↔∧ : ∀ {α β} {A : Set α} {B : Set β} → (A × B) ↔ (A ∧ B) 
  ×↔∧ = {!!} --(λ z → projl z ,' projr z) ,' (λ z → fst z , snd z)
