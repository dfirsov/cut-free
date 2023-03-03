{-#  OPTIONS --type-in-type #-}

open import Data.Empty


open import Data.Product
open import Data.Sum
open import Function
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any  hiding (map)
open import Data.Vec 
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool renaming (_∧_ to _&_; _∨_ to _∣_)
open import Data.Maybe

open import ListIn
open import Formula
open import LFP

infix 3 _⊢_


HContext : Set
HContext = ⊤
data _⊢_ :  HContext  → Seq → Set where
  id-axiom : ∀ {Φ : HContext}{Γ : Context}{A : Formula}
        → Φ ⊢ A ∷ Γ ⇒ A
       
  unit-r : ∀ {Φ : HContext}{Γ : Context} → Φ ⊢ Γ ⇒ unit
  unit-l : ∀ {Φ : HContext}{Γ : Context}{C : Formula}
   → Φ ⊢   Γ ⇒ C → Φ ⊢  unit ∷ Γ ⇒ C

  ∧-r  : ∀ {Φ : HContext} {Γ : Context} {A B : Formula}
             → Φ ⊢  Γ ⇒ A → Φ ⊢  Γ ⇒ B → Φ ⊢  Γ ⇒ A ∧ B     
  ∧-l  : ∀ {Φ : HContext} {Γ : Context} {A B C : Formula}
             →   Φ ⊢  A ∷ B ∷ Γ ⇒ C → Φ ⊢  A ∧ B ∷ Γ ⇒ C

  
  ∨-r₁  : ∀ {Φ : HContext} {Γ : Context} {A B : Formula}
             → Φ ⊢  Γ ⇒ A → Φ ⊢  Γ ⇒ A ∨ B
  ∨-r₂  : ∀ {Φ : HContext} {Γ : Context} {A B : Formula}
             → Φ ⊢ Γ ⇒ B → Φ ⊢  Γ ⇒ A ∨ B
  ∨-l  : ∀ {Φ : HContext} {Γ : Context} {A B C : Formula}
             → Φ ⊢ A ∷ Γ ⇒ C 
             → Φ ⊢ B ∷ Γ ⇒ C 
             → Φ ⊢ A ∨ B ∷ Γ ⇒ C   

  μ-r  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}
             → Φ ⊢ Γ ⇒ substVar (μ A)  A
             → Φ ⊢ Γ ⇒ μ A
             
  μ-l  : ∀ {Γ : Context} {A : Formula}{C : Formula}
            → tt ⊢ A ∷ Γ ⇒ C
            → closedF C ≡ true
            → closedC Γ ≡ true 
            → tt ⊢ μ A  ∷  Γ ⇒ C
{-            
  hyp-use : ∀ {S : Seq } → (just S) ⊢ S
-}

  contr  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → Φ ⊢ A ∷ A ∷ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C

  weakn  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → Φ ⊢ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C

  exchng  : ∀ {Φ : HContext} {Γ Γ' : Context} {A : Formula}{C : Formula}
            → A ∈ Γ , Γ'
            → Φ ⊢ A ∷ Γ' ⇒ C   
            → Φ ⊢ Γ ⇒ C         


⟦_⟧H :  HContext → Set
⟦ _ ⟧H  = ⊤


⟦_⟧ : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ (Γ ⇒ A) → (ρ : Maybe Set)
  → ⟦ Γ ⟧C ρ → ⟦ A ⟧F ρ
⟦ contr d ⟧ ρ v = ⟦ d ⟧ ρ  (proj₁ v , proj₁ v , proj₂ v)
⟦ id-axiom ⟧ ρ v = proj₁ v
⟦ unit-r ⟧ ρ v = tt
⟦ unit-l d ⟧ ρ v = ⟦ d ⟧ ρ (proj₂ v)
⟦ ∧-r d d₁ ⟧ ρ v = ⟦ d ⟧ ρ v , ⟦ d₁ ⟧ ρ v
⟦ ∧-l d ⟧ ρ v = ⟦ d ⟧ ρ  (proj₁ (proj₁ v) , proj₂ (proj₁ v) , proj₂ v)
⟦ ∨-r₁ d ⟧ ρ v = inj₁ (⟦ d ⟧ ρ v) 
⟦ ∨-r₂ d ⟧ ρ v = inj₂ (⟦ d ⟧ ρ v)
⟦ ∨-l d d₁ ⟧ ρ (inj₁ a , Γ) = ⟦ d ⟧ ρ (a , Γ)
⟦ ∨-l d d₁ ⟧ ρ (inj₂ b , Γ) = ⟦ d₁ ⟧ ρ (b , Γ)
⟦ μ-r {A = A} d ⟧ ρ v = In (subst id  (substEq A {μ A} {refl}) (⟦ d ⟧ ρ v) )
⟦ μ-l {Γ = Γ} {C = C} d x x₁ ⟧ ρ (IN x₂ x₃ , proj₄) = subst id (wcf-eq {_} {_} {C} {x}) (⟦ d ⟧  _ (x₃ , subst id (wcc-eq {_} {_} {Γ} {x₁}) proj₄))
⟦ weakn d ⟧ ρ v = ⟦ d ⟧  ρ (proj₂ v)
⟦ exchng  {Γ = Γ}{Γ' = Γ'} {A = A} p c ⟧ ρ v = ⟦ c ⟧ ρ (f-lemm  {ρ}  {A} _ _ p v , G-lemm  {ρ}  {A} _ _ p v)



