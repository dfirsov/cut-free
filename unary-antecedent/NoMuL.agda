{-#  OPTIONS --type-in-type #-}

open import Data.Empty

open import Data.Product
open import Data.Sum
open import Function
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.Any  hiding (map)
open import Data.Vec hiding (map; _++_; _∈_)
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool renaming (_∧_ to _&_; _∨_ to _∣_)
open import Data.Maybe

open import ListIn

open import FormulaUnarySeq
open import LFP


HContext : Set
HContext = ⊤

closedH : HContext → Bool
closedH _ = true


infix 3 _⊢_
data _⊢_ :  HContext  → Seq → Set where
  id-axiom : ∀ {Φ : HContext}{A : Formula}
        → Φ ⊢ A ⇒ A
        
  unit-r : ∀ {Φ : HContext}{A : Formula} → Φ ⊢ A ⇒ unit

  ∧-r  : ∀ {Φ : HContext} {C : Formula} {A B : Formula}
             → Φ ⊢  C ⇒ A → Φ ⊢  C ⇒ B → Φ ⊢  C ⇒ A ∧ B
             
  ∧-l₁  : ∀ {Φ : HContext}  {A B C : Formula}
             →   Φ ⊢ A ⇒ C → Φ ⊢  A ∧ B ⇒ C
  ∧-l₂  : ∀ {Φ : HContext}  {A B C : Formula}
             →   Φ ⊢ B ⇒ C → Φ ⊢  A ∧ B ⇒ C             
  
  ∨-r₁  : ∀ {Φ : HContext} {C : Formula} {A B : Formula}
             → Φ ⊢  C ⇒ A → Φ ⊢  C ⇒ A ∨ B
  ∨-r₂  : ∀ {Φ : HContext} {Γ : Formula} {A B : Formula}
             → Φ ⊢ Γ ⇒ B → Φ ⊢  Γ ⇒ A ∨ B
             
  ∨-l  : ∀ {Φ : HContext}{A B C : Formula}
             → Φ ⊢ A ⇒ C 
             → Φ ⊢ B ⇒ C 
             → Φ ⊢ A ∨ B ⇒ C   

  μ-r  : ∀ {Φ : HContext} {Γ : Formula} {A : Formula}
             → Φ ⊢ Γ ⇒ substVar (μ A)  A
             → Φ ⊢ Γ ⇒ μ A



cut : {Φ : HContext}{A B C : Formula}
         → Φ ⊢ A ⇒ B → Φ ⊢ B ⇒ C → Φ ⊢ A ⇒ C
cut d₁ id-axiom = d₁
cut d₁ unit-r = unit-r
cut d₁ (∧-r d₂ d₃) = ∧-r (cut d₁ d₂) (cut d₁ d₃)
cut id-axiom (∧-l₁ d₂) = ∧-l₁ d₂
cut (∧-r d₁ d₃) (∧-l₁ d₂) = cut d₁ d₂
cut (∧-l₁ d₁) d₂ = ∧-l₁ (cut d₁ d₂)
cut (∧-l₂ d₁) d₂ = ∧-l₂ (cut d₁ d₂)
cut (∨-l d₁ d₃) (∧-l₁ d₂) = ∨-l (cut d₁ (∧-l₁ d₂)) (cut d₃ (∧-l₁ d₂))
cut d₁ (μ-r d₂) = μ-r (cut d₁ d₂) 
cut (μ-r d₁) (∨-r₁ d₂) = ∨-r₁ (cut (μ-r d₁) d₂)
cut id-axiom (∧-l₂ d₂) = ∧-l₂ d₂
cut (∧-r d₁ d₃) (∧-l₂ d₂) = cut d₃ d₂
cut (∨-l d₁ d₃) (∧-l₂ d₂) = ∨-l (cut d₁ (∧-l₂ d₂)) (cut d₃ (∧-l₂ d₂))
cut id-axiom (∨-r₁ d₂) = ∨-r₁ d₂
cut unit-r (∨-r₁ d₂) = ∨-r₁ (cut unit-r d₂)
cut (∧-r d₁ d₃) (∨-r₁ d₂) = ∨-r₁ (cut (∧-r d₁ d₃) d₂)
cut (∨-r₁ d₁) (∨-r₁ d₂) = ∨-r₁ (cut (∨-r₁ d₁) d₂)
cut (∨-r₂ d₁) (∨-r₁ d₂) = ∨-r₁ (cut (∨-r₂ d₁) d₂)
cut (∨-l d₁ d₃) (∨-r₁ d₂) = ∨-l (cut d₁ (∨-r₁ d₂)) (∨-r₁ (cut d₃ d₂))
cut d₁ (∨-r₂ d₂) = ∨-r₂ (cut d₁ d₂)
cut id-axiom (∨-l d₂ d₃) = ∨-l d₂ d₃
cut (∨-r₁ d₁) (∨-l d₂ d₃) = cut d₁ d₂
cut (∨-r₂ d₁) (∨-l d₂ d₃) = cut d₁ d₃
cut (∨-l d d₂) d₁ = ∨-l (cut d d₁) (cut d₂ d₁)


