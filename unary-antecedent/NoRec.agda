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


infix 3 _⊢c_
data _⊢c_ :  HContext  → Seq → Set where
  id-axiom : ∀ {Φ : HContext}{A : Formula}
        → Φ ⊢c A ⇒ A
        
  unit-r : ∀ {Φ : HContext}{A : Formula} → Φ ⊢c A ⇒ unit

  ∧-r  : ∀ {Φ : HContext} {C : Formula} {A B : Formula}
             → Φ ⊢c  C ⇒ A → Φ ⊢c  C ⇒ B → Φ ⊢c  C ⇒ A ∧ B
             
  ∧-l₁  : ∀ {Φ : HContext}  {A B C : Formula}
             →   Φ ⊢c A ⇒ C → Φ ⊢c  A ∧ B ⇒ C
  ∧-l₂  : ∀ {Φ : HContext}  {A B C : Formula}
             →   Φ ⊢c B ⇒ C → Φ ⊢c  A ∧ B ⇒ C             
  
  ∨-r₁  : ∀ {Φ : HContext} {C : Formula} {A B : Formula}
             → Φ ⊢c  C ⇒ A → Φ ⊢c  C ⇒ A ∨ B
  ∨-r₂  : ∀ {Φ : HContext} {Γ : Formula} {A B : Formula}
             → Φ ⊢c Γ ⇒ B → Φ ⊢c  Γ ⇒ A ∨ B
             
  ∨-l  : ∀ {Φ : HContext}{A B C : Formula}
             → Φ ⊢c A ⇒ C 
             → Φ ⊢c B ⇒ C 
             → Φ ⊢c A ∨ B ⇒ C   

  μ-r  : ∀ {Φ : HContext} {Γ : Formula} {A : Formula}
             → Φ ⊢c Γ ⇒ substVar (μ A)  A
             → Φ ⊢c Γ ⇒ μ A
             
  μ-l  : ∀  {A : Formula}{C : Formula}
            → tt ⊢c A ⇒ C
            → closedF C ≡ true
            → tt ⊢c μ A  ⇒ C


substVarWeak : {Φ : HContext}{A B C : Formula}
         → Φ ⊢c A ⇒ C → {pf : closedF C ≡ true} → Φ ⊢c (substVar (μ B) A) ⇒ C
substVarWeak {A = unit} d = d
substVarWeak {A = A ∧ A₁} id-axiom {pf} = ∧-r (∧-l₁ (substVarWeak {A = A} id-axiom {closed-1 pf}) ) (∧-l₂ (substVarWeak id-axiom {closed-2 pf} ))
substVarWeak {A = A ∧ A₁} unit-r = unit-r
substVarWeak {A = A ∧ A₁} (∧-r d d₁) {pf} = ∧-r (substVarWeak d {closed-1 pf}) (substVarWeak d₁ {closed-2 pf})
substVarWeak {A = A ∧ A₁} (∧-l₁ d) {pf} = ∧-l₁ (substVarWeak d {pf})
substVarWeak {A = A ∧ A₁} (∧-l₂ d) {pf} = ∧-l₂ (substVarWeak d {pf}) 
substVarWeak {A = A ∧ A₁} (∨-r₁ d) {pf} = ∨-r₁ (substVarWeak d {closed-1 pf})
substVarWeak {A = A ∧ A₁} (∨-r₂ d) {pf} = ∨-r₂ (substVarWeak d {closed-2 pf})
substVarWeak {A = A ∧ A₁} (μ-r {A = A'} d) {pf} = μ-r (substVarWeak d {closed-subst {A'} refl})
substVarWeak {A = A ∨ A₁} id-axiom {pf} = ∨-l (∨-r₁ (substVarWeak id-axiom {closed-1 pf})) (∨-r₂ (substVarWeak id-axiom {closed-2 pf}))
substVarWeak {A = A ∨ A₁} unit-r = unit-r
substVarWeak {A = A ∨ A₁} (∧-r d d₁) {pf} = ∧-r (substVarWeak d {closed-1 pf}) (substVarWeak d₁ {closed-2 pf})
substVarWeak {A = A ∨ A₁} (∨-r₁ d) {pf} = ∨-r₁ (substVarWeak d {closed-1 pf})
substVarWeak {A = A ∨ A₁} (∨-r₂ d) {pf} = ∨-r₂ (substVarWeak d {closed-2 pf})
substVarWeak {A = A ∨ A₁} (∨-l d d₁) {pf} = ∨-l (substVarWeak d {pf}) (substVarWeak d₁ {pf})
substVarWeak {A = A ∨ A₁} (μ-r {A = A'} d) {pf} = μ-r (substVarWeak d {closed-subst {A'} refl})
substVarWeak {A = var} id-axiom {()}
substVarWeak {A = var} unit-r {pf} = unit-r
substVarWeak {A = var} (∧-r d d₁) {pf} = ∧-r (substVarWeak d {closed-1 pf}) (substVarWeak d₁ {closed-2 pf})
substVarWeak {A = var} (∨-r₁ d) {pf} = ∨-r₁ (substVarWeak d {closed-1 pf})
substVarWeak {A = var} (∨-r₂ d) {pf} = ∨-r₂ (substVarWeak d {closed-2 pf})
substVarWeak {A = var} (μ-r {A = A} d) {pf} = μ-r (substVarWeak d {closed-subst {A} refl})
substVarWeak {A = μ A} d = d

{- weaker requirement  that closedF C in cut definition -}
WeakL : {Φ : HContext}{A B : Formula}
         → Φ ⊢c A ⇒ B → Formula → Bool
WeakL id-axiom C = true
WeakL unit-r C = true
WeakL (∧-r d d₁) C = WeakL d C & WeakL d₁ C
WeakL (∧-l₁ d) C = WeakL d C
WeakL (∧-l₂ d) C = WeakL d C
WeakL (∨-r₁ d) C = WeakL d C
WeakL (∨-r₂ d) C = WeakL d C
WeakL (∨-l d d₁) C = WeakL d C & WeakL d₁ C
WeakL (μ-r d) C = WeakL d C
WeakL (μ-l d x) C = closedF C & WeakL d C

{-
closedF C = true can be put in different places

 1/ it might restrict the semantic brackets
 2/ or it might restrict the tree constructions

-}

cut : {Φ : HContext}{A B C : Formula}
         → (d : Φ ⊢c A ⇒ B)
         → {pf :  closedF C ≡ true}
         → Φ ⊢c B ⇒ C
         → Φ ⊢c A ⇒ C
cut d₁ id-axiom = d₁
cut d₁ unit-r = unit-r
cut d₁ {pf} (∧-r d₂ d₃) = ∧-r (cut d₁ {closed-1 pf} d₂) (cut d₁ {closed-2 pf} d₃)
cut id-axiom (∧-l₁ d₂) = ∧-l₁ d₂
cut (∧-r d₁ d₃) {pf} (∧-l₁ d₂) = cut d₁ {pf} d₂
cut (∧-l₁ d₁) {pf} d₂ = ∧-l₁ (cut d₁ {pf} d₂)
cut (∧-l₂ d₁) {pf} d₂ = ∧-l₂ (cut d₁ {pf} d₂)
cut  (μ-l d₁ x ) {pf} d = μ-l (cut d₁ {closed-2 pf} d) pf
cut id-axiom (μ-l d₂ x ) = μ-l d₂ x 
cut (μ-r d₁) {pf} (μ-l d x ) = cut d₁ {pf} (substVarWeak d {x})
cut {_} {A} {B} {C} d₁ {pf} (μ-r {A = A'} d₂) = μ-r (cut d₁ {closed-subst {A'} {μ _} refl} d₂) 
cut (μ-r d₁) {pf} (∨-r₁ d₂) = ∨-r₁ (cut (μ-r d₁) {closed-1 pf} d₂)
cut id-axiom (∧-l₂ d₂) = ∧-l₂ d₂
cut (∧-r d₁ d₃) {pf} (∧-l₂ d₂) = cut d₃ {closed-2 pf} d₂
cut id-axiom (∨-r₁ d₂) = ∨-r₁ d₂
cut unit-r {pf} (∨-r₁ d₂) = ∨-r₁ (cut unit-r {closed-1 pf } d₂)
cut (∧-r d₁ d₃) {pf} (∨-r₁ d₂) = ∨-r₁ (cut (∧-r d₁ d₃) {closed-1 pf} d₂)
cut (∨-r₁ d₁) {pf} (∨-r₁ d₂) = ∨-r₁ (cut (∨-r₁ d₁) {closed-1 pf} d₂)
cut (∨-r₂ d₁) {pf} (∨-r₁ d₂) = ∨-r₁ (cut (∨-r₂ d₁) {closed-1 pf} d₂)
cut d₁ {pf} (∨-r₂ d₂) = ∨-r₂ (cut d₁ {closed-2 pf} d₂)
cut id-axiom (∨-l d₂ d₃) = ∨-l d₂ d₃
cut (∨-r₁ d₁) {pf} (∨-l d₂ d₃) = cut d₁ {pf} d₂
cut (∨-r₂ d₁) {pf} (∨-l d₂ d₃) = cut d₁ {pf} d₃
cut (∨-l d d₂) {pf} d₁ = ∨-l (cut d {pf} d₁) (cut d₂ {closed-2 pf} d₁)


