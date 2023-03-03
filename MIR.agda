{-#  OPTIONS --type-in-type #-}

module MIR where

open import Data.Empty

open import Data.Product
open import Data.Sum
open import Function
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any  hiding (map)
open import Data.Vec hiding (_++_)
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool renaming (_∧_ to _&_; _∨_ to _∣_)
open import Data.Maybe

open import ListIn
open import Formula
open import LFP

HContext : Set
HContext = Maybe Seq

closedH : HContext → Bool
closedH (just x) = closedS x
closedH nothing = true

closedH-1 : {y : Context}{x : Formula} → (g : HContext) → closedH (just (y ⇒ x)) ≡ true
 → closedC y ≡ true
closedH-1 {y} {x} g p with closedF x | closedC y
closedH-1 {y} {x} g () | false | false
closedH-1 {y} {x} g () | true  | false
closedH-1 {y} {x} g p  | z     | true = refl

closedH-2 : {y : Context}{x : Formula} → (g : HContext) → closedH (just (y ⇒ x)) ≡ true
 → closedF x ≡ true
closedH-2 {y} {x} g p with closedF x 
closedH-2 {y} {x} g () | false 
closedH-2 {y} {x} g p  | true  = refl


infix 3 _⊢_

data _⊢_ :  HContext  → Seq → Set where
  id-axiom : ∀ {Φ : HContext}{Γ : Context}{A : Formula}
        → Φ ⊢ A ∷ Γ ⇒ A
       
  unit-r : ∀ {Φ : HContext}{Γ : Context} → Φ ⊢ Γ ⇒ unit
  unit-l : ∀ {Φ : HContext}{Γ : Context}{C : Formula}
    → Φ ⊢ Γ ⇒ C → Φ ⊢ unit ∷ Γ ⇒ C

  ∧-r  : ∀ {Φ : HContext}{Γ : Context}{A B : Formula}
             → Φ ⊢  Γ ⇒ A → Φ ⊢ Γ ⇒ B → Φ ⊢ Γ ⇒ A ∧ B     
  ∧-l  : ∀ {Φ : HContext}{Γ : Context}{A B C : Formula}
             → Φ ⊢  A ∷ B ∷ Γ ⇒ C → Φ ⊢ A ∧ B ∷ Γ ⇒ C
  
  ∨-r₁  : ∀ {Φ : HContext}{Γ : Context}{A B : Formula}
             → Φ ⊢ Γ ⇒ A → Φ ⊢ Γ ⇒ A ∨ B
  ∨-r₂  : ∀ {Φ : HContext}{Γ : Context}{A B : Formula}
             → Φ ⊢ Γ ⇒ B → Φ ⊢ Γ ⇒ A ∨ B
  ∨-l  : ∀ {Φ : HContext}{Γ : Context}{A B C : Formula}
             → Φ ⊢ A ∷ Γ ⇒ C 
             → Φ ⊢ B ∷ Γ ⇒ C 
             → Φ ⊢ A ∨ B ∷ Γ ⇒ C   

  μ-r  : ∀ {Φ : HContext}{Γ : Context}{A : Formula}
             → Φ ⊢ Γ ⇒ substVar (μ A) A
             → Φ ⊢ Γ ⇒ μ A

  μ-l  : ∀ {Γ : Context}{A : Formula}{C : Formula}{Φ : HContext}
            → just (var ∷ Γ ⇒ C) ⊢ A ∷  Γ ⇒ C
            → closedF C ≡ true -- can remove?
            → closedC Γ ≡ true 
            → Φ ⊢ μ A ∷ Γ ⇒ C -- in SingleRec this line is: nothing ⊢ μ A  ∷  Γ ⇒ C

  hyp-use : ∀ {S : Seq} → (just S) ⊢ S

  weakn  : ∀ {Φ : HContext}{Γ : Context}{A : Formula}{C : Formula}
            → Φ ⊢ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C

  exchng  : ∀ {Φ : HContext}{Γ Γ' : Context}{A : Formula}{C : Formula}
            → A ∈ Γ , Γ'
            → Φ ⊢ A ∷ Γ' ⇒ C   
            → Φ ⊢ Γ ⇒ C


⟦_⟧H :  HContext → Maybe Set → Set
⟦ nothing ⟧H ρs = ⊤
⟦ just S ⟧H ρs  = ⟦ S ⟧S ρs 


⟦_⟧ : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ (Γ ⇒ A) → (ρ : Maybe Set)
 → ⟦ Φ ⟧H ρ → ⟦ Γ ⟧C ρ → ⟦ A ⟧F ρ
⟦ id-axiom ⟧ ρ v (x , _) = x
⟦ unit-r ⟧ ρ v _ =  tt
⟦ unit-l c ⟧ ρ v = λ { (a , b) → ⟦ c ⟧ ρ v b  }
⟦ ∧-r A B ⟧ ρ v = λ φ → ⟦ A ⟧ ρ v φ ,  ⟦ B ⟧ ρ v φ
⟦ ∧-l A ⟧ ρ v ((a , b) , c) = ⟦ A ⟧ ρ v (a , b , c )
⟦ ∨-r₁ {A = A} c ⟧ ρ v g = inj₁ (⟦ c ⟧ ρ v g)
⟦ ∨-r₂ {B = B} c ⟧ ρ v g = inj₂ (⟦ c ⟧ ρ v g)
⟦ ∨-l {A = A} {B} {_} a b ⟧ ρ v (x , g) = [_,_] (λ x → ⟦ a ⟧ ρ v (x , g)) ((λ x → ⟦ b ⟧ ρ v (x , g)))  x
⟦ μ-r {A = A} c ⟧ ρ v = λ xs → In (subst id (substEq A {μ A} {refl}) (⟦ c ⟧ ρ v xs))
⟦ μ-l {Γ = Γ} {A =  A} {C = C} c a  z ⟧ ρ v
  =  uncurry (Fold λ Y rf rv w → subst id (wcf-eq {_} {_} {C} {a}) (⟦ c ⟧ (just Y) (λ q → subst id (wcf-eq {_} {_} {C} {a}) (rf (proj₁ q) w)) (rv , subst id (wcc-eq {ρ} {just Y} {Γ} {z}) w)))  
⟦ hyp-use  ⟧ ρ a  = a
⟦ weakn c ⟧ ρ v = λ { (a , g) → ⟦ c ⟧ ρ v g }
⟦ exchng  {Γ = Γ}{Γ' = Γ'} {A = A} p c ⟧ ρ v q =  ⟦ c ⟧ ρ v  (f-lemm  {ρ}  {A} _ _ p q , G-lemm  {ρ}  {A} _ _ p q)  


