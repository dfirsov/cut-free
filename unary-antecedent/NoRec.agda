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
  μ-l  : ∀ {Γ : Formula} {A : Formula}{C : Formula}
            → tt ⊢ A ⇒ C
            → closedF C ≡ true
            → closedF Γ ≡ true 
            → tt ⊢ μ A  ⇒ C



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
  μ-l  : ∀ {Γ : Formula} {A : Formula}{C : Formula}
            → tt ⊢ A ⇒ C
            → closedF C ≡ true
            → closedF Γ ≡ true 
            → tt ⊢c μ A  ⇒ C
  cut : {Φ : HContext}{A B C : Formula}
         → Φ ⊢c A ⇒ B
         → Φ ⊢c B ⇒ C
         → Φ ⊢c A ⇒ C
         


⟦_⟧ : {Φ : HContext}{Γ : Formula}{A : Formula} → Φ ⊢ (Γ ⇒ A) → (ρ : Maybe Set)
  → ⟦ Γ ⟧F ρ → ⟦ A ⟧F ρ
⟦ id-axiom ⟧ ρ v = v
⟦ unit-r ⟧ ρ v = tt
⟦ ∧-r d d₁ ⟧ ρ v = ⟦ d ⟧ ρ v , ⟦ d₁ ⟧ ρ v
⟦ ∧-l₁ d ⟧ ρ v = ⟦ d ⟧ ρ  (proj₁ v)
⟦ ∧-l₂ d ⟧ ρ v = ⟦ d ⟧ ρ  (proj₂ v)
⟦ ∨-r₁ d ⟧ ρ v = inj₁ (⟦ d ⟧ ρ v)
⟦ ∨-r₂ d ⟧ ρ v = inj₂ (⟦ d ⟧ ρ v)
⟦ ∨-l d₁ d₂ ⟧ ρ (inj₁ x) = ⟦ d₁ ⟧ ρ x
⟦ ∨-l d₁ d₂ ⟧ ρ (inj₂ y) = ⟦ d₂ ⟧ ρ y
⟦ μ-r {A = A} d ⟧ ρ v = In (subst id  (substEq A {μ A} {refl}) (⟦ d ⟧ ρ v) )
⟦ μ-l {Γ} {C = C} d x x₁ ⟧ ρ (IN x₂ x₃) = subst id (wcf-eq {_} {_} {C}{x} ) (⟦ d ⟧  _ x₃)



BoolRaw : Formula
BoolRaw = unit ∨ unit

𝔹 : Set
𝔹 = ⟦ BoolRaw ⟧F nothing

f : 𝔹
f = inj₁ tt

t : 𝔹
t = inj₂ tt

not𝔹-F : tt ⊢ BoolRaw ⇒ BoolRaw
not𝔹-F = ∨-l (∨-r₂  unit-r) (∨-r₁ unit-r)

not𝔹 : 𝔹 → 𝔹
not𝔹 b = ⟦ not𝔹-F ⟧ nothing b


not𝔹-l₁ : not𝔹 t ≡ f
not𝔹-l₁ = refl

not𝔹-l₂ : not𝔹 f ≡ t
not𝔹-l₂ = refl

{-



1/ cut-elimination

   ● unary antecedent
     ∘ no-rec
     ∘ single rec
     ∘ mult. ind. rec
     ∘ mult. dep. rec

   ● mult antecedent
     ∘ no-rec
     ∘ single rec
     ∘ mult. ind. rec
     ∘ mult. dep. rec


2/ Comparison: unary-antecedent vs. mult-antecedent in each rec. case



Y, A1, ..., An -> C


Delta1 ->  A1  ... Deltan -> An                 Lambda, C -> D
-----------------------------------------
  Y, Delta1, Deltan, Lambda -> D
               
-}
