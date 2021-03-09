

module FormulaUnarySeq where

open import Data.Product
open import Data.Sum
open import Function
open import Data.Nat
open import Data.List
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool renaming (_∧_ to _&_; _∨_ to _∣_)
open import Data.Maybe

open import LFP
open import ListIn

infix 25 _∧_
infix 25 _∨_
infix 4 _⇒_

data Formula : Set where
  unit : Formula 
  _∧_  : Formula → Formula → Formula
  _∨_  : Formula → Formula → Formula 
  var  : Formula
  μ    : Formula →  Formula

substVar : Formula → Formula  → Formula 
substVar A unit = unit
substVar A (c ∧ c₁) = substVar A c ∧ substVar A c₁
substVar A (c ∨ c₁) = substVar A c ∨ substVar A c₁
substVar A var = A
substVar A (μ B) = μ B

data Seq : Set where
  _⇒_ : Formula → Formula → Seq

closedF : Formula → Bool
closedF unit = true
closedF (A ∧ B) = closedF A & closedF B
closedF (A ∨ B) = closedF A & closedF B
closedF var = false
closedF (μ A) = true

closedS : Seq → Bool
closedS (A  ⇒ B) = closedF A & closedF B


closed-subst : {A B : Formula} → closedF B ≡ true → closedF (substVar B A) ≡ true
closed-subst {unit} {B} p  = refl
closed-subst {A ∧ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
closed-subst {A ∨ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
closed-subst {var} {B} p = p
closed-subst {μ A} {B} p = refl

closed-1 : {a b : Bool} → a & b ≡ true → a ≡ true
closed-1 {false} {b} ()
closed-1 {true} {b} q = refl

closed-2 : {a b : Bool} → a & b ≡ true → b ≡ true
closed-2 {false} {false} ()
closed-2 {true} {false} ()
closed-2 {a} {true}  q = refl


⟦_⟧F  : (A : Formula) → (ρ : Maybe Set) →  Set
⟦ unit ⟧F ρ  = ⊤
⟦ A ∧ B ⟧F ρ  = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ 
⟦ A ∨ B ⟧F ρ  = ⟦ A ⟧F ρ  ⊎ ⟦ B ⟧F ρ
⟦ var ⟧F nothing  = ⊤ -- or must be ⊥?
⟦ var ⟧F  (just x)  = x
⟦ μ A ⟧F _  = Mu λ (X : Set) → ⟦ A ⟧F (just X)

⟦_⟧S :  Seq → Maybe Set → Set
⟦ Γ ⇒ A ⟧S ρs = ⟦ Γ ⟧F ρs → ⟦ A ⟧F ρs

wcf-eq :  {ρ₁ ρ₂ : Maybe Set}{C : Formula} → .{p : closedF C ≡ true} → ⟦ C ⟧F ρ₁ ≡ ⟦ C ⟧F ρ₂
wcf-eq {_} {_} {unit} = refl
wcf-eq {ρ₁} {ρ₂} {A ∧ B} {p} rewrite wcf-eq {ρ₁} {ρ₂} {A} {closed-1 p} | wcf-eq {ρ₁} {ρ₂} {B} {closed-2 p} = refl
wcf-eq {ρ₁} {ρ₂} {A ∨ B} {p} rewrite wcf-eq {ρ₁} {ρ₂} {A} {closed-1 p} | wcf-eq {ρ₁} {ρ₂} {B} {closed-2 p} = refl 
wcf-eq {_} {_} {var} {()}
wcf-eq {_} {_} {μ C} = refl


substEq : {ρ : Maybe Set} (A : Formula) → {C : Formula} → .{p : closedF C ≡ true} → ⟦ substVar C A  ⟧F ρ ≡ ⟦ A ⟧F (just (⟦ C ⟧F ρ))
substEq unit {p} = refl
substEq {ρ} (A ∧ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
substEq {ρ} (A ∨ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
substEq var {p} = refl
substEq (μ A) {p} = refl








