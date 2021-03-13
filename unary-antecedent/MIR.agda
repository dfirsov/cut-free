{-#  OPTIONS --type-in-type #-}

module MIR where

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
HContext = Maybe Seq -- ≈ (Seq + 1)


{-
data Maybe {a} (A : Set a) : Set a where
  just    : (x : A) → Maybe A
  nothing : Maybe A
-}


closedH : HContext → Bool
closedH (just x) = closedS x
closedH nothing = true




infix 3 _⊢_

mutual

  data _⊢_ :  HContext  → Seq → Set where
    id-axiom : ∀ {Φ : HContext}{A : Formula}
          → Φ ⊢ A ⇒ A

    unit-r : ∀ {Φ : HContext}{Γ : Formula} → Φ ⊢ Γ ⇒ unit

    ∧-r  : ∀ {Φ : HContext}{Γ : Formula}{A B : Formula}
               → Φ ⊢  Γ ⇒ A → Φ ⊢ Γ ⇒ B → Φ ⊢ Γ ⇒ A ∧ B

    ∧-l₁  : ∀ {Φ : HContext}  {A B C : Formula}
               →   Φ ⊢ A ⇒ C → Φ ⊢  A ∧ B ⇒ C
    ∧-l₂  : ∀ {Φ : HContext}  {A B C : Formula}
               →   Φ ⊢ B ⇒ C → Φ ⊢  A ∧ B ⇒ C

    ∨-r₁  : ∀ {Φ : HContext}{Γ : Formula}{A B : Formula}
               → Φ ⊢ Γ ⇒ A → Φ ⊢ Γ ⇒ A ∨ B
    ∨-r₂  : ∀ {Φ : HContext}{Γ : Formula}{A B : Formula}
               → Φ ⊢ Γ ⇒ B → Φ ⊢ Γ ⇒ A ∨ B

    ∨-l  : ∀ {Φ : HContext}{A B C : Formula}
               → Φ ⊢ A ⇒ C 
               → Φ ⊢ B ⇒ C 
               → Φ ⊢ A ∨ B ⇒ C   

    μ-r  : ∀ {Φ : HContext}{Γ : Formula}{A : Formula}
               → Φ ⊢ Γ ⇒ substVar (μ A) A
               → Φ ⊢ Γ ⇒ μ A

    μ-l  : ∀ {Φ : HContext}{A : Formula}{C : Formula}
              → just (var ⇒ C) ⊢ A ⇒ C
              → closedF C ≡ true
              → Φ ⊢ μ A ⇒ C

    hyp-use : ∀ {S : Seq} → (just S) ⊢ S -- back edge


{-
-- cut must be in proof tree for that one, p. 258
reduce : {Φ : HContext}{A B : Formula}
         → Φ ⊢ A ⇒ B
         → Φ ⊢ B ⇒ C
         → Φ ⊢ A ⇒ B
reduce id-axiom = {!!}
reduce unit-r = {!!}
reduce (∧-r d d₁) = {!!}
reduce (∧-l₁ d) = {!!}
reduce (∧-l₂ d) = {!!}
reduce (∨-r₁ d) = {!!}
reduce (∨-r₂ d) = {!!}
reduce (∨-l d d₁) = {!!}
reduce (μ-r d) = {!!}
reduce (μ-l d x) = {!!}
reduce hyp-use = {!!}
-}

substVarWeak2 : {A B C : Formula}
         → (just (var ⇒ C)) ⊢ A ⇒ B
         → {pf : closedF C ≡ true}
         → (just (var ⇒ C)) ⊢ (substVar C A) ⇒ B
substVarWeak2 {unit} d {pf} = d
substVarWeak2 {A ∧ A₁} id-axiom {pf} = ∧-r (∧-l₁ (substVarWeak2 {A = A} id-axiom {pf}) ) (∧-l₂ (substVarWeak2 id-axiom {closed-2 pf} ))
substVarWeak2 {A ∧ A₁} unit-r {pf} = unit-r
substVarWeak2 {A ∧ A₁} (∧-r d d₁) {pf} = {!!}
substVarWeak2 {A ∧ A₁} (∧-l₁ d) {pf} = {!!}
substVarWeak2 {A ∧ A₁} (∧-l₂ d) {pf} = {!!}
substVarWeak2 {A ∧ A₁} (∨-r₁ d) {pf} = {!!}
substVarWeak2 {A ∧ A₁} (∨-r₂ d) {pf} = {!!}
substVarWeak2 {A ∧ A₁} (μ-r d) {pf} = {!!}


substVarWeak2 {A ∨ A₁} d {pf} = {!!}
substVarWeak2 {var} d {pf} = {!!}
substVarWeak2 {μ A} d {pf} = {!!}


cut : {Φ : HContext}{A B C : Formula}
         → (d : Φ ⊢ A ⇒ B)
         → {pf :  closedF C ≡ true}
         → Φ ⊢ B ⇒ C
         → Φ ⊢ A ⇒ C
cut (μ-l d₁ x) {pf} unit-r = unit-r
cut (μ-l d₁ x) {pf} (∨-r₁ d)
 = ∨-r₁ (cut (μ-l d₁ x) {closed-1 pf} d)
cut (μ-l d₁ x) {pf} (∨-r₂ d)
 = ∨-r₂ (cut (μ-l d₁ x) {closed-2 pf} d)

{- excluded if d₁ has hyp-use in them -}
cut (μ-l d₁ x) {pf} (∨-l d d₂) = {!!}
cut (μ-l d₁ x) {pf} (μ-l d x₁) = {!!}
cut (μ-l d₁ x) {pf} hyp-use = {!!}
cut (μ-l d₁ x) {pf} (∧-l₁ d) = {!!}
cut (μ-l d₁ x) {pf} (∧-l₂ d) = {!!}
cut unit-r      hyp-use = {!!}
cut (∧-r d₁ d₂) hyp-use = {!!}
cut (∨-r₁ d₁)   hyp-use = {!!}
cut (∨-r₂ d₁)   hyp-use = {!!}
cut (μ-r d₁)    hyp-use = {!!}
cut hyp-use (∧-l₁ d₂) = {!!}
cut hyp-use (∧-l₂ d₂) = {!!}
cut hyp-use (∨-l d₂ d₃) = {!!}
cut hyp-use (μ-l d₂ x) = {!!}
{- / excluded if d₁ has hyp-use in them -}


-- weaken d₁, weaken d
cut (μ-r d₁) {pf} (μ-l d x) =  {!!}
cut id-axiom hyp-use = hyp-use
cut hyp-use hyp-use = id-axiom
cut hyp-use id-axiom = hyp-use
cut hyp-use unit-r = unit-r

cut hyp-use {pf} (∨-r₁ d₂) = ∨-r₁ (cut hyp-use {closed-1 pf} d₂)
cut hyp-use {pf} (∨-r₂ d₂) = ∨-r₂ (cut hyp-use {closed-2 pf} d₂)

cut d₁ id-axiom = d₁
cut d₁ unit-r = unit-r
cut d₁ {pf} (∧-r d₂ d₃) = ∧-r (cut d₁ {closed-1 pf} d₂) (cut d₁ {closed-2 pf} d₃)
cut id-axiom (∧-l₁ d₂) = ∧-l₁ d₂
cut (∧-r d₁ d₃) {pf} (∧-l₁ d₂) = cut d₁ {pf} d₂
cut (∧-l₁ d₁) {pf} d₂ = ∧-l₁ (cut d₁ {pf} d₂)
cut (∧-l₂ d₁) {pf} d₂ = ∧-l₂ (cut d₁ {pf} d₂)
cut id-axiom (μ-l d₂ x ) = μ-l d₂ x
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



