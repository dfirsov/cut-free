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
    cut-hyp-lflip : ∀ {Φ : HContext}{A B C : Formula}
          → (d₁ : Φ ⊢ A ⇒ B)
          → (d₂ : nothing ⊢ B ⇒ C)
          → (if (concOfμ-l d₁) then (concOfRight? d₂)  else false) ≡ true
          → Φ ⊢ A ⇒ C
-}

    cut-!hyp : ∀ {Φ : HContext}{A B C : Formula}
          → (d₁ : Φ ⊢ A ⇒ B)
          → (d₂ : Φ ⊢ B ⇒ C)
          → (hyp-used? d₁ ≡ false) × (hyp-used? d₂ ≡ false)
          → Φ ⊢ A ⇒ C

   -- TODO: cut-hyp-right
 {-
  concOfμ-l : {Φ : HContext}{A B : Formula}(d : Φ ⊢ A ⇒ B) → Bool
  concOfμ-l id-axiom = false
  concOfμ-l unit-r = false
  concOfμ-l (∧-r d d₁) = false
  concOfμ-l (∧-l₁ d) = false
  concOfμ-l (∧-l₂ d) = false
  concOfμ-l (∨-r₁ d) = false
  concOfμ-l (∨-r₂ d) = false
  concOfμ-l (∨-l d d₁) = false
  concOfμ-l (μ-r d) = false
  concOfμ-l (μ-l d x) = true
  concOfμ-l hyp-use = false
  concOfμ-l (cut-hyp-lflip d d₁ x) = false
  concOfμ-l (cut-!hyp d d₁ x) = false
-}
  hyp-used? : {Φ : HContext}{A B : Formula}(d : Φ ⊢ A ⇒ B) → Bool
  hyp-used? unit-r     = false
  hyp-used? (∧-r d d₁) = false
  hyp-used? (∧-l₁ d)   = false
  hyp-used? (∧-l₂ d)   = false
  hyp-used? (∨-r₁ d)   = false
  hyp-used? (∨-r₂ d)   = false
  hyp-used? (∨-l d d₁) = false
  hyp-used? (μ-r d)    = false
  hyp-used? (μ-l d x)  = false
  hyp-used? hyp-use    = true
  hyp-used? (cut-!hyp d d₁ p ) = false
  hyp-used? id-axiom   = false
{-
  concOfRight? : {Φ : HContext}{A B : Formula}(d : Φ ⊢ A ⇒ B) → Bool
  concOfRight? unit-r       = true
  concOfRight? (∧-r d d₁)   = true
  concOfRight? (∧-l₁ d)     = false
  concOfRight? (∧-l₂ d)     = false
  concOfRight? (∨-r₁ d)     = true
  concOfRight? (∨-r₂ d)     = true
  concOfRight? (∨-l d d₁)   = false
  concOfRight? (μ-r d)      = true
  concOfRight? (μ-l d x)    = false
  concOfRight? hyp-use      = false 
  concOfRight? (cut-hyp-lflip d d₁ p ) = false
  concOfRight? (cut-!hyp d d₁ p ) = false   
  concOfRight? id-axiom     = false 
-}


cut-elim : {Φ : HContext}{A B : Formula} → (Φ ⊢ A ⇒ B) → (Φ ⊢ A ⇒ B)

cut-elim (cut-!hyp id-axiom d₁ x) = d₁
cut-elim (cut-!hyp unit-r d₁ x) = {!!}
cut-elim (cut-!hyp (∧-r d d₂) d₁ x) = {!!}
cut-elim (cut-!hyp (∧-l₁ d) d₁ x) = {!!}
cut-elim (cut-!hyp (∧-l₂ d) d₁ x) = {!!}
cut-elim (cut-!hyp (∨-r₁ d) d₁ x) = {!!}
cut-elim (cut-!hyp (∨-r₂ d) d₁ x) = {!!}
cut-elim (cut-!hyp (∨-l d d₂) d₁ x) = {!!}
cut-elim (cut-!hyp (μ-r d) d₁ x) = {!!}
cut-elim (cut-!hyp (μ-l d x₁) d₁ x) = {!!}
cut-elim (cut-!hyp hyp-use d₁ x) = {!!}
cut-elim (cut-!hyp (cut-!hyp d d₂ x₁) d₁ x) = {!!}

cut-elim id-axiom = {!!}
cut-elim unit-r = {!!}
cut-elim (∧-r d d₁) = {!!}
cut-elim (∧-l₁ d) = {!!}
cut-elim (∧-l₂ d) = {!!}
cut-elim (∨-r₁ d) = {!!}
cut-elim (∨-r₂ d) = {!!}
cut-elim (∨-l d d₁) = {!!}
cut-elim (μ-r d) = {!!}
cut-elim (μ-l d x) = {!!}
cut-elim hyp-use = {!!}



{-

{- false cases -}
cut-elim (cut (∧-l₁ d) id-axiom x) = {!!}
cut-elim (cut (∧-l₁ d) (μ-r d₁) x) = {!!}
cut-elim (cut (∧-l₁ d) (cut d₁ d₂ x₁) x) = {!!}
cut-elim (cut (∧-l₁ d) (∧-l₁ d₁) x) = {!!}
cut-elim (cut (∧-l₁ d) (μ-l d₁ x₁) x) = {!!}
cut-elim (cut (∧-l₁ d) (∨-l d₁ d₂) x) = {!!}
cut-elim (cut (∧-l₁ d) (∧-l₂ d₁) x) = {!!}

cut-elim (cut (∧-l₂ d) d₁ x) = {!!}
cut-elim (cut (∨-r₂ d) d₁ x) = {!!}
cut-elim (cut (∨-l d d₂) d₁ x) = {!!}
cut-elim (cut (μ-l d x₁) d₁ x) = {!!}

{-false cases-}
cut-elim (cut hyp-use d₁ x) = {!!}
cut-elim (cut (cut d d₂ x₁) d₁ x) = {!!}
cut-elim (cut id-axiom d₁ x) = {!!}
cut-elim (cut unit-r d₁ x) = {!!}
cut-elim (cut (∧-r d d₂) d₁ x) = {!!}
cut-elim (cut (μ-r d) d₁ x) = {!!}
cut-elim (cut (∨-r₁ d) d₁ x) = {!!}


cut-elim id-axiom = {!!}
cut-elim unit-r = {!!}
cut-elim (∧-r d d₁) = {!!}
cut-elim (∧-l₁ d) = {!!}
cut-elim (∧-l₂ d) = {!!}
cut-elim (∨-r₁ d) = {!!}
cut-elim (∨-r₂ d) = {!!}
cut-elim (∨-l d d₁) = {!!}
cut-elim (μ-r d) = {!!}
cut-elim (μ-l d x) = {!!}
cut-elim hyp-use = {!!}




-}
