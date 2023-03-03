{-#  OPTIONS --type-in-type #-}

module SR-vs-MIR where

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
open import FormulaExamples
open import LFP

NatRaw1 = μ (unit ∨ (μ BoolRaw))

Nat1 : Set
Nat1 = ⟦ NatRaw1 ⟧F  nothing

z1 : Nat1
z1 = In (inj₁ tt)

s1 : 𝔹 → Nat1
s1 b = In (inj₂ (In b))


module SingleRecNatBoolChar where

  open import SR


  charf2 :  (d : just (var ∷ [] ⇒ unit ∨ unit) ⊢  μ (unit ∨ unit) ∷ [] ⇒ unit ∨ unit)
   → (φ : Mu (λ X → ⊤ ⊎ Mu (λ X₁ → ⊤ ⊎ ⊤)) × ⊤ → ⊤ ⊎ ⊤)
    → ⟦ d ⟧ ((just (Mu (λ X → ⊤ ⊎ Mu (λ X₁ → ⊤ ⊎ ⊤))))) φ (In (inj₁ tt) , tt) ≡ ⟦ d ⟧ ((just (Mu (λ X → ⊤ ⊎ Mu (λ X₁ → ⊤ ⊎ ⊤))))) φ (In (inj₂ tt) , tt)
  charf2 (∨-r₁ d) φ  = refl
  charf2 (∨-r₂ d) φ  = refl
  charf2 (weakn (∨-r₁ d)) φ  = refl
  charf2 (weakn (∨-r₂ d)) φ  = refl
  charf2 (weakn (exchng () d)) φ 
  charf2 (exchng herex d) φ  = charf2 d φ
  charf2 (exchng (therex ()) d) φ

  charf3 :  (d : just (var ∷ [] ⇒ unit ∨ unit) ⊢  unit ∨ μ (unit ∨ unit) ∷ [] ⇒ unit ∨ unit)
   → (φ : Mu (λ X → ⊤ ⊎ Mu (λ X₁ → ⊤ ⊎ ⊤)) × ⊤ → ⊤ ⊎ ⊤)
    → ⟦ d ⟧ ((just (Mu (λ X → ⊤ ⊎ Mu (λ X₁ → ⊤ ⊎ ⊤))))) φ (inj₂ (In (inj₁ tt)) , tt) ≡ ⟦ d ⟧ ((just (Mu (λ X → ⊤ ⊎ Mu (λ X₁ → ⊤ ⊎ ⊤))))) φ ((inj₂ (In (inj₂ tt)) , tt))
  charf3 (∨-r₁ d) φ = refl
  charf3 (∨-r₂ d) φ = refl
  charf3 (∨-l d d₁) φ = charf2  d₁ _
  charf3 (weakn d) φ = refl
  charf3 (exchng herex d) φ = charf3 d φ
  charf3 (exchng (therex ()) d) φ


  charf :  (d : nothing ⊢ NatRaw1 ∷ [] ⇒ BoolRaw) → (b : 𝔹) →  ⟦ d ⟧ nothing tt (s1 (inj₁ tt) , tt) ≡ ⟦ d ⟧ nothing tt (s1 (inj₂ tt) , tt)
  charf (∨-r₁ d) b  =  refl
  charf (∨-r₂ d) b  =  refl
  charf (μ-l (∨-r₁ d) x x₁) (inj₁ tt)  =  refl
  charf (μ-l (∨-r₂ d) x x₁) (inj₁ tt)  =  refl
  charf (μ-l (∨-l d₁ d₂) x x₁) (inj₁ tt) rewrite x₁ = charf2 d₂ _
  charf (μ-l (weakn (∨-r₁ d)) x x₁) (inj₁ tt)  =  refl
  charf (μ-l (weakn (∨-r₂ d)) x x₁) (inj₁ tt)  =  refl 
  charf (μ-l (weakn (exchng () d)) x x₁) (inj₁ tt)
  charf (μ-l (exchng herex d) x x₁) (inj₁ tt) rewrite x₁ = charf3 d _
  charf (μ-l (exchng (therex ()) d) x x₁) (inj₁ tt)

  charf (μ-l (∨-r₁ d) x x₁) (inj₂ tt) = refl
  charf (μ-l (∨-r₂ d) x x₁) (inj₂ tt) = refl
  charf (μ-l (∨-l d d₁) x x₁) (inj₂ tt) rewrite x₁ = charf2 d₁ _
  charf (μ-l (weakn d) x x₁) (inj₂ tt) = refl
  charf (μ-l (exchng herex d) x x₁) (inj₂ tt) rewrite x₁ = charf3 d _
  charf (μ-l (exchng (therex ()) d) x x₁) (inj₂ tt) 

  charf (weakn (∨-r₁ unit-r)) b  =  refl
  charf (weakn (∨-r₁ (exchng () d))) b
  charf (weakn (∨-r₂ unit-r)) b  =  refl
  charf (weakn (∨-r₂ (exchng () d))) b
  charf (weakn (exchng () d)) b
  charf (exchng herex d) b = charf d b
  charf (exchng (therex ()) d) b




module MultIndRecSepExample where

  open import MIR

  {- separation example -}
  ce :  nothing ⊢ NatRaw1 ∷ [] ⇒ BoolRaw
  ce = μ-l (∨-l (∨-r₁ unit-r)  (μ-l (∨-l (∨-r₁ unit-r) (∨-r₂ unit-r)) refl refl)) refl refl

  charf-ce : ⟦ ce ⟧ nothing tt (s1 (inj₁ tt) , tt) ≡ ⟦ ce ⟧ nothing tt (s1 (inj₂ tt) , tt) → ⊥
  charf-ce ()

