

module NR-vs-SR where


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
open import Formula
open import FormulaExamples
open import LFP



module SRSeparationExample where

  open import SR

  idNatRaw : nothing ⊢ NatRaw ∷ [] ⇒ NatRaw
  idNatRaw = μ-l  (∨-l (unit-l (μ-r  (∨-r₁  unit-r))) (μ-r  (∨-r₂ (hyp-use )))) refl refl 

  idNat : Nat → Nat
  idNat n = ⟦ idNatRaw ⟧ nothing tt (n , tt)

  idNat-lem1 : Nat2ℕ (idNat (s (s (s z)))) ≡ 3
  idNat-lem1 = refl

  idNat-lem : ∀ x →  Nat2ℕ (idNat x) ≡ Nat2ℕ x
  idNat-lem (IN x (inj₁ x₁)) = refl
  idNat-lem (IN x (inj₂ y)) = cong suc (idNat-lem (x y))

  
