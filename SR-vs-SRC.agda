{-#  OPTIONS --type-in-type #-}

module SR-vs-SRC where


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


open import SRC



postulate
  +-comm : ∀ a b → a + b ≡ b + a
  *-comm : ∀ a b → a * b ≡ b * a
  +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)


sepex : nothing ⊢ NatRaw ∷ [] ⇒ NatRaw
sepex = contr (μ-l (∨-l (μ-r (∨-r₂  (μ-r (∨-r₁ id-axiom)))) (exchng (therex herex) id-axiom)) refl refl)

case1-contr : (Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (⟦ sepex ⟧  nothing tt (ℕ2Nat (suc b) , tt)) ≡ k) → ⊥
case1-contr (proj₃ , proj₄) with proj₄ zero | proj₄ (suc zero)
... | o1 | o2 with trans o1  (sym o2)
... | ()

blahh : ∀ k → 1 ≡ suc k → k ≡ 0
blahh .0 refl = refl

case2-contr : Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (⟦ sepex ⟧ nothing tt ((ℕ2Nat b) , tt))  ≡ Nat2ℕ (⟦ sepex ⟧ nothing tt (z , tt)) + k * b) → ⊥
case2-contr (k , p) with p (suc zero)
... | o rewrite *-comm k 1 | +-comm k zero  with blahh k o
... | kv with p (suc (suc zero))
... | o' rewrite kv with o'
... | ()

case3-contr : Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (⟦ sepex ⟧ nothing tt ((ℕ2Nat b) , tt))  ≡ k + b ) → ⊥ 
case3-contr (k , p) with (sym (p zero))
... | o rewrite +-comm k zero with p (suc zero)
... | o' rewrite o with o'
... | ()
