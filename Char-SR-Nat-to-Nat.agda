{-#  OPTIONS --type-in-type #-}

module Char-SR-Nat-to-Nat where


open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.List.Membership.Propositional using (_∈_) 
open import Data.List.Any  hiding (map)
open import Data.Vec
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary
open import Data.Bool renaming (_∧_ to _&_; _∨_ to _∣_)
open import Data.Maybe

open import ListIn
open import Formula
open import FormulaExamples
open import LFP

open import SR


postulate
  +-comm : ∀ a b → a + b ≡ b + a
  *-comm : ∀ a b → a * b ≡ b * a
  +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)


mutual
  case112' : {Φ : HContext}
    (d   : Φ ⊢ [] ⇒ unit ∨ μ (unit ∨ var)) → idax-free d ≡ true
  case112' (∨-r₁ unit-r) = refl
  case112' (∨-r₁ hyp-use) = refl
  case112' (∨-r₁ (exchng () d))
  case112' (∨-r₂ d) = case112 d
  case112' (exchng () d)
  case112' hyp-use = refl

  case112 : {Φ : HContext}
    (d   : Φ ⊢ [] ⇒ μ (unit ∨ var)) → idax-free d ≡ true
  case112 (μ-r d) = case112' d
  case112 (exchng () d)
  case112 hyp-use = refl


case11111 : {Φ : HContext} (d   : Φ ⊢ [] ⇒ unit) → idax-free d ≡ true
case11111 unit-r = refl
case11111 hyp-use = refl
case11111 (exchng () d)

case11112 : {Φ : HContext} (d   : Φ ⊢ var ∷ [] ⇒ unit) → idax-free d ≡ true
case11112 unit-r = refl
case11112 hyp-use = refl
case11112 (weakn d) = case11111 d
case11112 (exchng herex d) = case11112 d
case11112 (exchng (therex ()) d)

case11113 : {Φ : HContext} (d   : Φ ⊢ unit ∷ [] ⇒ unit) → idax-free d ≡ true
case11113 id-axiom = refl
case11113 unit-r = refl
case11113 (unit-l d) = case11111 d
case11113 hyp-use = refl
case11113 (weakn d) = case11111 d
case11113 (exchng herex d) = case11113 d
case11113 (exchng (therex ()) d)

case1111 : {Φ : HContext} (d   : Φ ⊢ unit ∨ var ∷ [] ⇒ unit) → idax-free d ≡ true
case1111 unit-r = refl
case1111 (∨-l d d₁) rewrite case11112 d₁ | case11113 d = refl
case1111 hyp-use = refl
case1111  (weakn d) = case11111 d
case1111 (exchng herex d) = case1111 d
case1111 (exchng (therex ()) d)

mutual
  case1112 : {Φ : HContext} (d   : Φ ⊢ unit  ∷ [] ⇒ unit ∨ μ (unit ∨ var)) → idax-free d ≡ true
  case1112 (unit-l d) = case112' d
  case1112 (∨-r₁ d) = case11113 d
  case1112 (∨-r₂ d) = case1112' d
  case1112 hyp-use = refl
  case1112 (weakn d) = case112' d
  case1112 (exchng herex d) = case1112 d
  case1112 (exchng (therex ()) d)

  case1112' : {Φ : HContext} (d   : Φ ⊢ unit  ∷ [] ⇒ μ (unit ∨ var)) → idax-free d ≡ true
  case1112' (unit-l d) = case112 d
  case1112' (μ-r d) = case1112 d
  case1112' hyp-use = refl
  case1112' (weakn d) = case112 d
  case1112' (exchng herex d) = case1112' d
  case1112' (exchng (therex ()) d)

mutual
  case1113 : {Φ : HContext} (d   : Φ ⊢ var  ∷ [] ⇒ unit ∨ μ (unit ∨ var)) → idax-free d ≡ true
  case1113 (∨-r₁ d) = case11112 d
  case1113 (∨-r₂ d) = case1113' d
  case1113 hyp-use = refl
  case1113 (weakn d) = case112' d
  case1113 (exchng herex d) = case1113 d
  case1113 (exchng (therex ()) d)

  case1113' : {Φ : HContext} (d   : Φ ⊢ var ∷ [] ⇒ μ (unit ∨ var)) → idax-free d ≡ true
  case1113' (μ-r d) = case1113 d
  case1113' hyp-use = refl
  case1113' (weakn d) = case112 d
  case1113' (exchng herex d) = case1113' d
  case1113' (exchng (therex ()) d)


mutual

  case111' : {Φ : HContext} (d   : Φ ⊢ unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) → idax-free d ≡ true
  case111' (∨-r₁ d) = case1111 d
  case111' (∨-r₂ d) = case111 d
  case111' (∨-l d d₁) rewrite case1112 d = case1113 d₁
  case111' (weakn d) = case112' d
  case111' (exchng herex d) = case111' d
  case111' (exchng (therex ()) d)
  case111' hyp-use = refl

  case111 : {Φ : HContext}
    (d   : Φ ⊢ unit ∨ var ∷ [] ⇒ μ (unit ∨ var)) → idax-free d ≡ true
  case111 (∨-l d d₁) rewrite case1113' d₁ | case1112' d = refl
  case111 (μ-r d) = case111' d
  case111 (weakn d) = case112 d
  case111 (exchng herex d) = case111 d
  case111 (exchng (therex ()) d)      
  case111 hyp-use = refl

case1122 : {Φ : HContext} (d   : Φ ⊢ NatRaw ∷ [] ⇒ unit) → idax-free d ≡ true
case1122 unit-r = refl
case1122 (μ-l d x x₁) = case1111 d
case1122 hyp-use = refl
case1122 (weakn d) =  case11111 d
case1122 (exchng herex d) = case1122 d
case1122 (exchng (therex ()) d)

mutual
  case11' :  (d : nothing ⊢ NatRaw ∷ [] ⇒ unit ∨  NatRaw)
      → {pf : idax-free d ≡ false}
      →  Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (In (⟦ d ⟧ nothing tt ((ℕ2Nat b) , tt)))  ≡ k + b )
  case11' (∨-r₁ d) {pf} rewrite case1122 d with pf
  ... | ()
  case11' (∨-r₂ d) {pf} with case3 d {pf}
  ... | k , p = suc k , λ b → cong suc (p b)
  case11' (μ-l d x x₁) {pf} rewrite case111' d with pf
  ... | ()
  case11' (weakn d) {pf} rewrite case112'  d with pf
  ... | ()
  case11' (exchng herex d) {pf} = case11' d {pf}
  case11' (exchng (therex ()) d) {pf}


  case3 :  (d : nothing ⊢ NatRaw ∷ [] ⇒ NatRaw)
      → {pf : idax-free d ≡ false}
      →  Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (⟦ d ⟧ nothing tt ((ℕ2Nat b) , tt))  ≡ k + b )
  case3 id-axiom = 0 , λ b → hb  b
  case3 (μ-r d) {pf} = case11' d {pf}
  case3 (μ-l d x x₁) {pf} rewrite case111 d with pf
  ... | ()
  case3 (weakn d) {pf} rewrite case112 d with pf
  ... | ()
  case3 (exchng herex d) {pf} =  case3 d {pf}
  case3 (exchng (therex ()) d)    
    

mutual
  caseFold21' : (d  : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢  var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒ μ (unit ∨ var)) ⟧S (just Nat) ) 
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (In (⟦ d ⟧  (just Nat) φ (ℕ2Nat b , tt))) ≡ k
  caseFold21' (∨-r₁ d) φ {pf} = 0 , λ b → refl
  caseFold21' (∨-r₂ d) φ {pf} with caseFold21 d φ {pf}
  ... | k , prf = suc k , λ b → cong suc (prf b)
  caseFold21' (weakn d) φ {pf} = _ , λ b → refl
  caseFold21' (exchng herex d) φ {pf} = caseFold21' d φ {pf}
  caseFold21' (exchng (therex ()) d) φ {pf}


  caseFold21 : (d  : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢  var ∷ [] ⇒ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒ μ (unit ∨ var)) ⟧S (just Nat) )
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (⟦ d ⟧  (just Nat) φ (ℕ2Nat b , tt)) ≡ k
  caseFold21 (μ-r d) φ {pf} = caseFold21' d φ {pf}
  caseFold21 hyp-use φ {()}
  caseFold21 (weakn d) φ {pf} = _ , λ b → refl
  caseFold21 (exchng herex d) φ {pf} = caseFold21 d φ {pf}
  caseFold21 (exchng (therex ()) d) φ {pf}


mutual
  caseFold21'q : (d  : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢  var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⟧S (just Nat) ) 
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (In (⟦ d ⟧  (just Nat) φ (ℕ2Nat b , tt))) ≡ k
  caseFold21'q (∨-r₁ d) φ {pf} = 0 , λ b → refl
  caseFold21'q (∨-r₂ d) φ {pf} with caseFold21q d φ {pf}
  ... | k , prf = suc k , λ b → cong suc (prf b)
  caseFold21'q (weakn d) φ {pf} = _ , λ b → refl
  caseFold21'q (exchng herex d) φ {pf} = caseFold21'q d φ {pf}
  caseFold21'q (exchng (therex ()) d) φ {pf}
  caseFold21'q hyp-use φ {()}


  caseFold21q : (d  : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢  var ∷ [] ⇒ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⟧S (just Nat) )
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (⟦ d ⟧  (just Nat) φ (ℕ2Nat b , tt)) ≡ k
  caseFold21q (μ-r d) φ {pf} = caseFold21'q d φ {pf}
  caseFold21q (weakn d) φ {pf} = _ , λ b → refl
  caseFold21q (exchng herex d) φ {pf} = caseFold21q d φ {pf}
  caseFold21q (exchng (therex ()) d) φ {pf}


mutual

  case1w : (d  : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢  unit ∨ var ∷ [] ⇒ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒ μ (unit ∨ var)) ⟧S (just Nat) )
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (⟦ d ⟧  (just Nat) φ (inj₂ (ℕ2Nat b) , tt)) ≡ k
  case1w (∨-l d d₁) φ {pf} = caseFold21 d₁ φ {closed-2 pf} 
  case1w (μ-r d) φ {pf} with case1w' d φ {pf}
  ... | o , p = o , λ b → p b
  case1w (weakn d) φ {pf} = _ , λ b → refl
  case1w (exchng herex d) = case1w d
  case1w (exchng (therex ()) d)


  case1w' : (d  : just (var ∷ [] ⇒  μ (unit ∨ var)) ⊢  unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒  μ (unit ∨ var)) ⟧S (just Nat) )
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (In (⟦ d ⟧  (just Nat) φ (inj₂ (ℕ2Nat b) , tt))) ≡ k
  case1w' (∨-r₁ d) φ {pf} = _ , λ b → refl
  case1w' (∨-r₂ d) φ {pf} with case1w d φ {pf}
  ... | o , p = suc o , λ b → cong suc (p b)
  case1w' (∨-l d d₁) φ {pf}  = caseFold21' d₁ φ {closed-2 pf}
  case1w' (weakn d) φ {pf} = _ , λ b → refl
  case1w' (exchng herex d) = case1w' d
  case1w' (exchng (therex ()) d)


mutual

  case1y : (d  : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢  unit ∨ var ∷ [] ⇒ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⟧S (just Nat) )
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (⟦ d ⟧  (just Nat) φ (inj₂ (ℕ2Nat b) , tt)) ≡ k
  case1y (∨-l d d₁) φ {pf} = caseFold21q d₁ φ {closed-2 pf}
  case1y (μ-r d) φ {pf} with case1y' d φ {pf}
  ... | o , p = o , λ b → p b
  case1y (weakn d) φ {pf} = _ , λ b → refl
  case1y (exchng herex d) = case1y d
  case1y (exchng (therex ()) d)


  case1y' : (d  : just (var ∷ [] ⇒   unit ∨ μ (unit ∨ var)) ⊢  unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
        → (φ : ⟦ (var ∷ [] ⇒  unit ∨ μ (unit ∨ var)) ⟧S (just Nat) )
        → {pf : hyp-free d ≡ true}
        → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (In (⟦ d ⟧  (just Nat) φ (inj₂ (ℕ2Nat b) , tt))) ≡ k
  case1y' (∨-r₁ d) φ {pf} = _ , λ b → refl
  case1y' (∨-r₂ d) φ {pf} with case1y d φ {pf}
  ... | o , p = suc o , λ b → cong suc (p b)
  case1y' (∨-l d d₁) φ {pf}  = caseFold21'q d₁ φ {closed-2 pf}
  case1y' (weakn d) φ {pf} = _ , λ b → refl
  case1y' (exchng herex d) = case1y' d
  case1y' (exchng (therex ()) d)




mutual


  case1' : (d  : nothing ⊢  NatRaw ∷ [] ⇒ unit ∨ NatRaw)
          → {pf : idax-free d ≡ true}
          → {pf' : hyp-free d ≡ true}
          → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (In (⟦ d ⟧  nothing tt (ℕ2Nat (suc b) , tt))) ≡ k
  case1' (∨-r₁ d) = _ , λ b → refl
  case1' (∨-r₂ d) {pf} {pf'} with case1 d {pf} {pf'}
  ... | k , p = suc k , λ b → cong suc (p b) 
  case1' (μ-l d x x₁) {pf} {pf'} = case1y' d _ {pf'}
  case1' (weakn d) = _ , λ b → refl
  case1' (exchng herex d) {pf} {pf'} = case1' d {pf} {pf'}
  case1' (exchng (therex ()) d)        

  case1 : (d  : nothing ⊢  NatRaw ∷ [] ⇒ NatRaw)
          → {pf : idax-free d ≡ true}
          → {pf' : hyp-free d ≡ true}          
          → Σ[ k ∈ ℕ ] ∀ b →  Nat2ℕ (⟦ d ⟧  nothing tt (ℕ2Nat (suc b) , tt)) ≡ k
  case1 id-axiom {()} 
  case1 (μ-r d) {pf} {pf'} = case1' d {pf} {pf'}
  case1 (μ-l d x x₁) {pf} {pf'} = case1w d _ {pf'}
  case1 (weakn d) = _ , λ b → refl
  case1 (exchng herex d) {pf} {pf'} = case1 d {pf} {pf'}
  case1 (exchng (therex ()) d)







mutual
  case211' : (d : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ c ∈ ℕ ] ∀ b → (Nat2ℕ (In (⟦ d ⟧ (just Nat) φ (b , tt))) ≡ c +  Nat2ℕ (φ (b , tt)) )
  case211' (∨-r₁ d) {pf} φ with  hyp-free-unit d (λ ())
  ... | q rewrite q with pf
  ... | ()
  case211' (∨-r₂ d) {pf} φ  with case211 d {pf} φ 
  ... | c ,  p = suc c , λ b → cong suc (p b)
  case211' (weakn d) {pf} φ  rewrite var-free-hyp d refl with pf
  ... | ()
  case211' (exchng herex d) {pf} φ  = case211' d {pf} φ
  case211' (exchng (therex ()) d) φ 

  case211 : (d : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢ var ∷ [] ⇒ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ c ∈ ℕ ] ∀ b → (Nat2ℕ (⟦ d ⟧ (just Nat) φ (b , tt)) ≡ c +  Nat2ℕ (φ (b , tt)) )
  case211 (μ-r d) {pf} φ  = case211' d {pf} φ 
  case211 hyp-use φ  = 0 , λ b → refl
  case211 (weakn d) {pf} φ rewrite var-free-hyp d refl with pf
  ... | ()
  case211 (exchng herex d) {pf} φ  = case211 d {pf} φ 
  case211 (exchng (therex ()) d) φ



mutual
  case211'u : (d : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ c ∈ ℕ ] ∀ b → (Nat2ℕ (In (⟦ d ⟧ (just Nat) φ (b , tt))) ≡ c +  Nat2ℕ (In (φ ( (b , tt)))) )
  case211'u (∨-r₁ d) {pf} φ with  hyp-free-unit d (λ ())
  ... | q rewrite q with pf
  ... | ()
  case211'u (∨-r₂ d) {pf} φ  with case211u d {pf} φ 
  ... | c ,  p = suc c , λ b → cong suc (p b)
  case211'u (weakn d) {pf} φ  rewrite var-free-hyp d refl with pf
  ... | ()
  case211'u hyp-use φ  = 0 , λ b → refl
  case211'u (exchng herex d) {pf} φ  = case211'u d {pf} φ
  case211'u (exchng (therex ()) d) φ 

  case211u : (d : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢ var ∷ [] ⇒ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ c ∈ ℕ ] ∀ b → (Nat2ℕ (⟦ d ⟧ (just Nat) φ (b , tt)) ≡ c +  Nat2ℕ (In (φ (b , tt))) )
  case211u (μ-r d) {pf} φ  = case211'u d {pf} φ 
  case211u (weakn d) {pf} φ  rewrite var-free-hyp d refl with pf
  ... | ()
  case211u (exchng herex d) {pf} φ  = case211u d {pf} φ 
  case211u (exchng (therex ()) d) φ


mutual
  case21' : (d : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ c ∈ ℕ ] ∀ b → (Nat2ℕ (In (⟦ d ⟧ (just Nat) φ  (inj₂ b , tt))) ≡ c +  Nat2ℕ (φ (b , tt)) )
  case21' (∨-r₁ d) {pf} φ with  hyp-free-unit d (λ ())
  ... | q rewrite q with pf
  ... | ()
  case21' (∨-r₂ d) {pf} φ  with case21 d {pf} φ 
  ... | k ,  p = suc k , λ b → cong suc (p b) 
  case21' (∨-l d d₁) {pf} φ  rewrite var-free-hyp d refl = case211' d₁ {pf} φ  
  case21' (weakn d) {pf} φ  rewrite var-free-hyp d refl with pf
  ... | ()
  case21' (exchng herex d) {pf} φ  = case21' d {pf} φ 
  case21' (exchng (therex ()) d) φ 

  case21 : (d : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ k ∈ ℕ ] ∀ b  → (Nat2ℕ (⟦ d ⟧ (just Nat) φ (inj₂ b , tt)) ≡ k +  Nat2ℕ (φ (b , tt)))
  case21 (∨-l d d₁) {pf} φ rewrite var-free-hyp d refl  = case211 d₁ {pf} φ
  case21 (μ-r d) {pf} φ with case21' d {pf} φ
  ... | k ,  p = k , λ b → p b 
  case21 (weakn d) {pf} φ  rewrite var-free-hyp  d refl with pf
  ... | ()
  case21 (exchng herex d) {pf} φ  = case21 d {pf} φ 
  case21 (exchng (therex ()) d) φ 



mutual
  case21u' : (d : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ c ∈ ℕ ] ∀ b → (Nat2ℕ (In (⟦ d ⟧ (just Nat) φ  (inj₂ b , tt))) ≡ c +  Nat2ℕ (In (φ (b , tt))) )
  case21u' (∨-r₁ d) {pf} φ with  hyp-free-unit d (λ ())
  ... | q rewrite q with pf
  ... | ()
  case21u' (∨-r₂ d) {pf} φ  with case21u d {pf}  φ 
  ... | k ,  p = suc k , λ b → cong suc (p b) 
  case21u' (∨-l d d₁) {pf} φ rewrite var-free-hyp d refl = case211'u d₁ {pf} φ  
  case21u' (weakn d) {pf} φ rewrite var-free-hyp d refl with pf
  ... | ()
  case21u' (exchng herex d) {pf} φ  = case21u' d {pf} φ 
  case21u' (exchng (therex ()) d) φ 

  case21u : (d : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ μ (unit ∨ var))
   → {pf : hyp-free d ≡ false}
   → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⟧H (just Nat) )
   → Σ[ k ∈ ℕ ] ∀ b  → (Nat2ℕ (⟦ d ⟧ (just Nat) φ (inj₂ b , tt)) ≡ k +  Nat2ℕ (In (φ (b , tt))))
  case21u (∨-l d d₁) {pf} φ rewrite var-free-hyp d refl = case211u d₁ {pf} φ
  case21u (μ-r d) {pf} φ  with case21u' d {pf} φ
  ... | k ,  p = k , λ b → (p b)
  case21u (weakn d) {pf} φ rewrite var-free-hyp d refl with pf
  ... | ()
  case21u (exchng herex d) {pf} φ  = case21u d {pf} φ 
  case21u (exchng (therex ()) d) φ 



caseFold' : (d  : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ μ (unit ∨ var))
     → {pf : hyp-free d ≡ false}
     → (k : ℕ)
     → (proj₁ (case21 d {pf} (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)) ≡ k )
     → ∀ b → Nat2ℕ (Fold (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q → rf (proj₁ q) w) (rv , w)) (ℕ2Nat b) tt)
       ≡ Nat2ℕ
      (⟦ d ⟧ (just (Mu (λ X → ⊤ ⊎ X)))
       (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)
       (inj₁ tt , tt))  + k *  b
caseFold' d k p zero rewrite *-comm k zero = +-comm zero _
caseFold' d {pf} k p (suc b) with (case21 d {pf}
     (λ q →
        Fold
        (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
        (proj₁ q) tt)
     ) | inspect (case21 d {pf}) (λ q →
        Fold
        (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
        (proj₁ q) tt)
caseFold' d .proj₃ refl (suc b) | proj₃ , proj₄ | Reveal_·_is_.[ eq ]
 rewrite proj₄ (ℕ2Nat b)
 | caseFold' d proj₃ (subst (λ R → proj₁ R ≡ proj₃) (sym eq) refl) b
 | *-comm proj₃ (suc b)
 | *-comm proj₃ b with Nat2ℕ (⟦ d ⟧ (just Nat) (λ q → Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w)) (proj₁ q) tt)
          (inj₁ tt , tt))
... | c rewrite sym (+-assoc proj₃ c (b * proj₃))
    | +-comm proj₃ c = +-assoc c _ (b * proj₃)



caseFold'U : (d  : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
     → {pf : hyp-free d ≡ false}
     → (k : ℕ)
     → (proj₁ (case21u' d {pf} (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)) ≡ k )
     → ∀ b → Nat2ℕ (In (Fold (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q → rf (proj₁ q) w) (rv , w)) (ℕ2Nat b) tt))
       ≡ Nat2ℕ
      (In (⟦ d ⟧ (just (Mu (λ X → ⊤ ⊎ X)))
       (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)
       (inj₁ tt , tt)))  + k *  b
caseFold'U d k p zero rewrite *-comm k zero = +-comm zero _
caseFold'U d {pf} k p (suc b) with (case21u' d {pf}
     (λ q →
        Fold
        (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
        (proj₁ q) tt)
     ) | inspect (case21u' d {pf}) (λ q →
        Fold
        (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
        (proj₁ q) tt)
caseFold'U d .proj₃ refl (suc b) | proj₃ , proj₄ | Reveal_·_is_.[ eq ] rewrite proj₄ (ℕ2Nat b) | caseFold'U d proj₃ (subst (λ R → proj₁ R ≡ proj₃) (sym eq) refl) b |  *-comm proj₃ (suc b)
 | *-comm proj₃ b with Nat2ℕ
      (In (⟦ d ⟧ (just (Mu (_⊎_ ⊤)))
       (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)
       (inj₁ tt , tt)))
... |  c rewrite sym (+-assoc proj₃ c (b * proj₃)) | +-comm proj₃ c       = +-assoc c _ (b * proj₃)



caseFold : (d  : just (var ∷ [] ⇒ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ μ (unit ∨ var))
      → {pf : hyp-free d ≡ false}
      → Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (Fold
             (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q → rf (proj₁ q) w) (rv , w)) (ℕ2Nat b)
             tt) ≡ Nat2ℕ
      (⟦ d ⟧ (just (Mu (λ X → ⊤ ⊎ X)))
       (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)
       (inj₁ tt , tt)) + k *  b)
caseFold d {pf} with (case21 d {pf}) (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt) | inspect (case21 d {pf})  (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)
caseFold d {pf} | k ,  p | Reveal_·_is_.[ eq ] = k , λ b → caseFold' d {pf} k (subst (λ R → proj₁ R ≡ k) (sym eq ) refl) b



caseFoldU : (d  : just (var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) ⊢ unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var))
      → {pf : hyp-free d ≡ false}
      → Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (In (Fold
             (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q → rf (proj₁ q) w) (rv , w)) (ℕ2Nat b)
             tt)) ≡ Nat2ℕ
      (In (⟦ d ⟧ (just (Mu (λ X → ⊤ ⊎ X)))
       (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)
       (inj₁ tt , tt))) + k *  b)
caseFoldU d {pf} with (case21u' d {pf}) (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt) | inspect (case21u' d {pf})  (λ q →
          Fold
          (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
          (proj₁ q) tt)
caseFoldU d {pf} | k ,  p | Reveal_·_is_.[ eq ] = k , λ b → caseFold'U d {pf} k ((subst (λ R → proj₁ R ≡ k) (sym eq ) refl)) b





mutual

  case2' :  (d : nothing ⊢ NatRaw ∷ [] ⇒ unit ∨ NatRaw)
     → {pf : hyp-free d ≡ false}
     →  Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (In (⟦ d ⟧ nothing tt ((ℕ2Nat b) , tt))) ≡ Nat2ℕ (In (⟦ d ⟧ nothing tt (z , tt))) + k * b)
  case2' (∨-r₁ d) = 0 ,  λ b → refl
  case2' (∨-r₂ d) {pf} with case2 d {pf}
  ... | k ,  prf = k ,  λ b → cong suc (prf b)
  case2' (μ-l d x x₁) {pf} =  caseFoldU d {pf}
  case2' (weakn (∨-r₁ d)) = 0 ,  λ b → refl
  case2' (weakn (∨-r₂ d)) = 0 , λ b → cong suc (+-comm zero _)
  case2' (weakn (exchng () d))
  case2' (exchng herex d) {pf} = case2' d {pf}
  case2' (exchng (therex ()) d)

  case2 :  (d : nothing ⊢ NatRaw ∷ [] ⇒ NatRaw)
    → {pf : hyp-free d ≡ false}
    →  Σ[ k ∈ ℕ ] (∀ b → Nat2ℕ (⟦ d ⟧ nothing tt ((ℕ2Nat b) , tt))  
           ≡ Nat2ℕ (⟦ d ⟧ nothing tt (z , tt)) + k * b)
  case2 id-axiom = 1 ,  λ b → trans (hb b) (+-comm zero _)
  case2 (μ-r d) {pf} = case2' d {pf}
  case2 (μ-l d x x₁) {pf} = caseFold d {pf}
  case2 (weakn (μ-r (∨-r₁ unit-r))) = 0 ,  λ b → refl
  case2 (weakn (μ-r (∨-r₁ (exchng () d))))
  case2 (weakn (μ-r (∨-r₂ d))) = 0 ,  λ b → cong suc (+-comm zero _)
  case2 (weakn (μ-r (exchng () d)))
  case2 (weakn (exchng () d))
  case2 (exchng herex d) {pf} = case2 d {pf}
  case2 (exchng (therex ()) d)

