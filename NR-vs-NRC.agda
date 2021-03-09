{-#  OPTIONS --type-in-type #-}

module NR-vs-NRC where


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

module NoRecNat2NatChar where

  open import NR
  
  -- full characterization of functions "Nat → Nat"

  idax-free : {Γ : Context}{A : Formula} → tt ⊢ Γ ⇒ A → Bool
  idax-free unit-r = true
  idax-free (unit-l d) = idax-free d
  idax-free (∧-r d d₁) = idax-free d & idax-free d₁ 
  idax-free (∧-l d) = idax-free d
  idax-free (∨-r₁ d) = idax-free d
  idax-free (∨-r₂ d) = idax-free d
  idax-free (∨-l d d₁) = idax-free d & idax-free d₁
  idax-free (μ-r d) = idax-free d
  idax-free (μ-l d x x₁) = idax-free d
  idax-free (weakn d) = idax-free d
  idax-free (exchng x d) = idax-free d
  idax-free (id-axiom {A = μ (unit ∨ var)} ) = false
  idax-free id-axiom = true


  charf-[]-A : {A : Formula} → (d : tt ⊢ [] ⇒ A) → idax-free d ≡ true
  charf-[]-A unit-r = refl
  charf-[]-A (∧-r d d₁) rewrite charf-[]-A d  | charf-[]-A d₁ = refl
  charf-[]-A (∨-r₁ d) = charf-[]-A d
  charf-[]-A (∨-r₂ d) = charf-[]-A d
  charf-[]-A (μ-r {A = unit ∨ var} d) = charf-[]-A d
  charf-[]-A (μ-r {A = unit} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = A ∧ A₁} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = unit ∨ unit} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = unit ∨ (A₁ ∧ A₂)} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = unit ∨ (A₁ ∨ A₂)} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = unit ∨ μ A₁} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = (A ∧ A₂) ∨ A₁} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = (A ∨ A₂) ∨ A₁} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = var ∨ A₁} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = μ A ∨ A₁} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = var} d) =  charf-[]-A d
  charf-[]-A (μ-r {A = μ A} d) =  charf-[]-A d
  charf-[]-A (exchng () d)


  charf-unit-A : {A : Formula} → (d : tt ⊢ unit ∷ [] ⇒ A) → idax-free d ≡ true
  charf-unit-A id-axiom = refl
  charf-unit-A unit-r = refl
  charf-unit-A (unit-l d) = charf-[]-A d
  charf-unit-A (∧-r d d₁) rewrite charf-unit-A d | charf-unit-A d₁ = refl
  charf-unit-A (∨-r₁ d) = charf-unit-A d
  charf-unit-A (∨-r₂ d) = charf-unit-A d
  charf-unit-A (μ-r d) = charf-unit-A d
  charf-unit-A (weakn d) = charf-[]-A d
  charf-unit-A (exchng herex d) = charf-unit-A d
  charf-unit-A (exchng (therex ()) d)


  charf-var-A : {A : Formula} → (d : tt ⊢ var ∷ [] ⇒ A) → idax-free d ≡ true
  charf-var-A {.var} id-axiom = refl
  charf-var-A {.unit} unit-r = refl
  charf-var-A {.(_ ∧ _)} (∧-r d d₁) rewrite charf-var-A d | charf-var-A d₁ = refl
  charf-var-A {.(_ ∨ _)} (∨-r₁ d) = charf-var-A d
  charf-var-A {.(_ ∨ _)} (∨-r₂ d) = charf-var-A d
  charf-var-A {.(μ _)} (μ-r {A = A} d) = charf-var-A d
  charf-var-A {A} (weakn d) = charf-[]-A d
  charf-var-A {A} (exchng herex d) = charf-var-A d
  charf-var-A {A} (exchng (therex ()) d)


  charf-unitvar-A : {A : Formula} → (d : tt ⊢ unit ∨ var ∷ [] ⇒ A) → idax-free d ≡ true
  charf-unitvar-A id-axiom = refl
  charf-unitvar-A unit-r = refl
  charf-unitvar-A (∧-r d d₁) rewrite charf-unitvar-A d | charf-unitvar-A d₁ = refl
  charf-unitvar-A (∨-r₁ d) = charf-unitvar-A d
  charf-unitvar-A (∨-r₂ d) = charf-unitvar-A d
  charf-unitvar-A {unit} (∨-l d d₁) rewrite charf-var-A d₁ | charf-unit-A d = refl
  charf-unitvar-A {A ∧ A₁} (∨-l d d₁) rewrite charf-var-A d₁ | charf-unit-A d = refl
  charf-unitvar-A {A ∨ A₁} (∨-l d d₁) rewrite charf-var-A d₁ | charf-unit-A d = refl
  charf-unitvar-A {var} (∨-l d d₁) rewrite charf-var-A d₁ | charf-unit-A d = refl
  charf-unitvar-A {μ A} (∨-l d d₁) rewrite charf-var-A d₁ | charf-unit-A d = refl
  charf-unitvar-A (μ-r {A = unit ∨ var} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = unit} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = A ∧ A₁} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = unit ∨ unit} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = unit ∨ (A₁ ∧ A₂)} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = unit ∨ (A₁ ∨ A₂)} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = unit ∨ μ A₁} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = (A ∧ A₂) ∨ A₁} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = (A ∨ A₂) ∨ A₁} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = var ∨ A₁} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = μ A ∨ A₁} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = var} d) = charf-unitvar-A d
  charf-unitvar-A (μ-r {A = μ A} d) = charf-unitvar-A d
  charf-unitvar-A (weakn unit-r) = refl
  charf-unitvar-A (weakn (∧-r d d₁)) rewrite charf-[]-A d | charf-[]-A d₁ = refl
  charf-unitvar-A (weakn (∨-r₁ d)) =  charf-[]-A d 
  charf-unitvar-A (weakn (∨-r₂ d)) =  charf-[]-A d 
  charf-unitvar-A (weakn (μ-r {A = unit} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = A ∧ A₁} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = unit ∨ unit} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = unit ∨ (A₁ ∧ A₂)} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = unit ∨ (A₁ ∨ A₂)} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = unit ∨ var} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = unit ∨ μ A₁} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = (A ∧ A₂) ∨ A₁} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = (A ∨ A₂) ∨ A₁} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = var ∨ A₁} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = μ A ∨ A₁} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = var} d)) = charf-[]-A d
  charf-unitvar-A (weakn (μ-r {A = μ A} d)) = charf-[]-A d
  charf-unitvar-A (weakn (exchng () d))
  charf-unitvar-A {unit} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {A ∧ A₁} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {unit ∨ unit} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {unit ∨ (A₁ ∧ A₂)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {unit ∨ (A₁ ∨ A₂)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {unit ∨ var} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {unit ∨ μ A₁} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {(A ∧ A₂) ∨ A₁} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {(A ∨ A₂) ∨ A₁} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {var ∨ A₁} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ A ∨ A₁} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {var} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ unit} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (A ∧ A₁)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (unit ∨ unit)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (unit ∨ (A₁ ∧ A₂))} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (unit ∨ (A₁ ∨ A₂))} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (unit ∨ var)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (unit ∨ μ A₁)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ ((A ∧ A₂) ∨ A₁)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ ((A ∨ A₂) ∨ A₁)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (var ∨ A₁)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (μ A ∨ A₁)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ var} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A {μ (μ A)} (exchng herex d) = charf-unitvar-A d
  charf-unitvar-A (exchng (therex ()) d)


  charf-natraw-unit : (d : tt ⊢ NatRaw ∷ [] ⇒ unit) → idax-free d ≡ true
  charf-natraw-unit unit-r = refl
  charf-natraw-unit (μ-l d x x₁) = charf-unitvar-A d
  charf-natraw-unit (weakn unit-r) = refl
  charf-natraw-unit (weakn (exchng () d))
  charf-natraw-unit (exchng herex d) = charf-natraw-unit d
  charf-natraw-unit (exchng (therex ()) d)


  mutual
    charfs :  (d : tt ⊢ NatRaw ∷ [] ⇒ unit ∨ NatRaw) → {pf : idax-free d ≡ false} → Σ[ b₁ ∈ ℕ ] (∀ b →  Nat2ℕ (In (⟦ d ⟧ nothing  (b , tt))) ≡ b₁ + Nat2ℕ b )
    charfs (∨-r₁ d) {pf}  rewrite charf-natraw-unit d with pf
    ... | ()
    charfs (∨-r₂ d) {pf}  with norec-case2 d {pf} 
    ... |  (p1 , p2) = suc p1 , λ b → cong  suc (p2  b) --suc p1 , cong suc p2
    charfs (μ-l d x x₁) {pf}  rewrite charf-unitvar-A d with pf
    ... | ()
    charfs (weakn d) {pf}  rewrite charf-[]-A d with pf
    ... | ()
    charfs (exchng herex d) {pf}  = charfs d {pf}  
    charfs (exchng (therex ()) d) {pf} 

    norec-case2 :  (d : tt ⊢ NatRaw ∷ [] ⇒ NatRaw) → {pf : idax-free d ≡ false} → Σ[ b₁ ∈ ℕ ] (∀ b → Nat2ℕ (⟦ d ⟧ nothing  (b , tt)) ≡ b₁ + Nat2ℕ b)
    norec-case2 id-axiom = 0 , λ _ → refl
    norec-case2 (μ-r (∨-r₁ d)) {pf}   rewrite charf-natraw-unit d with pf
    ... | () 
    norec-case2 (μ-r (∨-r₂ d)) {pf}  with norec-case2 d {pf} 
    norec-case2 (μ-r (∨-r₂ d)) {pf}  | proj₃ , proj₄ = suc proj₃ , λ b → cong suc (proj₄ b)
    norec-case2 (μ-r (μ-l d x x₁)) {pf}   rewrite charf-unitvar-A d with pf
    ... | ()
    norec-case2 (μ-r (weakn d)) {pf}  rewrite charf-[]-A d with pf
    ... | ()
    norec-case2 (μ-r (exchng herex (∨-r₁ d))) {pf}  rewrite charf-natraw-unit d with pf
    ... | () 
    norec-case2 (μ-r (exchng herex (∨-r₂ d))) {pf}  with norec-case2 d {pf} 
    ... | (p1 , p2) = suc p1 , λ b → cong suc (p2 b)
    norec-case2 (μ-r (exchng herex (μ-l d x x₁))) {pf}  rewrite charf-unitvar-A d with pf
    ... | () 
    norec-case2 (μ-r (exchng herex (weakn d)))  {pf}  rewrite charf-[]-A d with pf
    ... | ()
    norec-case2 (μ-r (exchng herex (exchng herex d))) {pf}  = charfs d {pf} 
    norec-case2 (μ-r (exchng herex (exchng (therex ()) d))) 
    norec-case2 (μ-r (exchng (therex ()) d))
    norec-case2 (μ-l d x x₁) {pf} rewrite charf-unitvar-A d with pf
    ... | () 
    norec-case2 (weakn (μ-r (∨-r₁ unit-r))) {()} 
    norec-case2 (weakn (μ-r (∨-r₁ (exchng () d)))) 
    norec-case2 (weakn (μ-r (∨-r₂ (μ-r (∨-r₁ unit-r))))) {()} 
    norec-case2 (weakn (μ-r (∨-r₂ (μ-r (∨-r₁ (exchng () d)))))) 
    norec-case2 (weakn (μ-r (∨-r₂ (μ-r (∨-r₂ d))))) {pf}  rewrite charf-[]-A d with pf
    ... | ()
    norec-case2 (weakn (μ-r (∨-r₂ (μ-r (exchng () d))))) 
    norec-case2 (weakn (μ-r (∨-r₂ (exchng () d)))) 
    norec-case2 (weakn (μ-r (exchng () d))) 
    norec-case2 (weakn (exchng () d)) 
    norec-case2 (exchng herex d) {pf}  = norec-case2 d {pf} 
    norec-case2 (exchng (therex ()) d) 



  -- without id-axiom only (zero, suc) case distintction function is expressible
  mutual

    charf5 :  (d : tt ⊢ unit ∨ var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) → (b : Nat) → ⟦ d ⟧ (just Nat)  (inj₂ ( b) , tt) ≡ ⟦ d ⟧ (just Nat)  (inj₂ ( (s b)) , tt)
    charf5 (∨-r₁ d) b = refl
    charf5 (∨-r₂ d) b rewrite charf2 d b = refl
    charf5 (∨-l d d₁) b = charf4 d₁ b
    charf5 (weakn d) b = refl
    charf5 (exchng herex d) b = charf5 d b
    charf5 (exchng (therex ()) d)

    charf4 :  (d : tt ⊢ var ∷ [] ⇒ unit ∨ μ (unit ∨ var)) → (b : Nat) → ⟦ d ⟧ (just Nat)  ( ( b) , tt) ≡ ⟦ d ⟧ (just Nat)  ( ( (s b)) , tt)
    charf4 (∨-r₁ d) b = refl
    charf4 (∨-r₂ d) b rewrite charf3 d b = refl
    charf4 (weakn d) b = refl
    charf4 (exchng herex d) b = charf4 d b
    charf4 (exchng (therex ()) d) b

    charf3 :  (d : tt ⊢ var ∷ [] ⇒ μ (unit ∨ var)) → (b : Nat) → ⟦ d ⟧ (just Nat)  ( ( b) , tt) ≡ ⟦ d ⟧ (just Nat)  ( ( (s b)) , tt)
    charf3 (μ-r d) b rewrite charf4 d b = refl
    charf3 (weakn d) b = refl
    charf3 (exchng herex d) b = charf3 d b
    charf3 (exchng (therex ()) d)

    charf2 :  (d : tt ⊢ unit ∨ var ∷ [] ⇒ μ (unit ∨ var)) → (b : Nat) → ⟦ d ⟧ (just Nat)  (inj₂ ( b) , tt) ≡ ⟦ d ⟧ (just Nat)  (inj₂ ( (s b)) , tt)
    charf2 (∨-l d d₁) b = charf3 d₁ b
    charf2 (μ-r (∨-r₁ d)) b = refl
    charf2 (μ-r (∨-r₂ d)) b rewrite charf2 d b = refl
    charf2 (μ-r (∨-l d d₁)) b rewrite charf4  d₁ b =  refl
    charf2 (μ-r (weakn (∨-r₁ d))) b = refl
    charf2 (μ-r (weakn (∨-r₂ d))) b = refl
    charf2 (μ-r (weakn (exchng () d))) b
    charf2 (μ-r (exchng herex (∨-r₁ d))) b = refl
    charf2 (μ-r (exchng herex (∨-r₂ d))) b rewrite charf2 d b = refl
    charf2 (μ-r (exchng herex (∨-l d d₁))) b rewrite charf4  d₁ b =  refl
    charf2 (μ-r (exchng herex (weakn (∨-r₁ d)))) b = refl
    charf2 (μ-r (exchng herex (weakn (∨-r₂ d)))) b = refl
    charf2 (μ-r (exchng herex (weakn (exchng () d)))) b
    charf2 (μ-r (exchng herex (exchng herex d))) b rewrite charf5 d b = refl
    charf2 (μ-r (exchng herex (exchng (therex ()) d))) b
    charf2 (μ-r (exchng (therex ()) d)) b
    charf2 (weakn (μ-r d)) b = refl
    charf2 (weakn (exchng () d)) b
    charf2 (exchng herex d) b = charf2 d b
    charf2 (exchng (therex ()) d) b

  mutual

    charf7 :  (d : tt ⊢ NatRaw ∷ [] ⇒ unit ∨ NatRaw) → {pf : idax-free d ≡ true} → (b : Nat) → ⟦ d ⟧ nothing  (s b , tt) ≡ ⟦ d ⟧ nothing  (s (s b) , tt)
    charf7 (∨-r₁ d) b = refl
    charf7 (∨-r₂ d) {pf} b rewrite norec-case1 d {pf} b = refl
    charf7 (μ-l d x x₁) b = charf5 d b
    charf7 (weakn d) b = refl
    charf7 (exchng herex d) {pf} b = charf7 d {pf} b
    charf7 (exchng (therex ()) d) b

    norec-case1 :  (d : tt ⊢ NatRaw ∷ [] ⇒ NatRaw) → {pf : idax-free d ≡ true} → (b : Nat) →  ⟦ d ⟧ nothing  (s b , tt) ≡ ⟦ d ⟧ nothing  (s (s b) , tt)
    norec-case1 id-axiom {()} b
    norec-case1 (μ-r (∨-r₁ d)) b =  refl
    norec-case1 (μ-r (∨-r₂ d)) {pf} b rewrite norec-case1 d {pf}  b = refl
    norec-case1 (μ-r (μ-l d x x₁)) b rewrite charf5  d b =  refl
    norec-case1 (μ-r (weakn (∨-r₁ d))) b = refl
    norec-case1 (μ-r (weakn (∨-r₂ d))) b = refl
    norec-case1 (μ-r (weakn (exchng () d))) b
    norec-case1 (μ-r (exchng herex (∨-r₁ d))) b = refl
    norec-case1 (μ-r (exchng herex (∨-r₂ d))) {pf} b rewrite norec-case1 d {pf} b = refl
    norec-case1 (μ-r (exchng herex (μ-l d x x₁))) b rewrite charf5 d b = refl
    norec-case1 (μ-r (exchng herex (weakn d))) b = refl
    norec-case1 (μ-r (exchng herex (exchng herex d))) {pf} b rewrite charf7 d  {pf}  b = refl

    norec-case1 (μ-r (exchng herex (exchng (therex ()) d))) b
    norec-case1 (μ-r (exchng (therex ()) d)) b

    norec-case1 (μ-l d x x₁) b = charf2  d b
    norec-case1 (weakn (μ-r (∨-r₁ d))) b =  refl
    norec-case1 (weakn (μ-r (∨-r₂ d))) b =  refl
    norec-case1 (weakn (μ-r (exchng () d))) b
    norec-case1 (weakn (exchng () d)) b
    norec-case1 (exchng herex d) {pf} b = norec-case1 d {pf} b
    norec-case1 (exchng (therex ()) d) b




module NoRecWithCSeparationExample where

  open import NRC

  idax-free : {Γ : Context}{A : Formula} → tt ⊢ Γ ⇒ A → Bool
  idax-free unit-r = true
  idax-free (unit-l d) = idax-free d
  idax-free (∧-r d d₁) = idax-free d & idax-free d₁ 
  idax-free (∧-l d) = idax-free d
  idax-free (∨-r₁ d) = idax-free d
  idax-free (∨-r₂ d) = idax-free d
  idax-free (∨-l d d₁) = idax-free d & idax-free d₁
  idax-free (μ-r d) = idax-free d
  idax-free (μ-l d x x₁) = idax-free d
  idax-free (weakn d) = idax-free d
  idax-free (exchng x d) = idax-free d
  idax-free (id-axiom {A = μ (unit ∨ var)} ) = false
  idax-free id-axiom = true
  idax-free (contr d) = idax-free d

  what?! : tt ⊢ NatRaw ∷ [] ⇒ NatRaw
  what?! = contr (μ-l (∨-l (μ-r  (∨-r₁ unit-r)) (exchng (therex herex) (μ-r (∨-r₂  id-axiom)))) refl refl)

  what?!₁ :   (⟦ what?! ⟧ nothing  (z , tt)) ≡ z
  what?!₁ = refl

  what?!₂ :   (⟦ what?! ⟧ nothing  (s z , tt)) ≡ s (s z)
  what?!₂ = refl


  lem0 : idax-free what?! ≡ false
  lem0 = refl

  lem1 :  (Σ[ b₁ ∈ ℕ ] (∀ b → Nat2ℕ (⟦ what?! ⟧ nothing  (b , tt)) ≡ b₁ + Nat2ℕ b)) → ⊥
  lem1 (zero , proj₄) with proj₄ (s z)
  ... | () 
  lem1 (suc proj₃ , proj₄) with proj₄ z
  ... | () 
