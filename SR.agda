{-#  OPTIONS --type-in-type #-}

module SR where

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
open import LFP


HContext : Set
HContext = Maybe Seq

closedH : HContext → Bool
closedH (just x) = closedS x
closedH nothing = true

closedH-1 : {y : Context}{x : Formula} → (g : HContext) →  closedH (just (y ⇒ x)) ≡ true
 → closedC y ≡ true
closedH-1 {y} {x} g p with closedF x | closedC y
closedH-1 {y} {x} g () | false | false
closedH-1 {y} {x} g () | true | false
closedH-1 {y} {x} g p | z | true = refl

closedH-2 : {y : Context}{x : Formula} → (g : HContext) →  closedH (just (y ⇒ x)) ≡ true
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
   → Φ ⊢   Γ ⇒ C → Φ ⊢  unit ∷ Γ ⇒ C

  ∧-r  : ∀ {Φ : HContext} {Γ : Context} {A B : Formula}
             → Φ ⊢  Γ ⇒ A → Φ ⊢  Γ ⇒ B → Φ ⊢  Γ ⇒ A ∧ B     
  ∧-l  : ∀ {Φ : HContext} {Γ : Context} {A B C : Formula}
             →   Φ ⊢  A ∷ B ∷ Γ ⇒ C → Φ ⊢  A ∧ B ∷ Γ ⇒ C

  ∨-r₁  : ∀ {Φ : HContext} {Γ : Context} {A B : Formula}
             → Φ ⊢  Γ ⇒ A → Φ ⊢  Γ ⇒ A ∨ B
  ∨-r₂  : ∀ {Φ : HContext} {Γ : Context} {A B : Formula}
             → Φ ⊢ Γ ⇒ B → Φ ⊢  Γ ⇒ A ∨ B
  ∨-l  : ∀ {Φ : HContext} {Γ : Context} {A B C : Formula}
             → Φ ⊢   A ∷ Γ ⇒ C 
             → Φ ⊢   B ∷ Γ ⇒ C 
             → Φ ⊢   A ∨ B ∷ Γ ⇒ C   

  μ-r  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}
             → Φ ⊢  Γ ⇒ substVar (μ A )  A
             → Φ ⊢  Γ ⇒ μ A
  μ-l  : ∀ {Γ : Context} {A : Formula}{C : Formula}
            → just (var ∷  Γ ⇒  C) ⊢ A ∷  Γ ⇒ C
            → closedF C ≡ true
            → closedC Γ ≡ true 
            → nothing ⊢ μ A  ∷  Γ ⇒ C
            
  hyp-use : ∀ {S : Seq } → (just S) ⊢ S


  weakn  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → Φ ⊢ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C

  exchng  : ∀ {Φ : HContext} {Γ Γ' : Context} {A : Formula}{C : Formula}
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



hyp-free : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ Γ ⇒ A → Bool
hyp-free id-axiom = true
hyp-free unit-r = true
hyp-free (unit-l d) = hyp-free d
hyp-free (∧-r d d₁) = hyp-free d & hyp-free d₁
hyp-free (∧-l d) = hyp-free d
hyp-free (∨-r₁ d) = hyp-free d
hyp-free (∨-r₂ d) = hyp-free d
hyp-free (∨-l d d₁) = hyp-free d & hyp-free d₁
hyp-free (μ-r d) = hyp-free d
hyp-free (μ-l d x x₁) = hyp-free d
hyp-free hyp-use = false
hyp-free (weakn d) = hyp-free d
hyp-free (exchng x d) = hyp-free d



var-free-hyp :  {A B : Formula}{Γ Γ' : Context}
 (d : just (var ∷ Γ' ⇒ A) ⊢ Γ ⇒ B)
  → var-freeC Γ ≡ true
  → hyp-free d ≡ true
var-free-hyp id-axiom p = refl
var-free-hyp unit-r p = refl
var-free-hyp (unit-l d) p = var-free-hyp d p
var-free-hyp (∧-r d d₁) p rewrite var-free-hyp d p | var-free-hyp d₁ p = refl
var-free-hyp (∧-l {Γ = Γ}{A = A}{B = B}{C = C} d) p = var-free-hyp d (trans (sym (and-assoc {(var-freeF A)} {(var-freeF B)} {(var-freeC Γ)})) p)
var-free-hyp (∨-r₁ d) p = var-free-hyp d p
var-free-hyp (∨-r₂ d) p = var-free-hyp d p
var-free-hyp (∨-l {Γ = Γ} {A = A}{B = B} d d₁) p rewrite var-free-hyp d (subst (λ R → R & var-freeC Γ ≡ true) (sym (closed-1 (closed-1 p))) (closed-2 p)) | var-free-hyp d₁ ((subst (λ R → R & var-freeC Γ ≡ true) (sym ((closed-2 (closed-1 {var-freeF A & var-freeF B} p)))) (closed-2 p))) = refl
var-free-hyp (μ-r d) p = var-free-hyp d p
var-free-hyp hyp-use ()
var-free-hyp (weakn d) p = var-free-hyp d  (closed-2 p)
var-free-hyp (exchng x d) p = var-free-hyp d (var-free-in p x)


hyp-free-unit :  {A : Formula}{Γ Γ' : Context}
 (d : just (var ∷ Γ' ⇒ A) ⊢ Γ ⇒ unit)
  → (A ≡ unit → ⊥)
  → hyp-free d ≡ true
hyp-free-unit id-axiom p = refl
hyp-free-unit unit-r p = refl
hyp-free-unit (unit-l d) p = hyp-free-unit  d p
hyp-free-unit (∧-l d) p = hyp-free-unit d p
hyp-free-unit (∨-l d d₁) p rewrite hyp-free-unit d p | hyp-free-unit d₁ p = refl
hyp-free-unit hyp-use p = ⊥-elim (p refl)
hyp-free-unit (weakn d) p = hyp-free-unit d p
hyp-free-unit (exchng x d) p = hyp-free-unit d p


open import FormulaExamples

{-
addRaw :  nothing ⊢ NatRaw ∧ NatRaw ∷ [] ⇒ NatRaw
addRaw = ∧-l (μ-l  ((∨-l (unit-l id-axiom) ((μ-r  ((∨-r₂ (hyp-use ))))))) refl refl  )

add : Nat × Nat → Nat
add (a , b) = ⟦ addRaw ⟧ nothing tt ((a , b) , tt)

add-lem1 : Nat2ℕ (add ((s (s z)) , (s (z)) )) ≡ Nat2ℕ ((s ((s (s z)))))
add-lem1 = refl

add-lem : ∀ (x y : Nat) → Nat2ℕ (add (x , y)) ≡ Nat2ℕ x + Nat2ℕ y
add-lem (IN x (inj₁ x₁)) y = refl
add-lem (IN x (inj₂ y₁)) y = cong suc (add-lem (x y₁) y)

----

constNRaw : nothing ⊢ NatRaw ∷ [] ⇒ NatRaw
constNRaw = μ-r  (∨-r₂ (μ-r  (∨-r₁ unit-r)))

constN : Nat → Nat
constN v = ⟦ constNRaw ⟧ nothing tt (v , tt)

constN-lem :  ∀ x → Nat2ℕ (constN x) ≡ 1
constN-lem x = refl

-----

idNatRaw : nothing ⊢ NatRaw ∷ [] ⇒ NatRaw
idNatRaw = μ-l  (∨-l (unit-l (μ-r  (∨-r₁  unit-r))) (μ-r  (∨-r₂ (hyp-use )))) refl refl 

idNat : Nat → Nat
idNat n = ⟦ idNatRaw ⟧ nothing tt (n , tt)

idNat-lem1 : Nat2ℕ (idNat (s (s (s z)))) ≡ 3
idNat-lem1 = refl

idNat-lem : ∀ x →  Nat2ℕ (idNat x) ≡ Nat2ℕ x
idNat-lem (IN x (inj₁ x₁)) = refl
idNat-lem (IN x (inj₂ y)) = cong suc (idNat-lem (x y))

---

dblNatRaw : nothing ⊢ NatRaw ∷ [] ⇒ NatRaw
dblNatRaw = μ-l  (∨-l (unit-l (μ-r  (∨-r₁  unit-r))) (μ-r  (∨-r₂ (μ-r  (∨-r₂ (hyp-use )))))) refl refl 

dblNat : Nat → Nat
dblNat n = ⟦ dblNatRaw ⟧ nothing tt (n , tt)


dblNat-lem1 : Nat2ℕ (dblNat (s (s (s z)))) ≡ 6
dblNat-lem1 = refl

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm zero zero = refl
+-comm zero (suc b) rewrite +-comm b zero = refl
+-comm (suc a) zero rewrite +-comm a zero = refl
+-comm (suc a) (suc b) rewrite +-comm b (suc a) | +-comm a (suc b) | +-comm a b = refl

dblNat-lem : ∀ x →  Nat2ℕ (dblNat x) ≡ Nat2ℕ x * 2
dblNat-lem (IN x (inj₁ x₁)) = refl
dblNat-lem (IN x (inj₂ y)) rewrite dblNat-lem (x y)
  | +-comm (Nat2ℕ (x y)) (suc (Nat2ℕ (x y) + 0))
  | +-comm (Nat2ℕ (x y)) 0  = refl

-----

-}

zz : nothing ⊢ NatRaw ∷ [] ⇒ BoolRaw → Nat → 𝔹
zz prf n = ⟦ prf ⟧  nothing tt (n , tt)


{-# TERMINATING #-} -- or add induction on proof length
zz-lem : {n : Nat} → (d : nothing ⊢ NatRaw ∷ [] ⇒ BoolRaw) →  zz d (s (s (n))) ≡ zz d (s n)
zz-lem (∨-r₁ d) = refl
zz-lem (∨-r₂ d) = refl
zz-lem (weakn d) = refl
zz-lem (exchng herex d) = zz-lem d 
zz-lem (exchng (therex ()) d) 
zz-lem (μ-l (∨-r₁ d) x x₁ ) = refl
zz-lem (μ-l (∨-r₂ d) x x₁ ) = refl
zz-lem (μ-l (∨-l d (∨-r₁ d₁)) x x₁ ) = refl
zz-lem (μ-l (∨-l d (∨-r₂ d₁)) x x₁ ) = refl
zz-lem (μ-l (∨-l d (hyp-use )) x x₁ ) = refl
zz-lem (μ-l (∨-l d (weakn d₁)) x x₁ ) = refl
zz-lem (μ-l (∨-l d (exchng herex d₁)) x x₁ )  = zz-lem (μ-l (∨-l d d₁) x x₁ ) 
zz-lem (μ-l (∨-l d (exchng (therex ()) d₁)) x x₁ ) 
zz-lem (μ-l (weakn d) x x₁ ) = refl
zz-lem (μ-l (exchng herex d) x x₁ ) = zz-lem ((μ-l d x x₁ )) 
zz-lem (μ-l (exchng (therex ()) d) x x₁ ) 


idax-free : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ Γ ⇒ A → Bool
idax-free unit-r = true
idax-free hyp-use = true
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
