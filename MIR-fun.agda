{-#  OPTIONS --type-in-type #-}

module MIR-fun where


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


HContext : Set
HContext = Maybe Seq

closedH : HContext → Bool
closedH (just x) = closedS x
closedH nothing = true

closedH-1 : {y : Context}{x : Formula} → (g : HContext) → closedH (just (y ⇒ x)) ≡ true
 → closedC y ≡ true
closedH-1 {y} {x} g p with closedF x | closedC y
closedH-1 {y} {x} g () | false | false
closedH-1 {y} {x} g () | true  | false
closedH-1 {y} {x} g p  | z     | true = refl

closedH-2 : {y : Context}{x : Formula} → (g : HContext) → closedH (just (y ⇒ x)) ≡ true
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
    → Φ ⊢ Γ ⇒ C → Φ ⊢ unit ∷ Γ ⇒ C

  ∧-r  : ∀ {Φ : HContext}{Γ : Context}{A B : Formula}
             → Φ ⊢  Γ ⇒ A → Φ ⊢ Γ ⇒ B → Φ ⊢ Γ ⇒ A ∧ B     
  ∧-l  : ∀ {Φ : HContext}{Γ : Context}{A B C : Formula}
             → Φ ⊢  A ∷ B ∷ Γ ⇒ C → Φ ⊢ A ∧ B ∷ Γ ⇒ C
  
  ∨-r₁  : ∀ {Φ : HContext}{Γ : Context}{A B : Formula}
             → Φ ⊢ Γ ⇒ A → Φ ⊢ Γ ⇒ A ∨ B
  ∨-r₂  : ∀ {Φ : HContext}{Γ : Context}{A B : Formula}
             → Φ ⊢ Γ ⇒ B → Φ ⊢ Γ ⇒ A ∨ B
  ∨-l  : ∀ {Φ : HContext}{Γ : Context}{A B C : Formula}
             → Φ ⊢ A ∷ Γ ⇒ C 
             → Φ ⊢ B ∷ Γ ⇒ C 
             → Φ ⊢ A ∨ B ∷ Γ ⇒ C   

  μ-r  : ∀ {Φ : HContext}{Γ : Context}{A : Formula}
             → Φ ⊢ Γ ⇒ substVar (μ A) A
             → Φ ⊢ Γ ⇒ μ A

  μ-l  : ∀ {Γ : Context}{A : Formula}{C : Formula}{Φ : HContext}
            → just (var ∷ Γ ⇒ C) ⊢ A ∷  Γ ⇒ C
            → closedF C ≡ true -- can remove?
            → closedC Γ ≡ true 
            → Φ ⊢ μ A ∷ Γ ⇒ C -- in SingleRec this line is: nothing ⊢ μ A  ∷  Γ ⇒ C

  hyp-use : ∀ {S : Seq} → (just S) ⊢ S

  weakn  : ∀ {Φ : HContext}{Γ : Context}{A : Formula}{C : Formula}
            → Φ ⊢ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C

  exchng  : ∀ {Φ : HContext}{Γ Γ' : Context}{A : Formula}{C : Formula}
            → A ∈ Γ , Γ'
            → Φ ⊢ A ∷ Γ' ⇒ C   
            → Φ ⊢ Γ ⇒ C

  cut : {Φ : HContext}{A : Context}{B C : Formula} → Φ ⊢ A ⇒ B → nothing ⊢ B ∷ [] ⇒ C → Φ ⊢ A ⇒ C


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

⟦ cut A B ⟧ ρ v g = ⟦ B ⟧ ρ tt (⟦ A ⟧ ρ v g , tt)




hyp-free : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ Γ ⇒ A → Bool
hyp-free id-axiom = true
hyp-free unit-r = true
hyp-free (unit-l d) = hyp-free d
hyp-free (∧-r d d₁) = hyp-free d & hyp-free d₁
hyp-free (cut d d₁) = hyp-free d & hyp-free d₁
hyp-free (∧-l d) = hyp-free d
hyp-free (∨-r₁ d) = hyp-free d
hyp-free (∨-r₂ d) = hyp-free d
hyp-free (∨-l d d₁) = hyp-free d & hyp-free d₁
hyp-free (μ-r d) = hyp-free d
hyp-free (μ-l d x x₁) = hyp-free d
hyp-free hyp-use = false
hyp-free (weakn d) = hyp-free d
hyp-free (exchng x d) = hyp-free d

isJust : HContext → Bool
isJust (just x) = true
isJust nothing = false


notRaw : nothing ⊢ BoolRaw ∷ [] ⇒ BoolRaw
notRaw = ∨-l (∨-r₂ unit-r) (∨-r₁ unit-r)

oddity : nothing ⊢ NatRaw ∷ [] ⇒ BoolRaw
oddity = μ-l (∨-l (∨-r₁ unit-r) (cut hyp-use notRaw)) refl refl

odd1  : ⟦ oddity ⟧ nothing  tt  (z , tt) ≡ inj₁ tt
odd1 = refl

odd2  : ⟦ oddity ⟧ nothing  tt  (s z , tt) ≡ inj₂ tt
odd2 = refl

odd3  : ⟦ oddity ⟧ nothing  tt  (s (s z) , tt) ≡ inj₁ tt
odd3 = refl


μBoolRaw : Formula
μBoolRaw = μ (unit ∨ unit)

μBool : Set
μBool = ⟦ μBoolRaw ⟧F nothing

μf : μBool
μf = In (inj₁ tt)

μt : μBool
μt = In (inj₂ tt)

WeirdRaw : Formula
WeirdRaw = μ (unit ∨ (μBoolRaw ∧ var))

Weird : Set
Weird = ⟦ WeirdRaw ⟧F nothing

wb : Weird
wb = In (inj₁ tt)

ws : Weird → μBool → Weird
ws w μb = In (inj₂ (μb , w))

prependRaw : nothing ⊢ WeirdRaw ∧ μBoolRaw ∷ [] ⇒ WeirdRaw
prependRaw = ∧-l (μ-l (∨-l (exchng (therex herex) (μ-r (∨-r₂ (∧-r id-axiom (μ-r (∨-r₁ unit-r) ))))) (∧-l (μ-r (∨-r₂ (∧-r id-axiom (weakn hyp-use)))))) refl refl)

revRaw1 : just (var ∷ [] ⇒ WeirdRaw) ⊢ μBoolRaw ∷ var ∷ [] ⇒ WeirdRaw ∧ μBoolRaw
revRaw1 = ∧-r (weakn hyp-use) id-axiom

reverseRaw : nothing ⊢ WeirdRaw ∷ [] ⇒ WeirdRaw 
reverseRaw = μ-l (∨-l (μ-r (∨-r₁ unit-r)) (∧-l (cut revRaw1 prependRaw)  )) refl refl

headRaw : nothing ⊢ WeirdRaw ∷ [] ⇒ μBoolRaw 
headRaw = μ-l (∨-l (μ-r (∨-r₁ unit-r)) (∧-l id-axiom)) refl refl

sepFunc : nothing ⊢ WeirdRaw ∷ [] ⇒ μBoolRaw
sepFunc = cut reverseRaw  headRaw

sepFunc' : nothing ⊢ μBoolRaw ∷ [] ⇒ BoolRaw
sepFunc' = μ-l id-axiom refl refl

ss : nothing ⊢ WeirdRaw ∷ [] ⇒ BoolRaw
ss = cut sepFunc sepFunc'



--  brr : (d : nothing ⊢ WeirdRaw ∷ [] ⇒ BoolRaw) → ⟦ d ⟧ nothing  tt  (ws (ws wb μf) μt , tt) ≡ ⟦ d ⟧ nothing  tt  (ws (ws wb μt) μt , tt)
hod1 :  ⟦ ss ⟧ nothing  tt  (ws (ws wb μf) μt , tt) ≡ inj₁ tt
hod1 = refl

hod2 :  ⟦ ss ⟧ nothing  tt  (ws (ws wb μt) μt , tt) ≡ inj₂ tt
hod2 = refl


