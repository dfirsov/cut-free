{-#  OPTIONS --type-in-type #-}

module MIR2 where

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

postulate
  ∣-1 : ∀ a b → b ≡ true → a ∣ b ≡ true

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



hyp-free : {Φ : HContext}{A B : Formula} → (d : Φ ⊢ A ⇒ B) → Bool
hyp-free id-axiom = true
hyp-free unit-r = true
hyp-free (∧-r d d₁) = hyp-free d & hyp-free d₁
hyp-free (∧-l₁ d) = hyp-free d
hyp-free (∧-l₂ d) = hyp-free d
hyp-free (∨-r₁ d) = hyp-free d
hyp-free (∨-r₂ d) = hyp-free d
hyp-free (∨-l d d₁) = hyp-free d & hyp-free d₁
hyp-free (μ-r d) = hyp-free d
hyp-free (μ-l d x) = hyp-free d
hyp-free hyp-use = false

has-L-rule : {Φ : HContext}{A B : Formula} → (d : Φ ⊢ A ⇒ B) → Bool
has-L-rule id-axiom = false
has-L-rule unit-r = false
has-L-rule (∧-r d d₁) = has-L-rule d ∣ has-L-rule d₁
has-L-rule (∧-l₁ d) = true
has-L-rule (∧-l₂ d) = true
has-L-rule (∨-r₁ d) = has-L-rule d
has-L-rule (∨-r₂ d) = has-L-rule d
has-L-rule (∨-l d d₁) = true
has-L-rule (μ-r d) = has-L-rule d
has-L-rule (μ-l d x) = true
has-L-rule hyp-use = false

has-R-rule : {Φ : HContext}{A B : Formula} → (d : Φ ⊢ A ⇒ B) → Bool
has-R-rule id-axiom = false
has-R-rule unit-r = true
has-R-rule (∧-r d d₁) = true
has-R-rule (∧-l₁ d) = has-R-rule d 
has-R-rule (∧-l₂ d) = has-R-rule d 
has-R-rule (∨-r₁ d) = true
has-R-rule (∨-r₂ d) = true
has-R-rule (∨-l d d₁) = has-R-rule d ∣ has-R-rule d₁
has-R-rule (μ-r d) = true
has-R-rule (μ-l d x) = has-R-rule d
has-R-rule hyp-use = false

nothing-to-Φ : {Φ : HContext}{A B : Formula}
  → (d : nothing ⊢ A ⇒ B)
  → Φ ⊢ A ⇒ B
nothing-to-Φ id-axiom = id-axiom
nothing-to-Φ unit-r = unit-r
nothing-to-Φ (∧-r d d₁) = ∧-r (nothing-to-Φ d) (nothing-to-Φ d₁)
nothing-to-Φ (∧-l₁ d) = ∧-l₁ (nothing-to-Φ d)
nothing-to-Φ (∧-l₂ d) = ∧-l₂ (nothing-to-Φ d)
nothing-to-Φ (∨-r₁ d) = ∨-r₁ (nothing-to-Φ d)
nothing-to-Φ (∨-r₂ d) = ∨-r₂ (nothing-to-Φ d)
nothing-to-Φ (∨-l d d₁) = ∨-l (nothing-to-Φ d) (nothing-to-Φ d₁)
nothing-to-Φ (μ-r d) = μ-r (nothing-to-Φ d)
nothing-to-Φ (μ-l d x) = μ-l d x




hyp-free-weaken : {Φ₁ Φ₂ : HContext}{A B : Formula}
  → (d : Φ₁ ⊢ A ⇒ B)
  → hyp-free d ≡ true
  → Φ₂ ⊢ A ⇒ B
hyp-free-weaken id-axiom pf = id-axiom
hyp-free-weaken unit-r pf = unit-r
hyp-free-weaken (∧-r d d₁) pf
  = ∧-r (hyp-free-weaken d (closed-1 pf))
        (hyp-free-weaken d₁ (closed-2 pf))
hyp-free-weaken (∧-l₁ d) pf = ∧-l₁ (hyp-free-weaken d pf)
hyp-free-weaken (∧-l₂ d) pf = ∧-l₂ (hyp-free-weaken d pf)
hyp-free-weaken (∨-r₁ d) pf = ∨-r₁ (hyp-free-weaken d pf)
hyp-free-weaken (∨-r₂ d) pf = ∨-r₂ (hyp-free-weaken d pf)
hyp-free-weaken (∨-l d d₁) pf
 = ∨-l (hyp-free-weaken d (closed-1 pf))
       (hyp-free-weaken d₁ (closed-2 pf))
hyp-free-weaken (μ-r d) pf = μ-r (hyp-free-weaken d pf)
hyp-free-weaken (μ-l d x) pf = μ-l (hyp-free-weaken d pf) x
hyp-free-weaken hyp-use ()  


substVarWeak : {Φ : HContext}{A B C : Formula}
         → (d : Φ ⊢ A ⇒ C)
         → {pf : closedF C ≡ true}
         → {pf' : hyp-free d ≡ true}
         → Φ ⊢ (substVar (μ B) A) ⇒ C
substVarWeak {A = unit} d = d
substVarWeak {A = A ∧ A₁} id-axiom {pf} {pf'}  = ∧-r (∧-l₁ (substVarWeak {A = A} id-axiom {closed-1 pf} {closed-1 pf'}) ) (∧-l₂ (substVarWeak id-axiom {closed-2 pf} {closed-2 pf'} ))
substVarWeak {A = A ∧ A₁} unit-r = unit-r
substVarWeak {A = A ∧ A₁} (∧-r d d₁) {pf} {pf'} = ∧-r (substVarWeak d {closed-1 pf} {closed-1 pf'}) (substVarWeak d₁ {closed-2 pf} {closed-2 pf'})
substVarWeak {A = A ∧ A₁} (∧-l₁ d) {pf} {pf'} = ∧-l₁ (substVarWeak d {pf} {pf'})
substVarWeak {A = A ∧ A₁} (∧-l₂ d) {pf} {pf'} = ∧-l₂ (substVarWeak d {pf} {pf'}) 
substVarWeak {A = A ∧ A₁} (∨-r₁ d) {pf} {pf'} = ∨-r₁ (substVarWeak d {closed-1 pf} {pf'})
substVarWeak {A = A ∧ A₁} (∨-r₂ d) {pf} {pf'} = ∨-r₂ (substVarWeak d {closed-2 pf} {closed-2 pf'})
substVarWeak {A = A ∧ A₁} (μ-r {A = A'} d) {pf} {pf'} = μ-r (substVarWeak d {closed-subst {A'} refl} {pf'})
substVarWeak {A = A ∨ A₁} id-axiom {pf} {pf'} = ∨-l (∨-r₁ (substVarWeak id-axiom {closed-1 pf} {closed-1 pf'})) (∨-r₂ (substVarWeak id-axiom {closed-2 pf} {closed-2 pf'}))
substVarWeak {A = A ∨ A₁} unit-r = unit-r
substVarWeak {A = A ∨ A₁} (∧-r d d₁) {pf} {pf'} = ∧-r (substVarWeak d {closed-1 pf} {closed-1 pf'}) (substVarWeak d₁ {closed-2 pf} {closed-2 pf'})
substVarWeak {A = A ∨ A₁} (∨-r₁ d) {pf} {pf'} = ∨-r₁ (substVarWeak d {closed-1 pf} {pf'})
substVarWeak {A = A ∨ A₁} (∨-r₂ d) {pf} {pf'} = ∨-r₂ (substVarWeak d {closed-2 pf} {closed-2 pf'})
substVarWeak {A = A ∨ A₁} (∨-l d d₁) {pf} {pf'} = ∨-l (substVarWeak d {pf} {closed-1 pf'}) (substVarWeak d₁ {pf} {closed-2 pf'})
substVarWeak {A = A ∨ A₁} (μ-r {A = A'} d) {pf} {pf'} = μ-r (substVarWeak d {closed-subst {A'} refl} {pf'})
substVarWeak {A = var} id-axiom {()}
substVarWeak {A = var} unit-r {pf} {pf'} = unit-r
substVarWeak {A = var} (∧-r d d₁) {pf} {pf'} = ∧-r (substVarWeak d {closed-1 pf} {closed-1 pf'}) (substVarWeak d₁ {closed-2 pf} {closed-2 pf'})
substVarWeak {A = var} (∨-r₁ d) {pf} {pf'} = ∨-r₁ (substVarWeak d {closed-1 pf} {pf'})
substVarWeak {A = var} (∨-r₂ d) {pf} {pf'} = ∨-r₂ (substVarWeak d {closed-2 pf} {closed-2 pf'})
substVarWeak {A = var} (μ-r {A = A} d) {pf} {pf'} = μ-r (substVarWeak d {closed-subst {A} refl} {pf'})
substVarWeak {A = μ A} d = d
substVarWeak hyp-use {pf} {()} 


svw1 : {Φ : HContext}{A B C : Formula}
         → (d : Φ ⊢ A ⇒ C)
         → {pf : closedF C ≡ true}
         → {pf' : hyp-free d ≡ true}
         → hyp-free d ≡ true
         → hyp-free (substVarWeak {Φ} {A} {B} {C} d {pf} {pf'}) ≡ true
svw1 = {!!}         

substVarWeak3 : {A B C : Formula}
         → (d : (just (var ⇒ C))  ⊢ A ⇒ B)
         → closedF A ≡ true
         → nothing ⊢ A ⇒ B
substVarWeak3 id-axiom p = id-axiom 
substVarWeak3 unit-r p = unit-r
substVarWeak3 (∧-r d d₁) p = ∧-r (substVarWeak3 d p) (substVarWeak3 d₁ p)
substVarWeak3 (∧-l₁ d) p = ∧-l₁ (substVarWeak3 d (closed-1 p)) 
substVarWeak3 (∧-l₂ d) p = ∧-l₂ (substVarWeak3 d (closed-2 p)) 
substVarWeak3 (∨-r₁ d) p = ∨-r₁ (substVarWeak3 d (closed-2 p))
substVarWeak3 (∨-r₂ d) p = ∨-r₂ (substVarWeak3 d (closed-2 p)) 
substVarWeak3 (∨-l d d₁) p = ∨-l (substVarWeak3 d (closed-1 p)) (substVarWeak3 d₁ (closed-2 p))
substVarWeak3 (μ-r d) p = μ-r (substVarWeak3 d p)
substVarWeak3 (μ-l d x) p = μ-l d x
substVarWeak3 hyp-use ()


cutPredicate1 : {Φ1 Φ2 : HContext}{A B C D : Formula}
         → Φ1 ⊢ A ⇒ B
         → Φ2 ⊢ C ⇒ D
         → Bool
cutPredicate1 d1 id-axiom = true
cutPredicate1 d1 unit-r = true
cutPredicate1 d1 (∧-r d2 d3) = cutPredicate1 d1 d2 & cutPredicate1 d1 d3
cutPredicate1 d1 (∧-l₁ d2) = hyp-free d1
cutPredicate1 d1 (∧-l₂ d2) = hyp-free d1
cutPredicate1 d1 (∨-r₁ d2) = cutPredicate1 d1 d2
cutPredicate1 d1 (∨-r₂ d2) = cutPredicate1 d1 d2
cutPredicate1 d1 (∨-l d2 d3) = hyp-free d1
cutPredicate1 d1 (μ-r d2) = cutPredicate1 d1 d2
cutPredicate1 d1 (μ-l d2 x) = hyp-free d1
cutPredicate1 d1 hyp-use = true


cutPredicate2 : {Φ1 Φ2 : HContext}{A B C D : Formula}
         → Φ1 ⊢ A ⇒ B
         → Φ2 ⊢ C ⇒ D
         → Bool
cutPredicate2 id-axiom d2 = true
cutPredicate2 unit-r d2 = hyp-free d2
cutPredicate2 (∧-r d1 d3) d2 = hyp-free d2
cutPredicate2 (∨-r₁ d1) d2 = hyp-free d2
cutPredicate2 (∨-r₂ d1) d2 = hyp-free d2
cutPredicate2 (μ-r d1) d2 = hyp-free d2
cutPredicate2 (∧-l₁ d1) d2 = cutPredicate2 d1 d2
cutPredicate2 (∧-l₂ d1) d2 = cutPredicate2 d1 d2
cutPredicate2 (∨-l d1 d3) d2 = cutPredicate2 d1 d2 & cutPredicate2 d3 d2
cutPredicate2 (μ-l d1 x) (∨-r₁ d2) = cutPredicate2 d1 d2
cutPredicate2 (μ-l d1 x) (∨-r₂ d2) = cutPredicate2 d1 d2
cutPredicate2 (μ-l d1 x) d2 = cutPredicate2 d1 d2
cutPredicate2 hyp-use d2 = true


hfw : {Φ₁ Φ₂ : HContext}{A B : Formula}
  → (d : Φ₁ ⊢ A ⇒ B)
  → (pf : hyp-free d ≡ true)
  → has-R-rule {Φ₂} (hyp-free-weaken d pf) ≡ true
  → has-R-rule d ≡ true
hfw id-axiom pf l = l
hfw unit-r pf l = refl
hfw (∧-r d d₁) pf l = refl
hfw (∧-l₁ d) pf l = hfw d pf l
hfw (∧-l₂ d) pf l = hfw d pf l
hfw (∨-r₁ d) pf l = refl
hfw (∨-r₂ d) pf l = refl
hfw (∨-l d d₁) pf l = {!!}
hfw (μ-r d) pf l = refl
hfw (μ-l d x) pf l = hfw  d pf l
hfw hyp-use () l

wfh : {Φ₁ Φ₂ : HContext}{A B : Formula}
  → (d : Φ₁ ⊢ A ⇒ B)
  → (pf : hyp-free d ≡ true)
  → has-R-rule d ≡ true
  → has-R-rule {Φ₂} (hyp-free-weaken d pf) ≡ true
wfh = {!!}  

hfw2 : {Φ₁ Φ₂ : HContext}{A B : Formula}
  → (d : Φ₁ ⊢ A ⇒ B)
  → (pf : hyp-free d ≡ true)
  → hyp-free {Φ₂} (hyp-free-weaken d pf) ≡ true
hfw2 id-axiom pf = refl
hfw2 unit-r pf = refl
hfw2 (∧-r d d₁) pf = {!!}
hfw2 (∧-l₁ d) pf = {!!}
hfw2 (∧-l₂ d) pf = {!!}
hfw2 (∨-r₁ d) pf = {!!}
hfw2 (∨-r₂ d) pf = {!!}
hfw2 (∨-l d d₁) pf = {!!}
hfw2 (μ-r d) pf = {!!}
hfw2 (μ-l d x) pf = {!!}
hfw2 hyp-use pf = {!!}  



cut : {Φ : HContext}{A B C : Formula}
         → (d1 : Φ ⊢ A ⇒ B)
         → {pf : closedF C ≡ true}
         → (d2 : nothing ⊢ B ⇒ C)
         → {pf'  : has-L-rule d2 ≡ true → hyp-free d1 ≡ true}
         → {pf'' : has-R-rule d1 ≡ true → hyp-free d2 ≡ true}
         → Φ ⊢ A ⇒ C
cut (μ-l d₁ x) {pf} unit-r = unit-r
cut (μ-l d₁ x) {pf} (∨-r₁ d) {pf'} {pf''}
 = ∨-r₁ (cut (μ-l d₁ x) {closed-1 pf} d {pf'} {pf''})
cut (μ-l d₁ x) {pf} (∨-r₂ d) {pf'} {pf''}
 = ∨-r₂ (cut (μ-l d₁ x) {closed-2 pf} d {pf'} {pf''})


cut (μ-l d₁ x) {pf} (∧-l₁ d) {pf'} {pf''} = μ-l (cut (hyp-free-weaken d₁ (pf' refl)) {pf} (∧-l₁ d) {{!!}} {λ q → pf'' (hfw d₁ {!!} q )} ) pf
cut (μ-l d₁ x) {pf} (∧-l₂ d) {pf'} {pf''} = μ-l (cut (hyp-free-weaken d₁ (pf' refl)) {pf} (∧-l₂ d) {{!!}} {λ q → pf'' (hfw d₁ {!!} q )}) pf
cut (μ-l d₁ x) {pf} (∨-l d d₂) {pf'} {pf''} = μ-l (cut (hyp-free-weaken d₁ (pf' refl)) {pf} (∨-l d d₂) {{!!}} {λ q → pf'' (hfw d₁ {!!} q )}) pf
cut (μ-l d₁ x) {pf} (μ-l d x₁) {pf'} {pf''} = μ-l (cut (hyp-free-weaken d₁ (pf' refl)) {pf} (μ-l d x₁) {{!!}} {λ q → pf'' (hfw d₁ {!!} q )}) pf

cut hyp-use (∧-l₁ d₂) {pf'} with pf' refl
... | ()
cut hyp-use (∧-l₂ d₂) {pf'} with pf' refl
... | ()
cut hyp-use (∨-l d₂ d₃) {pf'} with pf' refl
... | ()
cut hyp-use (μ-l d₂ x) {pf'} with pf' refl
... | ()
{- / excluded if d₁ has hyp-use in them -}


-- weaken d₁, weaken d
cut  (μ-r {A = A} d₁) {pf} (μ-l d x) {pf'} {pf''} = cut d₁ {x} (hyp-free-weaken (substVarWeak d {x} {pf'' refl} ) (svw1 d {x} {pf'' refl} (pf'' refl))) {λ _ → pf' refl} {λ q → hfw2 (substVarWeak d) ((svw1 d (pf'' refl)))  }

cut hyp-use id-axiom = hyp-use
cut hyp-use unit-r = unit-r

cut hyp-use {pf} (∨-r₁ d₂) {pf'} = ∨-r₁ (cut hyp-use {closed-1 pf} d₂ {pf'} {λ { () }})
cut hyp-use {pf} (∨-r₂ d₂) {pf'} = ∨-r₂ (cut hyp-use {closed-2 pf} d₂ {pf'} {λ { () }})

cut d₁ id-axiom = d₁
cut d₁ unit-r = unit-r
cut d₁ {pf} (∧-r d₂ d₃) {pf'} {pf''} = ∧-r (cut d₁ {closed-1 pf} d₂ {{!!}} {  λ q → closed-1 (pf'' q) }) (cut d₁ {closed-2 pf} d₃ {{!!}} {λ q → closed-2 (pf'' q)})
cut (∧-r d₁ d₃) {pf} (∧-l₁ d₂) {pf'} {pf''} = cut d₁ {pf} d₂ {{!!}} {λ _ → pf'' refl}
cut (∧-l₁ d₁) {pf} d₂ {pf'} {pf''} = ∧-l₁ (cut d₁ {pf} d₂ {{!!}} {pf''})
cut (∧-l₂ d₁) {pf} d₂ {pf'} {pf''} = ∧-l₂ (cut d₁ {pf} d₂ {{!!}} {pf''})

cut {_} {A} {B} {C} d₁ {pf} (μ-r {A = A'} d₂) {pf'} {pf''} = μ-r (cut d₁ {closed-subst {A'} {μ _} refl} d₂ {pf'} {pf''}) 

cut (∧-r d₁ d₃) {pf} (∧-l₂ d₂) {pf'} {pf''} = cut d₃ {closed-2 pf} d₂ {{!!}} {λ _ → pf'' refl}

cut id-axiom (∧-l₁ d₂) = ∧-l₁ (nothing-to-Φ d₂)
cut id-axiom (μ-l d₂ x ) = μ-l d₂ x
cut id-axiom (∧-l₂ d₂) = ∧-l₂ (nothing-to-Φ d₂)
cut id-axiom {pf} (∨-r₁ d₂) {pf'} {pf''} = nothing-to-Φ (∨-r₁ d₂)

cut unit-r {pf}    (∨-r₁ d₂) {pf'} {pf''} = ∨-r₁ (cut unit-r {closed-1 pf} d₂ {pf'} {pf''})
cut (∧-r d₁ d₃) {pf} (∨-r₁ d₂) {pf'} {pf''} = ∨-r₁ (cut (∧-r d₁ d₃) {closed-1 pf} d₂ {pf'} {pf''})
cut (∨-r₁ d₁) {pf} (∨-r₁ d₂) {pf'} {pf''} = ∨-r₁ (cut (∨-r₁ d₁) {closed-1 pf} d₂ {pf'} {pf''})
cut (∨-r₂ d₁) {pf} (∨-r₁ d₂) {pf'} {pf''} = ∨-r₁ (cut (∨-r₂ d₁) {closed-1 pf} d₂ {pf'} {pf''})
cut (μ-r d₁) {pf} (∨-r₁ d₂) {pf'} {pf''} = ∨-r₁ (cut (μ-r d₁) {closed-1 pf} d₂ {pf'} {pf''})


cut id-axiom {pf} (∨-r₂ d₂) {pf'} {pf''} = nothing-to-Φ (∨-r₂ d₂)
cut unit-r {pf}    (∨-r₂ d₂) {pf'} {pf''} = ∨-r₂ (cut unit-r {closed-2 pf} d₂ {pf'} {pf''})
cut (∧-r d₁ d₃) {pf} (∨-r₂ d₂) {pf'} {pf''} = ∨-r₂ (cut (∧-r d₁ d₃) {closed-2 pf} d₂ {pf'} {pf''})
cut (∨-r₁ d₁) {pf} (∨-r₂ d₂) {pf'} {pf''} = ∨-r₂ (cut (∨-r₁ d₁) {closed-2 pf} d₂ {pf'} {pf''})
cut (∨-r₂ d₁) {pf} (∨-r₂ d₂) {pf'} {pf''} = ∨-r₂ (cut (∨-r₂ d₁) {closed-2 pf} d₂ {pf'} {pf''})
cut (μ-r d₁) {pf} (∨-r₂ d₂) {pf'} {pf''} = ∨-r₂ (cut (μ-r d₁) {closed-2 pf} d₂ {pf'} {pf''})

cut id-axiom (∨-l d₂ d₃) = ∨-l (nothing-to-Φ d₂) (nothing-to-Φ d₃)
cut (∨-r₁ d₁) {pf} (∨-l d₂ d₃) {pf'} {pf''} = cut d₁ {pf} d₂ {{!!}} {λ _ → closed-1 (pf'' refl)}
cut (∨-r₂ d₁) {pf} (∨-l d₂ d₃) {pf'} {pf''} = cut d₁ {pf} d₃ {{!!}} {λ _ → closed-2 (pf'' refl)}
cut (∨-l d d₂) {pf} d₁ {pf'} {pf''} = ∨-l (cut d {pf} d₁ {{!!}} {{!!}}) (cut d₂ {closed-2 pf} d₁ {{!pf'!}} {λ q → pf'' (∣-1  _ _ q)})




