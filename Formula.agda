module Formula where

open import Data.Product
open import Data.Sum
open import Function
open import Data.Nat
open import Data.List
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool renaming (_∧_ to _&_; _∨_ to _∣_)
open import Data.Maybe

open import LFP
open import ListIn

infix 25 _∧_
infix 25 _∨_
infix 4 _⇒_

data Formula : Set where
  unit : Formula 
  _∧_  : Formula → Formula → Formula
  _∨_  : Formula → Formula → Formula 
  var  : Formula
  μ    : Formula →  Formula

Context : Set
Context = List Formula

substVar : Formula → Formula  → Formula 
substVar A unit = unit
substVar A (c ∧ c₁) = substVar A c ∧ substVar A c₁
substVar A (c ∨ c₁) = substVar A c ∨ substVar A c₁
substVar A var = A
substVar A (μ B) = μ B


data Seq : Set where
  _⇒_ : Context → Formula → Seq


closedF : Formula → Bool
closedF unit = true
closedF (A ∧ B) = closedF A & closedF B
closedF (A ∨ B) = closedF A & closedF B
closedF var = false
closedF (μ A) = true

closedC : Context → Bool
closedC c = and (Data.List.map closedF c)

closedS : Seq → Bool
closedS (Γ  ⇒ A) = closedF A & closedC Γ


closed-subst : {A B : Formula} → closedF B ≡ true → closedF (substVar B A) ≡ true
closed-subst {unit} {B} p  = refl
closed-subst {A ∧ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
closed-subst {A ∨ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
closed-subst {var} {B} p = p
closed-subst {μ A} {B} p = refl

closed-1 : {a b : Bool} → a & b ≡ true → a ≡ true
closed-1 {false} {b} ()
closed-1 {true} {b} q = refl

closed-2 : {a b : Bool} → a & b ≡ true → b ≡ true
closed-2 {false} {false} ()
closed-2 {true} {false} ()
closed-2 {a} {true}  q = refl


postulate
  and-assoc : {a b c : Bool} → (a & b) & c ≡ a & (b & c)


closedC-1 : {x : Formula} → (g : Context) →  closedC (x ∷ g) ≡ true → closedC g ≡ true
closedC-1 {x} g v with  closedF x
closedC-1 {x} g () | false
closedC-1 {x} g v | true = v

closedC-2 : {x : Formula} → (g : Context) →  closedC (x ∷ g) ≡ true → closedF x ≡ true
closedC-2 {x} g v with  closedF x
closedC-2 {x} g () | false
closedC-2 {x} g v | true = refl


⟦_⟧F  : (A : Formula) → (ρ : Maybe Set) →  Set
⟦ unit ⟧F ρ  = ⊤
⟦ A ∧ B ⟧F ρ  = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ 
⟦ A ∨ B ⟧F ρ  = ⟦ A ⟧F ρ  ⊎ ⟦ B ⟧F ρ
⟦ var ⟧F nothing  = ⊤ -- or must be ⊥?
⟦ var ⟧F  (just x)  = x
⟦ μ A ⟧F _  = Mu λ (X : Set) → ⟦ A ⟧F (just X)


⟦_⟧C : Context →  Maybe Set → Set
⟦ [] ⟧C ρs = ⊤
⟦ A ∷ Γ ⟧C ρs = ⟦ A ⟧F ρs × ⟦ Γ ⟧C  ρs

f-lemm : {ρ : Maybe Set}{A : Formula}(Γ Γ' : Context)
  → A ∈ Γ , Γ' → ⟦ Γ ⟧C ρ  → ⟦ A ⟧F ρ
f-lemm .(_ ∷ G') G' herex v = proj₁ v
f-lemm .(_ ∷ _) .(_ ∷ _) (therex p) v = f-lemm _ _ p (proj₂ v)


G-lemm : {ρ : Maybe Set}{A : Formula}(Γ Γ' : Context)
  → A ∈ Γ , Γ' → ⟦ Γ ⟧C ρ  → ⟦ Γ' ⟧C ρ
G-lemm .(_ ∷ G') G' herex v = proj₂ v
G-lemm .(_ ∷ _) .(_ ∷ _) (therex p) v = proj₁ v , G-lemm _ _ p  (proj₂ v)


⟦_⟧S :  Seq → Maybe Set → Set
⟦ Γ ⇒ A ⟧S ρs = ⟦ Γ ⟧C ρs → ⟦ A ⟧F ρs




wcf-eq :  {ρ₁ ρ₂ : Maybe Set}{C : Formula} → .{p : closedF C ≡ true} → ⟦ C ⟧F ρ₁ ≡ ⟦ C ⟧F ρ₂
wcf-eq {_} {_} {unit} = refl
wcf-eq {ρ₁} {ρ₂} {A ∧ B} {p} rewrite wcf-eq {ρ₁} {ρ₂} {A} {closed-1 p} | wcf-eq {ρ₁} {ρ₂} {B} {closed-2 p} = refl
wcf-eq {ρ₁} {ρ₂} {A ∨ B} {p} rewrite wcf-eq {ρ₁} {ρ₂} {A} {closed-1 p} | wcf-eq {ρ₁} {ρ₂} {B} {closed-2 p} = refl 
wcf-eq {_} {_} {var} {()}
wcf-eq {_} {_} {μ C} = refl


wcc-eq :  {ρ₁ ρ₂ : Maybe Set}{Γ : Context} → .{p : closedC Γ ≡ true} → ⟦ Γ ⟧C ρ₁ ≡ ⟦ Γ ⟧C ρ₂
wcc-eq {Γ = []} {p} = refl
wcc-eq {ρ₁} {ρ₂} {Γ = A ∷ Γ} {p}
 rewrite wcf-eq {ρ₁} {ρ₂} {A} {closedC-2 {A} Γ p}
 | wcc-eq {ρ₁} {ρ₂} {Γ} {closedC-1 {A} Γ p} = refl


substEq : {ρ : Maybe Set} (A : Formula) → {C : Formula} → .{p : closedF C ≡ true} → ⟦ substVar C A  ⟧F ρ ≡ ⟦ A ⟧F (just (⟦ C ⟧F ρ))
substEq unit {p} = refl
substEq {ρ} (A ∧ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
substEq {ρ} (A ∨ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
substEq var {p} = refl
substEq (μ A) {p} = refl



var-freeF : Formula → Bool
var-freeF unit = true
var-freeF (A ∧ B) = var-freeF A & var-freeF B
var-freeF (A ∨ B) = var-freeF A & var-freeF B
var-freeF var = false
var-freeF (μ A) = var-freeF A


var-freeC : Context → Bool
var-freeC [] = true
var-freeC (x ∷ c) = var-freeF x &  var-freeC c


var-free-in : {Γ Γ' : Context}{A : Formula} →  var-freeC Γ ≡ true
 → A ∈ Γ , Γ' → var-freeF A & var-freeC Γ' ≡ true
var-free-in p herex = p
var-free-in {A = A} p (therex {y = y} {xs = xs} {ys = ys} i) with var-free-in (closed-2 p) i
... | q rewrite closed-1 {var-freeF A}  q | closed-1 {var-freeF y} p = closed-2 q



-- module Formula where

-- open import Data.Product
-- open import Data.Sum
-- open import Function
-- open import Data.Nat
-- open import Data.List
-- open import Data.Unit hiding (_≟_)
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Nullary
-- open import Data.Bool renaming (_∧_ to _&_; _∨_ to _∣_)
-- open import Data.Maybe

-- open import LFP
-- open import ListIn

-- infix 25 _∧_
-- infix 25 _∨_
-- infix 4 _⇒_

-- data Formula : Set where
--   unit : Formula
--   Top    : Formula
--   _∧_  : Formula → Formula → Formula
--   _⊗_  : Formula → Formula → Formula  
--   _∨_  : Formula → Formula → Formula 
--   var  : Formula
--   μ    : Formula →  Formula

-- Context : Set
-- Context = List Formula

-- substVar : Formula → Formula  → Formula 
-- substVar A unit = unit
-- substVar A Top = Top
-- substVar A (c ∧ c₁) = substVar A c ∧ substVar A c₁
-- substVar A (c ⊗ c₁) = substVar A c ⊗ substVar A c₁
-- substVar A (c ∨ c₁) = substVar A c ∨ substVar A c₁
-- substVar A var = A
-- substVar A (μ B) = μ B


-- data Seq : Set where
--   _⇒_ : Context → Formula → Seq


-- closedF : Formula → Bool
-- closedF unit = true
-- closedF Top = true
-- closedF (A ∧ B) = closedF A & closedF B
-- closedF (A ⊗ B) = closedF A & closedF B
-- closedF (A ∨ B) = closedF A & closedF B
-- closedF var = false
-- closedF (μ A) = true

-- closedC : Context → Bool
-- closedC c = and (Data.List.map closedF c)

-- closedS : Seq → Bool
-- closedS (Γ  ⇒ A) = closedF A & closedC Γ


-- closed-subst : {A B : Formula} → closedF B ≡ true → closedF (substVar B A) ≡ true
-- closed-subst {unit} {B} p  = refl
-- closed-subst {Top} {B} p  = refl
-- closed-subst {A ∧ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
-- closed-subst {A ⊗ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
-- closed-subst {A ∨ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
-- closed-subst {var} {B} p = p
-- closed-subst {μ A} {B} p = refl

-- closed-1 : {a b : Bool} → a & b ≡ true → a ≡ true
-- closed-1 {false} {b} ()
-- closed-1 {true} {b} q = refl

-- closed-2 : {a b : Bool} → a & b ≡ true → b ≡ true
-- closed-2 {false} {false} ()
-- closed-2 {true} {false} ()
-- closed-2 {a} {true}  q = refl


-- postulate
--   and-assoc : {a b c : Bool} → (a & b) & c ≡ a & (b & c)


-- closedC-1 : {x : Formula} → (g : Context) →  closedC (x ∷ g) ≡ true → closedC g ≡ true
-- closedC-1 {x} g v with  closedF x
-- closedC-1 {x} g () | false
-- closedC-1 {x} g v | true = v

-- closedC-2 : {x : Formula} → (g : Context) →  closedC (x ∷ g) ≡ true → closedF x ≡ true
-- closedC-2 {x} g v with  closedF x
-- closedC-2 {x} g () | false
-- closedC-2 {x} g v | true = refl


-- ⟦_⟧F  : (A : Formula) → (ρ : Maybe Set) →  Set
-- ⟦ unit ⟧F ρ  = ⊤
-- ⟦ Top ⟧F ρ  = ⊤
-- ⟦ A ∧ B ⟧F ρ  = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ
-- ⟦ A ⊗ B ⟧F ρ  = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ 
-- ⟦ A ∨ B ⟧F ρ  = ⟦ A ⟧F ρ  ⊎ ⟦ B ⟧F ρ
-- ⟦ var ⟧F nothing  = ⊤ -- or must be ⊥?
-- ⟦ var ⟧F  (just x)  = x
-- ⟦ μ A ⟧F _  = Mu λ (X : Set) → ⟦ A ⟧F (just X)


-- ⟦_⟧C : Context →  Maybe Set → Set
-- ⟦ [] ⟧C ρs = ⊤
-- ⟦ A ∷ Γ ⟧C ρs = ⟦ A ⟧F ρs × ⟦ Γ ⟧C  ρs

-- f-lemm : {ρ : Maybe Set}{A : Formula}(Γ Γ' : Context)
--   → A ∈ Γ , Γ' → ⟦ Γ ⟧C ρ  → ⟦ A ⟧F ρ
-- f-lemm .(_ ∷ G') G' herex v = proj₁ v
-- f-lemm .(_ ∷ _) .(_ ∷ _) (therex p) v = f-lemm _ _ p (proj₂ v)


-- G-lemm : {ρ : Maybe Set}{A : Formula}(Γ Γ' : Context)
--   → A ∈ Γ , Γ' → ⟦ Γ ⟧C ρ  → ⟦ Γ' ⟧C ρ
-- G-lemm .(_ ∷ G') G' herex v = proj₂ v
-- G-lemm .(_ ∷ _) .(_ ∷ _) (therex p) v = proj₁ v , G-lemm _ _ p  (proj₂ v)


-- ⟦_⟧S :  Seq → Maybe Set → Set
-- ⟦ Γ ⇒ A ⟧S ρs = ⟦ Γ ⟧C ρs → ⟦ A ⟧F ρs




-- wcf-eq :  {ρ₁ ρ₂ : Maybe Set}{C : Formula} → .{p : closedF C ≡ true} → ⟦ C ⟧F ρ₁ ≡ ⟦ C ⟧F ρ₂
-- wcf-eq {_} {_} {unit} = refl
-- wcf-eq {_} {_} {Top} = refl
-- wcf-eq {ρ₁} {ρ₂} {A ∧ B} {p} rewrite wcf-eq {ρ₁} {ρ₂} {A} {closed-1 p} | wcf-eq {ρ₁} {ρ₂} {B} {closed-2 p} = refl
-- wcf-eq {ρ₁} {ρ₂} {A ⊗ B} {p} rewrite wcf-eq {ρ₁} {ρ₂} {A} {closed-1 p} | wcf-eq {ρ₁} {ρ₂} {B} {closed-2 p} = refl
-- wcf-eq {ρ₁} {ρ₂} {A ∨ B} {p} rewrite wcf-eq {ρ₁} {ρ₂} {A} {closed-1 p} | wcf-eq {ρ₁} {ρ₂} {B} {closed-2 p} = refl 
-- wcf-eq {_} {_} {var} {()}
-- wcf-eq {_} {_} {μ C} = refl


-- wcc-eq :  {ρ₁ ρ₂ : Maybe Set}{Γ : Context} → .{p : closedC Γ ≡ true} → ⟦ Γ ⟧C ρ₁ ≡ ⟦ Γ ⟧C ρ₂
-- wcc-eq {Γ = []} {p} = refl
-- wcc-eq {ρ₁} {ρ₂} {Γ = A ∷ Γ} {p}
--  rewrite wcf-eq {ρ₁} {ρ₂} {A} {closedC-2 {A} Γ p}
--  | wcc-eq {ρ₁} {ρ₂} {Γ} {closedC-1 {A} Γ p} = refl


-- substEq : {ρ : Maybe Set} (A : Formula) → {C : Formula} → .{p : closedF C ≡ true} → ⟦ substVar C A  ⟧F ρ ≡ ⟦ A ⟧F (just (⟦ C ⟧F ρ))
-- substEq unit {p} = refl
-- substEq Top {p} = refl
-- substEq {ρ} (A ∧ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
-- substEq {ρ} (A ⊗ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
-- substEq {ρ} (A ∨ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
-- substEq var {p} = refl
-- substEq (μ A) {p} = refl



-- var-freeF : Formula → Bool
-- var-freeF unit = true
-- var-freeF Top = true
-- var-freeF (A ∧ B) = var-freeF A & var-freeF B
-- var-freeF (A ⊗ B) = var-freeF A & var-freeF B
-- var-freeF (A ∨ B) = var-freeF A & var-freeF B
-- var-freeF var = false
-- var-freeF (μ A) = var-freeF A


-- var-freeC : Context → Bool
-- var-freeC [] = true
-- var-freeC (x ∷ c) = var-freeF x &  var-freeC c


-- var-free-in : {Γ Γ' : Context}{A : Formula} →  var-freeC Γ ≡ true
--  → A ∈ Γ , Γ' → var-freeF A & var-freeC Γ' ≡ true
-- var-free-in p herex = p
-- var-free-in {A = A} p (therex {y = y} {xs = xs} {ys = ys} i) with var-free-in (closed-2 p) i
-- ... | q rewrite closed-1 {var-freeF A}  q | closed-1 {var-freeF y} p = closed-2 q
