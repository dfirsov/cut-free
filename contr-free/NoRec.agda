{-#  OPTIONS --type-in-type #-}

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

infix 25 _∧_
infix 25 _∨_
infix 4 _⇒_
infix 3 _⊢_


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


HContext : Set
HContext = ⊤


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

closedH : HContext → Bool
closedH _ = true



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

closedC-1 : {x : Formula} → (g : Context) →  closedC (x ∷ g) ≡ true → closedC g ≡ true
closedC-1 {x} g v with  closedF x
closedC-1 {x} g () | false
closedC-1 {x} g v | true = v

closedC-2 : {x : Formula} → (g : Context) →  closedC (x ∷ g) ≡ true → closedF x ≡ true
closedC-2 {x} g v with  closedF x
closedC-2 {x} g () | false
closedC-2 {x} g v | true = refl



--HContext : Set
--HContext = ⊤

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
             → Φ ⊢ A ∷ Γ ⇒ C 
             → Φ ⊢ B ∷ Γ ⇒ C 
             → Φ ⊢ A ∨ B ∷ Γ ⇒ C   

  μ-r  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}
             → Φ ⊢ Γ ⇒ substVar (μ A)  A
             → Φ ⊢ Γ ⇒ μ A
             
  μ-l  : ∀ {Γ : Context} {A : Formula}{C : Formula}
            → tt ⊢ A ∷ Γ ⇒ C
            → closedF C ≡ true
            → closedC Γ ≡ true 
            → tt ⊢ μ A  ∷  Γ ⇒ C
{-            
  hyp-use : ∀ {S : Seq } → (just S) ⊢ S
-}

  weakn  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → Φ ⊢ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C

  exchng  : ∀ {Φ : HContext} {Γ Γ' : Context} {A : Formula}{C : Formula}
            → A ∈ Γ , Γ'
            → Φ ⊢ A ∷ Γ' ⇒ C   
            → Φ ⊢ Γ ⇒ C         



data Mu (F : Set → Set) :  Set where
  IN : ∀ {X : Set} → (X → Mu F) → F X → Mu F

In : {F : Set → Set} → F (Mu F) → Mu F
In m = IN id m

Fold : {F : Set → Set}{C : Set} → ((Y : Set) → (Y → C) → F Y → C) → Mu F  → C
Fold {F} alg (IN {X} f v) = alg X (Fold alg ∘ f) v 

MuF2G : {F G : Set → Set } → (∀ (Y : Set) → F Y → G Y) →  Mu F → Mu G
MuF2G {F} {G} conv mf = Fold ( λ X f v → IN {G} f (conv  X v)) mf

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

⟦_⟧H :  HContext → Set
⟦ _ ⟧H  = ⊤





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



⟦_⟧ : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ (Γ ⇒ A) → (ρ : Maybe Set)
  → ⟦ Γ ⟧C ρ → ⟦ A ⟧F ρ
⟦ id-axiom ⟧ ρ v = proj₁ v
⟦ unit-r ⟧ ρ v = tt
⟦ unit-l d ⟧ ρ v = ⟦ d ⟧ ρ (proj₂ v)
⟦ ∧-r d d₁ ⟧ ρ v = ⟦ d ⟧ ρ v , ⟦ d₁ ⟧ ρ v
⟦ ∧-l d ⟧ ρ v = ⟦ d ⟧ ρ  (proj₁ (proj₁ v) , proj₂ (proj₁ v) , proj₂ v)
⟦ ∨-r₁ d ⟧ ρ v = inj₁ (⟦ d ⟧ ρ v) 
⟦ ∨-r₂ d ⟧ ρ v = inj₂ (⟦ d ⟧ ρ v)
⟦ ∨-l d d₁ ⟧ ρ (inj₁ a , Γ) = ⟦ d ⟧ ρ (a , Γ)
⟦ ∨-l d d₁ ⟧ ρ (inj₂ b , Γ) = ⟦ d₁ ⟧ ρ (b , Γ)
⟦ μ-r {A = A} d ⟧ ρ v = In (subst id  (substEq A {μ A} {refl}) (⟦ d ⟧ ρ v) )
⟦ μ-l {Γ = Γ} {C = C} d x x₁ ⟧ ρ (IN x₂ x₃ , proj₄) = subst id (wcf-eq {_} {_} {C} {x}) (⟦ d ⟧  _ (x₃ , subst id (wcc-eq {_} {_} {Γ} {x₁}) proj₄))
⟦ weakn d ⟧ ρ v = ⟦ d ⟧  ρ (proj₂ v)
⟦ exchng  {Γ = Γ}{Γ' = Γ'} {A = A} p c ⟧ ρ v = ⟦ c ⟧ ρ (f-lemm  {ρ}  {A} _ _ p v , G-lemm  {ρ}  {A} _ _ p v)



{- all functions from finite domain are here -}

BoolRaw : Formula
BoolRaw = unit ∨ unit

𝔹 : Set
𝔹 = ⟦ BoolRaw ⟧F nothing

t : 𝔹
t = inj₁ tt

f : 𝔹
f = inj₂ tt

not𝔹-F : tt ⊢ BoolRaw ∷ [] ⇒ BoolRaw
not𝔹-F = ∨-l (∨-r₂  unit-r) (∨-r₁ unit-r)

not𝔹 : 𝔹 → 𝔹
not𝔹 b = ⟦ not𝔹-F ⟧ nothing (b , tt)

not𝔹-l₁ : not𝔹 t ≡ f
not𝔹-l₁ = refl

not𝔹-l₂ : not𝔹 f ≡ t
not𝔹-l₂ = refl


--

NatRaw : Formula 
NatRaw =  μ (unit ∨ var)  
 
Nat : Set
Nat = ⟦ NatRaw ⟧F  nothing

z : Nat
z = In (inj₁ tt)

s : Nat → Nat
s n = In (inj₂ n)

Nat2ℕ : Nat → ℕ
Nat2ℕ (IN f (inj₁ tt)) = 0
Nat2ℕ (IN f (inj₂ y)) = suc (Nat2ℕ (f y))

ℕ2Nat : ℕ → Nat
ℕ2Nat zero = z
ℕ2Nat (suc n) = s (ℕ2Nat n)


-- plus 1 is expressible 

addone : tt ⊢ NatRaw ∷ [] ⇒ NatRaw
addone = μ-r (∨-r₂ id-axiom)

qq : ⟦ addone ⟧ nothing (s z , tt) ≡ s (s z)
qq = refl





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
  charfs :  (d : tt ⊢ NatRaw ∷ [] ⇒ unit ∨ NatRaw) → {pf : idax-free d ≡ false} → (b : Nat) → Σ[ b₁ ∈ ℕ ]  Nat2ℕ (In (⟦ d ⟧ nothing  (b , tt))) ≡ b₁ + Nat2ℕ b
  charfs (∨-r₁ d) {pf} b rewrite charf-natraw-unit d with pf
  ... | ()
  charfs (∨-r₂ d) {pf} b with charf' d {pf} b
  ... |  (p1 , p2) = suc p1 , cong suc p2
  charfs (μ-l d x x₁) {pf} b rewrite charf-unitvar-A d with pf
  ... | ()
  charfs (weakn d) {pf} b rewrite charf-[]-A d with pf
  ... | ()
  charfs (exchng herex d) {pf} b = charfs d {pf} b 
  charfs (exchng (therex ()) d) {pf} b

  charf' :  (d : tt ⊢ NatRaw ∷ [] ⇒ NatRaw) → {pf : idax-free d ≡ false} → (b : Nat) → Σ[ b₁ ∈ ℕ ]  Nat2ℕ (⟦ d ⟧ nothing  (b , tt)) ≡ b₁ + Nat2ℕ b
  charf' id-axiom b = 0 , refl
  charf' (μ-r (∨-r₁ d)) {pf} b  rewrite charf-natraw-unit d with pf
  ... | () 
  charf' (μ-r (∨-r₂ d)) {pf} b with charf' d {pf} b
  charf' (μ-r (∨-r₂ d)) {pf} b | proj₃ , proj₄ = suc proj₃ , cong suc proj₄
  charf' (μ-r (μ-l d x x₁)) {pf} b  rewrite charf-unitvar-A d with pf
  ... | ()
  charf' (μ-r (weakn d)) {pf} b rewrite charf-[]-A d with pf
  ... | ()
  charf' (μ-r (exchng herex (∨-r₁ d))) {pf} b rewrite charf-natraw-unit d with pf
  ... | () 
  charf' (μ-r (exchng herex (∨-r₂ d))) {pf} b with charf' d {pf} b
  ... | (p1 , p2) = suc p1 , cong suc p2
  charf' (μ-r (exchng herex (μ-l d x x₁))) {pf} b rewrite charf-unitvar-A d with pf
  ... | () 
  charf' (μ-r (exchng herex (weakn d)))  {pf} b rewrite charf-[]-A d with pf
  ... | ()
  charf' (μ-r (exchng herex (exchng herex d))) {pf} b = charfs d {pf} b
  charf' (μ-r (exchng herex (exchng (therex ()) d))) b
  charf' (μ-r (exchng (therex ()) d)) b
  charf' (μ-l d x x₁) {pf} b rewrite charf-unitvar-A d with pf
  ... | () 
  charf' (weakn (μ-r (∨-r₁ unit-r))) {()} b
  charf' (weakn (μ-r (∨-r₁ (exchng () d)))) b
  charf' (weakn (μ-r (∨-r₂ (μ-r (∨-r₁ unit-r))))) {()} b
  charf' (weakn (μ-r (∨-r₂ (μ-r (∨-r₁ (exchng () d)))))) b
  charf' (weakn (μ-r (∨-r₂ (μ-r (∨-r₂ d))))) {pf} b rewrite charf-[]-A d with pf
  ... | ()
  charf' (weakn (μ-r (∨-r₂ (μ-r (exchng () d))))) b
  charf' (weakn (μ-r (∨-r₂ (exchng () d)))) b
  charf' (weakn (μ-r (exchng () d))) b
  charf' (weakn (exchng () d)) b
  charf' (exchng herex d) {pf} b = charf' d {pf} b
  charf' (exchng (therex ()) d) b



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
  charf7 (∨-r₂ d) {pf} b rewrite charf d {pf} b = refl
  charf7 (μ-l d x x₁) b = charf5 d b
  charf7 (weakn d) b = refl
  charf7 (exchng herex d) {pf} b = charf7 d {pf} b
  charf7 (exchng (therex ()) d) b

  charf :  (d : tt ⊢ NatRaw ∷ [] ⇒ NatRaw) → {pf : idax-free d ≡ true} → (b : Nat) →  ⟦ d ⟧ nothing  (s b , tt) ≡ ⟦ d ⟧ nothing  (s (s b) , tt)
  charf id-axiom {()} b
  charf (μ-r (∨-r₁ d)) b =  refl
  charf (μ-r (∨-r₂ d)) {pf} b rewrite charf d {pf}  b = refl
  charf (μ-r (μ-l d x x₁)) b rewrite charf5  d b =  refl
  charf (μ-r (weakn (∨-r₁ d))) b = refl
  charf (μ-r (weakn (∨-r₂ d))) b = refl
  charf (μ-r (weakn (exchng () d))) b
  charf (μ-r (exchng herex (∨-r₁ d))) b = refl
  charf (μ-r (exchng herex (∨-r₂ d))) {pf} b rewrite charf d {pf} b = refl
  charf (μ-r (exchng herex (μ-l d x x₁))) b rewrite charf5 d b = refl
  charf (μ-r (exchng herex (weakn d))) b = refl
  charf (μ-r (exchng herex (exchng herex d))) {pf} b rewrite charf7 d  {pf}  b = refl

  charf (μ-r (exchng herex (exchng (therex ()) d))) b
  charf (μ-r (exchng (therex ()) d)) b

  charf (μ-l d x x₁) b = charf2  d b
  charf (weakn (μ-r (∨-r₁ d))) b =  refl
  charf (weakn (μ-r (∨-r₂ d))) b =  refl
  charf (weakn (μ-r (exchng () d))) b
  charf (weakn (exchng () d)) b
  charf (exchng herex d) {pf} b = charf d {pf} b
  charf (exchng (therex ()) d) b


