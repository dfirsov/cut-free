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

-- decidable equality
postulate
  _≟f_ : (a b : Formula) → Dec (a ≡ b)


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
HContext = List Seq


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
closedH Φ = and (Data.List.map closedS Φ)


closed-subst : {A B : Formula} → closedF B ≡ true → closedF (substVar B A) ≡ true
closed-subst {unit} {B} p  = refl
closed-subst {A ∧ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
closed-subst {A ∨ B} {C} p rewrite closed-subst {A} {C} p | closed-subst {B} {C} p = refl
closed-subst {var} {B} p = p
closed-subst {μ A} {B} p = refl

closedH-1 : {y : Context}{x : Formula} → (g : HContext) →  closedH ((y ⇒ x) ∷ g) ≡ true
 → closedC y ≡ true
closedH-1 {y} {x} g p with closedF x | closedC y
closedH-1 {y} {x} g () | false | false
closedH-1 {y} {x} g () | true | false
closedH-1 {y} {x} g p | z | true = refl

closedH-2 : {y : Context}{x : Formula} → (g : HContext) →  closedH ((y ⇒ x) ∷ g) ≡ true
 → closedF x ≡ true
closedH-2 {y} {x} g p with closedF x 
closedH-2 {y} {x} g () | false 
closedH-2 {y} {x} g p  | true  = refl

closedH-3 : {y : Context}{x : Formula} → (g : HContext) →  closedH ((y ⇒ x) ∷ g) ≡ true
 → closedH g ≡ true
closedH-3 {y} {x} g p with closedF x | closedC y
closedH-3 {y} {x} g () | false | false
closedH-3 {y} {x} g () | true | false
closedH-3 {y} {x} g () | false | true
closedH-3 {y} {x} g p | true | true = p

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
  μ-l  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → (var ∷  Γ ⇒  C) ∷  Φ  ⊢ A ∷  Γ ⇒ C
            → closedF C ≡ true
            → closedH Φ ≡ true
            → closedC Γ ≡ true 
            → Φ ⊢ μ A  ∷  Γ ⇒ C
            
{- ei saa praegu, F peab olema functor!
  μ-lₚ  : ∀ {Φ : HContext} {Γ : Context} {A C : Formula}
             → Φ ⊢ substVar (μ A )  A ∷ Γ ⇒ C
             → Φ ⊢  μ A ∷ Γ ⇒ C
-}

  hyp-use : ∀ {Φ : HContext }{S : Seq }
     → S ∈ Φ → Φ ⊢ S

  contr  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → Φ ⊢ A ∷ A ∷ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C


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

⟦_⟧H :  HContext → Maybe Set → Set
⟦ [] ⟧H ρs = ⊤
⟦ S ∷ Φ ⟧H ρs  = ⟦ S ⟧S ρs × ⟦ Φ ⟧H ρs


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

wch-eq :  {ρ₁ ρ₂ : Maybe Set}{Φ : HContext} → .{p : closedH Φ ≡ true} → ⟦ Φ ⟧H ρ₁ ≡ ⟦ Φ ⟧H ρ₂
wch-eq {Φ = []} {p} = refl
wch-eq {ρ₁} {ρ₂} {Φ = (Γ ⇒ A) ∷ Φ} {p} 
 rewrite wcf-eq {ρ₁} {ρ₂} {A} {closedH-2 {Γ} {A} Φ p}
 | wcc-eq {ρ₁} {ρ₂} {Γ} {closedH-1 {Γ} {A} Φ p}
 | wch-eq {ρ₁} {ρ₂} {Φ} {closedH-3 {Γ} {A} Φ p} = refl

substEq : {ρ : Maybe Set} (A : Formula) → {C : Formula} → .{p : closedF C ≡ true} → ⟦ substVar C A  ⟧F ρ ≡ ⟦ A ⟧F (just (⟦ C ⟧F ρ))
substEq unit {p} = refl
substEq {ρ} (A ∧ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
substEq {ρ} (A ∨ B) {C} {p} rewrite substEq {ρ} A {C} {p} | substEq {ρ} B {C} {p} = refl
substEq var {p} = refl
substEq (μ A) {p} = refl


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
⟦ μ-l {Γ = Γ} {A =  A} {C = C} c a b z ⟧ ρ v
  = uncurry (Fold λ Y rf rv w →

       subst id (wcf-eq {_} {_} {C} {a}) (⟦ c ⟧ (just Y) ((λ  q → subst id (wcf-eq {_} {_} {C} {a}) (rf (proj₁ q) w) )
                             , subst id (wch-eq {ρ} {just Y}  {_} {b}) v)
                            (rv , subst id (wcc-eq {ρ} {just Y} {Γ} {z}) w)))  
⟦ hyp-use (here refl) ⟧ ρ (a , _) = a
⟦ hyp-use (there x) ⟧ ρ (_ , h) =  ⟦ hyp-use x ⟧ ρ h  
⟦ contr c ⟧ ρ v = λ { (a , g) → ⟦ c ⟧ ρ v (a , a , g) }
⟦ weakn c ⟧ ρ v = λ { (a , g) → ⟦ c ⟧ ρ v g }

⟦ exchng  {Γ = Γ}{Γ' = Γ'} {A = A} p c ⟧ ρ v q =  ⟦ c ⟧ ρ v  (f-lemm  {ρ}  {A} _ _ p q , G-lemm  {ρ}  {A} _ _ p q)  




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


addRaw :  [] ⊢ NatRaw ∧ NatRaw ∷ [] ⇒ NatRaw
addRaw = ∧-l (μ-l  ((∨-l (unit-l id-axiom) ((μ-r  ((∨-r₂ (hyp-use (here refl)))))))) refl refl  refl)

add : Nat × Nat → Nat
add (a , b) = ⟦ addRaw ⟧ nothing tt ((a , b) , tt)

add-lem1 : Nat2ℕ (add ((s (s z)) , (s (z)) )) ≡ Nat2ℕ ((s ((s (s z)))))
add-lem1 = refl

add-lem : ∀ (x y : Nat) → Nat2ℕ (add (x , y)) ≡ Nat2ℕ x + Nat2ℕ y
add-lem (IN x (inj₁ x₁)) y = refl
add-lem (IN x (inj₂ y₁)) y = cong suc (add-lem (x y₁) y)

----

{- multiplication: #contraction -}

----

constNRaw : [] ⊢ NatRaw ∷ [] ⇒ NatRaw
constNRaw = μ-r  (∨-r₂ (μ-r  (∨-r₁ unit-r)))

constN : Nat → Nat
constN v = ⟦ constNRaw ⟧ nothing tt (v , tt)

constN-lem :  ∀ x → Nat2ℕ (constN x) ≡ 1
constN-lem x = refl

-----

idNatRaw : [] ⊢ NatRaw ∷ [] ⇒ NatRaw
idNatRaw = μ-l  (∨-l (unit-l (μ-r  (∨-r₁  unit-r))) (μ-r  (∨-r₂ (hyp-use (here refl))))) refl refl refl

idNat : Nat → Nat
idNat n = ⟦ idNatRaw ⟧ nothing tt (n , tt)

idNat-lem1 : Nat2ℕ (idNat (s (s (s z)))) ≡ 3
idNat-lem1 = refl

idNat-lem : ∀ x →  Nat2ℕ (idNat x) ≡ Nat2ℕ x
idNat-lem (IN x (inj₁ x₁)) = refl
idNat-lem (IN x (inj₂ y)) = cong suc (idNat-lem (x y))

---

dblNatRaw : [] ⊢ NatRaw ∷ [] ⇒ NatRaw
dblNatRaw = μ-l  (∨-l (unit-l (μ-r  (∨-r₁  unit-r))) (μ-r  (∨-r₂ (μ-r  (∨-r₂ (hyp-use (here refl))))))) refl refl refl

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

cntFree : {A : Formula}{Φ : HContext}{Γ : Context} → Φ ⊢ Γ ⇒ A → Bool
cntFree id-axiom = true
cntFree unit-r = true
cntFree (unit-l t) = cntFree t
cntFree (∧-r t t₁) = cntFree t & cntFree t₁
cntFree (∧-l t) = cntFree t
cntFree (∨-r₁ t) = cntFree t
cntFree (∨-r₂ t) = cntFree t
cntFree (∨-l t t₁) = cntFree t & cntFree t₁
cntFree (μ-r  t) = cntFree t
cntFree (μ-l t x x₁ x₂) = cntFree t
cntFree (hyp-use x) = true
cntFree (contr t) = false
cntFree (weakn t) = cntFree t
cntFree (exchng t d ) = cntFree d

μFree : {A : Formula}{Φ : HContext}{Γ : Context} → Φ ⊢ Γ ⇒ A → Bool
μFree id-axiom = true
μFree unit-r = true
μFree (unit-l t) = μFree t
μFree (∧-r t t₁) = μFree t & μFree t₁
μFree (∧-l t) = μFree t
μFree (∨-r₁ t) = μFree t
μFree (∨-r₂ t) = μFree t
μFree (∨-l t t₁) = μFree t & μFree t₁
μFree (μ-r  t) = true
μFree (μ-l t x x₁ x₂) = false
μFree (hyp-use x) = true
μFree (contr t) = μFree t
μFree (weakn t) = μFree t
μFree (exchng t d ) = μFree d


BoolRaw : Formula
BoolRaw = unit ∨ unit

𝔹 : Set
𝔹 = ⟦ BoolRaw  ⟧F nothing

t : 𝔹
t = inj₁ tt

f : 𝔹
f = inj₂ tt


zz : [] ⊢ NatRaw ∷ [] ⇒ BoolRaw → Nat → 𝔹
zz prf n = ⟦ prf ⟧  nothing tt (n , tt)

&-comm : {a : Bool} →  a & false ≡ true → ⊥
&-comm {false} () 
&-comm {true}  () 



fWF : (A : Formula) → Bool
fWF (unit ∨ var) = true
fWF (μ (unit ∨ var))= true
fWF var = true
fWF _ =  false

cWF : (Γ : Context) → Set
cWF [] = ⊤
cWF (A ∷ Γ) = fWF A ≡ true × cWF Γ


ρwf : Maybe Set → Set
ρwf (just X) = X ≡ Nat
ρwf nothing = ⊤

toValF : (ρ : Maybe Set) → ρwf ρ → (A : Formula) → Nat → fWF A ≡ true → ⟦ A ⟧F ρ
toValF (just .Nat) refl unit n ()
toValF (just .Nat) refl  (A ∧ A₁) n ()
toValF (just .Nat) refl (unit ∨ var) n _ = inj₂ n
toValF (just .Nat) refl (_ ∨ _) n prf = {!prf!}
toValF (just .Nat) refl var n prf = n
toValF (just .Nat) refl (μ (unit ∨ var)) n prf = s n
toValF (just .Nat) refl (μ _) = {!!}
toValF nothing tt unit n () 
toValF nothing tt (c ∧ c₁) n ()
toValF nothing tt (unit ∨ var) n _ = inj₂ tt -- can it happen?
toValF nothing tt (_ ∨ _) n = {!!}
toValF nothing tt var n _ = tt -- can it happen
toValF nothing tt (μ (unit ∨ var)) n _ = s n
toValF nothing tt (μ _) n = {!!}


toValC : (ρ : Maybe Set) → ρwf ρ → (Γ : Context) → (n : Nat) → cWF Γ → ⟦ Γ ⟧C ρ
toValC ρ ρwf [] n t = t
toValC ρ ρwf (x ∷ Γ) n t = toValF ρ ρwf x n (proj₁ t) , toValC ρ ρwf Γ n (proj₂ t)

hWF : (Φ : HContext) → Set
hWF [] = ⊤
hWF ((x ⇒ x₁) ∷ []) = cWF x
hWF ((x ⇒ x₁) ∷ x₂ ∷ Φ) = ⊥


sucItAll : {Γ' : Context} → cWF Γ' →  ⟦ Γ' ⟧C (just Nat) → ⟦ Γ' ⟧C (just Nat)
sucItAll {[]} d n = n
sucItAll {(μ (unit ∨ var)) ∷ Γ'} d  (n , n') = s n , sucItAll {Γ'} (proj₂ d) n' 
sucItAll {unit ∨ var ∷ Γ'} d (inj₁ x , n') = inj₂ z , sucItAll {Γ'} (proj₂ d) n' 
sucItAll {unit ∨ var ∷ Γ'} d (inj₂ y , n') = inj₂ (s y) , sucItAll {Γ'} (proj₂ d) n'
sucItAll {var ∷ Γ'} d  (n , n') = s n , sucItAll {Γ'} (proj₂ d) n'
sucItAll {z ∷ Γ'} d  n = n -- impossible

sucItAll' : {Γ' : Context} → cWF Γ' →  ⟦ Γ' ⟧C (just Nat) → Bool
sucItAll' {[]} d tt = true
sucItAll' {μ (unit ∨ var) ∷ Γ'} d (IN x (inj₁ x₁) , n') = false
sucItAll' {μ (unit ∨ var) ∷ Γ'} d (IN x (inj₂ y) , n') = sucItAll' {Γ'} (proj₂ d) n'
sucItAll' {unit ∨ var ∷ Γ'} d (inj₁ x , n') = false
sucItAll' {unit ∨ var ∷ Γ'} d (inj₂ (IN x (inj₁ x₁)) , n') = true
sucItAll' {unit ∨ var ∷ Γ'} d (inj₂ (IN x (inj₂ y)) , n') = sucItAll' {Γ'} (proj₂ d) n'
sucItAll' {var ∷ Γ'} d (IN x (inj₁ x₁) , n') = false
sucItAll' {var ∷ Γ'} d (IN x (inj₂ y) , n') = sucItAll' {Γ'} (proj₂ d) n'
sucItAll' {z ∷ Γ'} d  n = false

Γgood : (Γ : Context)  →  (cn : ⟦ Γ ⟧C (just Nat)) → Bool
Γgood (unit ∨ var ∷ G) (inj₁ x , proj₄) = false
Γgood (unit ∨ var ∷ G) (inj₂ y , proj₄) = Γgood G proj₄
Γgood (x ∷ G) (y , proj₄) = Γgood G proj₄
Γgood [] _ = true


cok : {A : Formula}(Γ Γ' : Context)(cwf1 : cWF Γ) → A ∈ Γ , Γ'
   → cWF Γ'
cok .(_ ∷ G') G' (proj₃ , proj₄) herex = proj₄
cok .(_ ∷ _) .(_ ∷ _) cwf (therex x) = proj₁ cwf , cok _ _ (proj₂ cwf) x

mylemma : {A : Formula}{Γ Γ' : Context}{n : Nat}{cwf1 : cWF Γ} → (x : A ∈ Γ , Γ')
   → G-lemm Γ Γ' x (toValC (just Nat) refl Γ n cwf1)  ≡ (toValC (just Nat) refl Γ' n (cok Γ Γ' cwf1 x))
mylemma {Γ' = []} herex = refl
mylemma {Γ' = x ∷ Γ'} herex = refl
mylemma {A} {Γ} {Γ'}{n} {cwf1} (therex {xs = xs} {ys = ys} x) rewrite mylemma {A} {_} {_} {n} {proj₂ cwf1} x  = refl

fok : {A : Formula}(Γ Γ' : Context) → A ∈ Γ , Γ'
   → cWF Γ → fWF A ≡ true
fok .(_ ∷ G') G'  herex p = proj₁ p
fok .(_ ∷ _) .(_ ∷ _)  (therex x) p = fok _ _  x (proj₂ p)

mylemma' : {A : Formula}{Γ Γ' : Context}{n : Nat}{cwf1 : cWF Γ} → (x : A ∈ Γ , Γ')
   → f-lemm Γ Γ' x (toValC (just Nat) refl Γ n cwf1)  ≡ (toValF (just Nat) refl A n (fok _ _ x cwf1 ))
mylemma' herex = refl
mylemma' {A} {Γ} {Γ'}{n} {cwf1} (therex x) rewrite mylemma' {A} {_} {_} {n} {proj₂ cwf1}  x = refl



-- hyp-free, μ-l free
zz-lem'' : {Γ : Context}{H : HContext}
 → (cwf : cWF Γ)
 → (d :  H ⊢ Γ ⇒ BoolRaw) → (true ≡ true)
 → (φ φ' : ⟦ H ⟧H (just Nat))
 → (cn1 : ⟦ Γ ⟧C (just Nat))
 → (cn2 : ⟦ Γ ⟧C (just Nat))
 → sucItAll cwf cn1 ≡ cn2 -- one suc of other
 → Γgood Γ cn1 ≡ true 
 → ⟦ d ⟧ (just Nat)  φ cn1 ≡ ⟦ d ⟧ (just Nat) φ' cn2
zz-lem'' (() , proj₄) id-axiom p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (unit-l d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (∧-l d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' cwf (∨-r₁ d) p ph1 ph2 cn1 cn2 sprf gprf = refl
zz-lem'' cwf (∨-r₂ d) p ph1 ph2 cn1 cn2 sprf gprf = refl
zz-lem'' cwf (contr {A = unit ∨ var} d) p ph1 ph2 (inj₁ x , proj₄) cn2 sprf ()
zz-lem'' cwf (contr {A = unit ∨ var} d) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) () gprf
zz-lem'' cwf (contr {A = unit ∨ var} d) p ph1 ph2 (inj₂ y , proj₄) (inj₂ .(IN (λ x → x) (inj₂ y)) , .(sucItAll (proj₂ cwf) proj₄)) refl gprf rewrite p
  = zz-lem'' (refl , refl , proj₂ cwf) d p ph1 ph2 (inj₂ y , inj₂ y , proj₄) (inj₂ (s y) , inj₂ (s y) , (sucItAll (proj₂ cwf) proj₄)) refl gprf
zz-lem'' (() , proj₄) (contr {A = unit} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = A ∧ A₁} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = unit ∨ unit} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = unit ∨ (A₁ ∧ A₂)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = unit ∨ (A₁ ∨ A₂)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = unit ∨ μ A₁} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = (A ∧ A₂) ∨ A₁} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = (A ∨ A₂) ∨ A₁} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = var ∨ A₁} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ A ∨ A₁} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (proj₃ , proj₄) (contr {A = var} d) p ph1 ph2 (proj₅ , proj₆) (.(IN (λ x → x) (inj₂ proj₅)) , .(sucItAll proj₄ proj₆)) refl gprf
  = zz-lem''  (refl , refl , proj₄) d refl ph1 ph2 (proj₅ , proj₅ , proj₆) (s proj₅ , s proj₅ , (sucItAll proj₄ proj₆)) refl gprf 
zz-lem'' (() , proj₄) (contr {A = μ unit} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ (A ∧ A₁)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ (unit ∨ unit)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ (unit ∨ (A₁ ∧ A₂))} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ (unit ∨ (A₁ ∨ A₂))} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (proj₃ , proj₄) (contr {A = μ (unit ∨ var)} d) p ph1 ph2 (proj₅ , proj₆) (.(IN (λ x → x) (inj₂ proj₅)) , .(sucItAll proj₄ proj₆)) refl gprf
  = zz-lem'' (refl , refl , proj₄) d refl ph1 ph2 (proj₅ , proj₅ , proj₆) (s proj₅ , s proj₅ , (sucItAll proj₄ proj₆)) refl gprf
zz-lem'' (() , proj₄) (contr {A = μ (unit ∨ μ A₁)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ ((A ∧ A₂) ∨ A₁)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ ((A ∨ A₂) ∨ A₁)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ (var ∨ A₁)} d) p ph1 ph2 cn1 cn2 sprf gprf 
zz-lem'' (() , proj₄) (contr {A = μ (μ A ∨ A₁)} d) p ph1 ph2 cn1 cn2 sprf gprf 
zz-lem'' (() , proj₄) (contr {A = μ var} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₄) (contr {A = μ (μ A)} d) p ph1 ph2 cn1 cn2 sprf gprf
zz-lem'' (() , proj₈) (weakn {A = unit} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = A ∧ A₁} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = unit ∨ unit} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = unit ∨ (A₁ ∧ A₂)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = unit ∨ (A₁ ∨ A₂)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = unit ∨ μ A₁} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = (A ∧ A₂) ∨ A₁} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = (A ∨ A₂) ∨ A₁} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = var ∨ A₁} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = μ A ∨ A₁} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = μ unit} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = μ (A ∧ A₁)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = μ (unit ∨ unit)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = μ (unit ∨ (A₁ ∧ A₂))} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = μ (unit ∨ (A₁ ∨ A₂))} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = μ (unit ∨ μ A₁)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = μ ((A ∧ A₂) ∨ A₁)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = μ ((A ∨ A₂) ∨ A₁)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf
zz-lem'' (() , proj₈) (weakn {A = μ (var ∨ A₁)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = μ (μ A ∨ A₁)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = μ var} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' (() , proj₈) (weakn {A = μ (μ A)} d) p ph1 ph2 (proj₃ , proj₄) (proj₅ , proj₆) sprf gprf 
zz-lem'' cwf (weakn {A = unit ∨ var} d) p ph1 ph2 (inj₁ x , proj₄) (proj₅ , proj₆) sprf ()

zz-lem'' cwf (weakn {A = unit ∨ var} d) p ph1 ph2 (inj₂ y , proj₄) (.(inj₂ (IN (λ x → x) (inj₂ y))) , .(sucItAll (proj₂ cwf) proj₄)) refl gprf = zz-lem'' (proj₂ cwf) d refl ph1 ph2 proj₄ _ refl gprf
zz-lem'' cwf (weakn {A = var} d) p ph1 ph2 (proj₃ , proj₄) (.(IN (λ x → x) (inj₂ proj₃)) , .(sucItAll (proj₂ cwf) proj₄)) refl gprf = zz-lem'' (proj₂ cwf) d refl ph1 ph2 proj₄ ((sucItAll (proj₂ cwf) proj₄)) refl gprf
zz-lem'' cwf (weakn {A = μ (unit ∨ var)} d) p ph1 ph2 (proj₃ , proj₄) (.(IN (λ x → x) (inj₂ proj₃)) , .(sucItAll (proj₂ cwf) proj₄)) refl gprf = zz-lem'' (proj₂ cwf) d refl ph1 ph2 proj₄ ((sucItAll (proj₂ cwf) proj₄)) refl gprf

zz-lem'' cwf (exchng x d) p ph1 ph2 cn1 cn2 sprf gprf = zz-lem'' ({!!} , {!!}) d p ph1 ph2 (f-lemm   _ _ x cn1 , G-lemm _ _ x cn1) ((f-lemm   _ _ x cn2 , G-lemm _ _ x cn2)) {!!} {!!}


zz-lem'' (proj₃ , proj₆) (∨-l {A = unit} {var} d d₁) p ph1 ph2 (inj₁ x , proj₄) _ sprf ()
zz-lem'' (() , proj₆) (∨-l {A = unit} {unit} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {B ∧ B₁} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {B ∨ B₁} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {μ B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = A ∧ A₁} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = A ∨ A₁} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = var} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = μ A} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₁ x₁ , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {unit} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {B ∧ B₁} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {B ∨ B₁} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {μ B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf 
zz-lem'' (() , proj₆) (∨-l {A = A ∧ A₁} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf 
zz-lem'' (() , proj₆) (∨-l {A = A ∨ A₁} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf 
zz-lem'' (() , proj₆) (∨-l {A = var} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf 
zz-lem'' (() , proj₆) (∨-l {A = μ A} {B} d d₁) p ph1 ph2 (inj₁ x , proj₄) (inj₂ y , proj₅) sprf gprf
zz-lem'' cwf (∨-l {A = unit} {var} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) () gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {unit} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {B ∧ B₁} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {B ∨ B₁} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = unit} {μ B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = A ∧ A₁} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = A ∨ A₁} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf
zz-lem'' (() , proj₆) (∨-l {A = var} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf 
zz-lem'' (() , proj₆) (∨-l {A = μ A} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₁ x , proj₅) sprf gprf
zz-lem'' cwf (∨-l {A = unit} {var} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ .(IN (λ x → x) (inj₂ y))
  , .(sucItAll (proj₂ cwf) proj₄)) refl gprf
     = zz-lem'' (refl , proj₂ cwf) d₁ p ph1 ph2 (y , proj₄) (s y , (sucItAll (proj₂ cwf) proj₄)) refl gprf
zz-lem'' (() , proj) (∨-l {A = unit} {unit} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 
zz-lem'' (() , proj) (∨-l {A = unit} {B ∧ B₁} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 
zz-lem'' (() , proj) (∨-l {A = unit} {B ∨ B₁} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 
zz-lem'' (() , proj) (∨-l {A = unit} {μ B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 
zz-lem'' (() , proj) (∨-l {A = A ∧ A₁} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 
zz-lem'' (() , proj) (∨-l {A = A ∨ A₁} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 
zz-lem'' (() , proj) (∨-l {A = var} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 
zz-lem'' (() , proj) (∨-l {A = μ A} {B} d d₁) p ph1 ph2 (inj₂ y , proj₄) (inj₂ y₁ , proj₅) sprf gprf 


zz-lem'' cwf (μ-l  d x x₁ x₂) p ph1 ph2 (IN x₃ x₄ , proj₄) cn2 sprf gprf = {!x₄!}
zz-lem'' cwf (hyp-use x) p ph1 ph2 cn1 cn2 sprf gprf = {!!}




-- hyp-full juhtum
zz-lem : {Γ Γ' : Context}{n : Nat}
 → (cwf' : cWF Γ')   
 → (hwf : hWF ((Γ' ⇒ BoolRaw) ∷ [])) 
 → (d :  ((Γ' ⇒ BoolRaw) ∷ []) ⊢ Γ ⇒ BoolRaw) → (true ≡ true)
 → (φ : ⟦ ((Γ' ⇒ BoolRaw) ∷ []) ⟧H (just Nat))
 → (cn1 : ⟦ Γ ⟧C (just Nat)) 
 → (cn2 : ⟦ Γ' ⟧C (just Nat))
 → ⟦ d ⟧ (just Nat)  φ cn1 ≡ (proj₁ φ) cn2
zz-lem  cwf' hwf (μ-l d x x₁ x₂) p φ = {!!}
zz-lem  cwf' hwf id-axiom p φ cn1 cn2 = {!!} -- no way
zz-lem  cwf' hwf (∨-r₁ d) p φ = {!!}
zz-lem  cwf' hwf (∨-r₂ d) φ = {!!}

zz-lem {n = n} cwf' hwf (unit-l d) p φ (proj₃ , proj₄) cn2
   rewrite p = zz-lem {n = n} cwf' cwf' d p φ proj₄ cn2
zz-lem {n = n}  cwf' hwf (∧-l d) p φ cn1 cn2
   = zz-lem {n = n} cwf' cwf' d refl φ ( proj₁ (proj₁ cn1) ,  proj₂ (proj₁ cn1) , (proj₂ cn1)) cn2
zz-lem {Γ = .(A ∨ B) ∷ Γ} {Γ'} {n}  cwf' hwf (∨-l {A = A} {B = B} d d₁) p φ (inj₁ x , proj₄) cn2 = zz-lem {A ∷ Γ} {Γ'} {n} cwf' cwf' d refl φ (x , proj₄) cn2  

zz-lem {Γ = .(A ∨ B) ∷ Γ} {Γ'} {n} cwf' hwf (∨-l {A = A} {B = B} d d₁) p φ (inj₂ y , proj₄) cn2 = zz-lem {B ∷ Γ} {Γ'} {n} cwf' cwf' d₁ refl φ (y , proj₄) cn2  
zz-lem  cwf' hwf (hyp-use (here refl)) p φ cn1 cn2 = {!!}
zz-lem  cwf' hwf (hyp-use (there ())) φ
zz-lem  {n = n} cwf' hwf (contr d) p φ cn1 cn2 = zz-lem {n = n}  cwf' cwf' d refl  _ (proj₁ cn1 , proj₁ cn1 , proj₂ cn1) cn2
zz-lem {n = n}  cwf' hwf (weakn d) p φ cn1 cn2 = zz-lem {n = n}   cwf'  cwf' d refl  _ (proj₂ cn1) cn2
zz-lem {n = n}  cwf' hwf (exchng x d) p φ cn1 cn2 = zz-lem {n = n}  cwf' cwf' d refl φ ({!!} , {!!}) cn2




mutual
  zz-lem' : {Γ  : Context}{n : Nat}
   → (cwf : cWF Γ)
    → {x : Γgood Γ (toValC (just Nat) refl Γ n cwf ) ≡ true    }
   → (d :  [] ⊢ Γ ⇒ BoolRaw) → (true ≡ true)
   → ⟦ d ⟧ (just Nat) tt (toValC (just Nat) refl Γ n cwf ) ≡ ⟦ d ⟧ (just Nat) tt (toValC (just Nat) refl Γ (s n) cwf)
  zz-lem' (() , cwf) id-axiom p 
  zz-lem' (() , cwf) (unit-l d) p
  zz-lem' (()  , cwf) (∧-l c) 
  zz-lem' cwf (∨-r₁ d) p = refl
  zz-lem' cwf (∨-r₂ d) p = refl
  zz-lem' {(.(unit ∨ var) ∷ Γ)} {IN x (inj₁ x₁)} cwf {xx}  (∨-l {A = unit} {var} d d₁)  p with  zz-lem' {var ∷ Γ} {IN x (inj₁ x₁)} (refl , proj₂ cwf) {xx}  d₁ refl
  ... | o  rewrite o = refl
  zz-lem' {(.(unit ∨ var) ∷ Γ)} {IN x (inj₂ y)} cwf {xx} (∨-l {A = unit} {var} d d₁) p with  zz-lem' {var ∷ Γ} {IN x (inj₂ y)} (refl , proj₂ cwf) {xx}  d₁ refl
  ... | o rewrite o = refl
  zz-lem' (() , cwf) (∨-l {A = unit} {unit} d d₁) p 
  zz-lem' (() , cwf) (∨-l {A = unit} {B ∧ B₁} d d₁) p
  zz-lem' (() , cwf) (∨-l {A = unit} {B ∨ B₁} d d₁) p
  zz-lem' (() , cwf) (∨-l {A = unit} {μ B} d d₁) p 
  zz-lem' (() , cwf) (∨-l {A = A ∧ A₁} {B} d d₁) p 
  zz-lem' (() , cwf) (∨-l {A = A ∨ A₁} {B} d d₁) p
  zz-lem' (() , cwf) (∨-l {A = var} {B} d d₁) p 
  zz-lem' (() , cwf) (∨-l {A = μ A} {B} d d₁) p   

  zz-lem' {.(μ (unit ∨ var)) ∷ Γ} {n = n} (prf , cwf) {xx} (μ-l {A = unit ∨ var} d x x₁ x₂) p =  zz-lem'' (refl , cwf) d  refl _ _  _ _ {!refl!}  {!xx!}

  zz-lem' (() , cwf) (μ-l {A = unit} d x x₁ x₂) p 
  zz-lem' (() , cwf) (μ-l {A = A ∧ A₁} d x x₁ x₂) p
  zz-lem' (() , cwf) (μ-l {A = unit ∨ unit} d x x₁ x₂) p 
  zz-lem' (() , cwf) (μ-l {A = unit ∨ (A₁ ∧ A₂)} d x x₁ x₂) p
  zz-lem' (() , cwf) (μ-l {A = unit ∨ (A₁ ∨ A₂)} d x x₁ x₂) p

  zz-lem' (() , cwf) (μ-l {A = unit ∨ μ A₁} d x x₁ x₂) p
  zz-lem' (() , cwf) (μ-l {A = (A ∧ A₂) ∨ A₁} d x x₁ x₂) p
  zz-lem' (() , cwf) (μ-l {A = (A ∨ A₂) ∨ A₁} d x x₁ x₂) p
  zz-lem' (() , cwf) (μ-l {A = var ∨ A₁} d x x₁ x₂) p 
  zz-lem' (() , cwf) (μ-l {A = μ A ∨ A₁} d x x₁ x₂) p 
  zz-lem' (() , cwf) (μ-l {A = var} d x x₁ x₂) p 
  zz-lem' (() , cwf) (μ-l {A = μ A} d x x₁ x₂) p 

  zz-lem' cwf (hyp-use ())
  zz-lem' {Γ} {n} cwf {xx} (contr {A = A} d) p with zz-lem' {A ∷ Γ} {n}  (proj₁ cwf , proj₁ cwf , proj₂ cwf) {{!!}} d refl
  ... | o rewrite o = refl
  zz-lem' {Γ} {n} cwf {xx} (weakn {A = A} d) p rewrite p with zz-lem' {n = n} (proj₂ cwf) {{!!}} d refl
  ... | o rewrite o = refl
  zz-lem' {Γ} {n} cwf {xx} (exchng {Γ' = Γ'} {A = A} x d) p
    rewrite mylemma {A} {Γ} {Γ'} {n} {cwf} x
    | mylemma {A} {Γ} {Γ'} {s n} {cwf} x
    | mylemma' {A} {Γ} {Γ'} {n} {cwf} x
    | mylemma' {A} {Γ} {Γ'} {s n} {cwf} x
    with zz-lem' {Γ = A ∷ Γ'} {n} (fok _ _ x cwf , cok _ _ cwf x) {{!!}} d refl
  ... | o rewrite o =  refl

