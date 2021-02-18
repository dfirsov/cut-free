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

-- hyp-free
zz-lem'' : {Γ Γ' : Context}{H : HContext}{n : Nat}
 → (cwf : cWF Γ)
 → (d :  H ⊢ Γ ⇒ BoolRaw) → (true ≡ true)
 → (φ φ' : ⟦ H ⟧H (just Nat))
 → ⟦ d ⟧ (just Nat)  φ (toValC (just Nat) refl Γ  n cwf) ≡ ⟦ d ⟧ (just Nat) φ' ((toValC (just Nat) refl Γ  (s n) cwf))
zz-lem'' (() , proj₄) id-axiom p ph1 ph2
zz-lem'' (() , proj₄) (unit-l d) p ph1 ph2
zz-lem'' (() , proj₄) (∧-l d) p ph1 ph2
zz-lem'' cwf (∨-r₁ d) p ph1 ph2 = refl
zz-lem'' cwf (∨-r₂ d) p ph1 ph2 = refl
zz-lem'' cwf (∨-l {A = unit} {B = var} d d₁) p ph1 ph2 = zz-lem'' (refl , proj₂ cwf) d₁ refl ph1 ph2

zz-lem'' cwf (∨-l d d₁) p ph1 ph2 = {!!}
zz-lem'' cwf (μ-l d x x₁ x₂) p ph1 ph2 = {!!}
zz-lem'' cwf (hyp-use x) p ph1 ph2 = {!!}
zz-lem'' cwf (contr d) p ph1 ph2 = {!!}
zz-lem'' cwf (weakn d) p ph1 ph2 = {!!}
zz-lem'' cwf (exchng x d) p ph1 ph2 = {!!}

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
   → (d :  [] ⊢ Γ ⇒ BoolRaw) → (true ≡ true)
   → ⟦ d ⟧ (just Nat) tt (toValC (just Nat) refl Γ n cwf ) ≡ ⟦ d ⟧ (just Nat) tt (toValC (just Nat) refl Γ (s n) cwf)
  zz-lem' cwf id-axiom = {!!}
  zz-lem' cwf (unit-l d) = {!!}
  zz-lem' cwf (∧-l id-axiom) = {!!}
  zz-lem' cwf (∧-l (unit-l d)) = {!!}
  zz-lem' cwf (∧-l (∧-l d)) = {!!}
  zz-lem' cwf (∧-l (∨-r₁ d)) = {!!}
  zz-lem' cwf (∧-l (∨-r₂ d)) = {!!}
  zz-lem' cwf (∧-l (∨-l d d₁)) = {!!}
  zz-lem' cwf (∧-l (μ-l d x x₁ x₂)) = {!!}
  zz-lem' cwf (∧-l (hyp-use x)) = {!!}
  zz-lem' cwf (∧-l (contr d)) = {!!}
  zz-lem' cwf (∧-l (weakn d)) = {!!}
  zz-lem' cwf (∧-l (exchng x d)) = {!!}
  zz-lem' cwf (∨-r₁ d) = {!!}
  zz-lem' cwf (∨-r₂ d) = {!!}
  zz-lem' cwf (∨-l d d₁) = {!!}
  zz-lem' {.(μ (unit ∨ var) ∷ [])} {IN x₃ (inj₁ tt)} cwf (μ-l {.[]} {[]} {unit ∨ var} {.(unit ∨ unit)} d x x₁ x₂) p   with zz-lem {unit ∨ var ∷ []} {var ∷ []} {(IN (λ x₄ → x₄) (inj₂ (IN x₃ (inj₁ tt))))}  cwf (refl , tt) d refl ((λ q →
          Fold
          (λ Y rf rv w →
             ⟦ d ⟧ (just Y) ((λ q₁ → rf (proj₁ q₁) w) , tt) (rv , w))
          (proj₁ q) (proj₂ cwf))
       , tt) {!!} {!!}
    | zz-lem {unit ∨ var ∷ []} {var ∷ []}  {IN x₃ (inj₁ tt)} cwf cwf  d refl ((λ q →
          Fold
          (λ Y rf rv w →
             ⟦ d ⟧ (just Y) ((λ q₁ → rf (proj₁ q₁) w) , tt) (rv , w))
          (proj₁ q) (proj₂ cwf))
       , tt)  {!!} {!!}
  ... | o1 | o2   = {!!} -- refl
    
  zz-lem' {.(μ (unit ∨ var) ∷ [])} {IN x₃ (inj₂ y)} cwf (μ-l {.[]} {[]} {unit ∨ var} {.(unit ∨ unit)} d x x₁ x₂) p with zz-lem {unit ∨ var ∷ []} {var ∷ []} {(IN (λ x₄ → x₄) (inj₂ (IN x₃ (inj₂ y))))} cwf (refl , tt) d refl ((λ q →
          Fold
          (λ Y rf rv w →
             ⟦ d ⟧ (just Y) ((λ q₁ → rf (proj₁ q₁) w) , tt) (rv , w))
          (proj₁ q) (proj₂ cwf)) , tt)
        | zz-lem {unit ∨ var ∷ []} {var ∷ []} {IN x₃ (inj₂ y)}  cwf (refl , tt) d refl ((λ q →
          Fold
          (λ Y rf rv w →
             ⟦ d ⟧ (just Y) ((λ q₁ → rf (proj₁ q₁) w) , tt) (rv , w))
          (proj₁ q) (proj₂ cwf))
       , tt)
  ... | o1 | o2 = {!!} -- refl

  zz-lem' cwf (μ-l d x x₁ x₂) p = {!!}

  zz-lem' cwf (hyp-use x) = {!!}
  zz-lem' cwf (contr d) = {!!}
  zz-lem' cwf (weakn d) = {!!}
  zz-lem' cwf (exchng x d) = {!!}

     


