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



{-# TERMINATING #-} -- or add induction on proof length
zz-lem : {n : Nat} → (d : [] ⊢ NatRaw ∷ [] ⇒ BoolRaw) → cntFree d ≡ true → zz d (s (s (n))) ≡ zz d (s n)
zz-lem (∨-r₁ d) p = refl
zz-lem (∨-r₂ d) p = refl
zz-lem (hyp-use ()) p
zz-lem (contr d) ()
zz-lem (weakn d) p = refl
zz-lem (exchng herex d) p = zz-lem d p
zz-lem (exchng (therex ()) d) p
zz-lem (μ-l (∨-r₁ d) x x₁ x₂) p = refl
zz-lem (μ-l (∨-r₂ d) x x₁ x₂) p = refl
zz-lem (μ-l (∨-l d (∨-r₁ d₁)) x x₁ x₂) p = refl
zz-lem (μ-l (∨-l d (∨-r₂ d₁)) x x₁ x₂) p = refl
zz-lem (μ-l (∨-l d (hyp-use (here refl))) x x₁ x₂) p = refl
zz-lem (μ-l (∨-l d (hyp-use (there ()))) x x₁ x₂) p
zz-lem (μ-l (∨-l d (contr d₁)) x x₁ x₂) p = ⊥-elim (&-comm p)
zz-lem (μ-l (∨-l d (weakn d₁)) x x₁ x₂) p = refl
zz-lem (μ-l (∨-l d (exchng herex d₁)) x x₁ x₂) p  = zz-lem (μ-l (∨-l d d₁) x x₁ x₂) p
zz-lem (μ-l (∨-l d (exchng (therex ()) d₁)) x x₁ x₂) p
zz-lem (μ-l (hyp-use (here ())) x x₁ x₂) p
zz-lem (μ-l (hyp-use (there ())) x x₁ x₂) p
zz-lem (μ-l (contr d) x x₁ x₂) ()
zz-lem (μ-l (weakn d) x x₁ x₂) p = refl
zz-lem (μ-l (exchng herex d) x x₁ x₂) p = zz-lem ((μ-l d x x₁ x₂)) p
zz-lem (μ-l (exchng (therex ()) d) x x₁ x₂) p
