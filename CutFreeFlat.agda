{-#  OPTIONS --type-in-type #-}

open import Data.Empty

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

infix 25 _∧_
infix 25 _∨_
infix 4 _⇒_
infix 3 _⊢_

--infix 5 _or_


mutual

 data Formula : Set where
   unit : Formula 
   _∧_  : Formula → Formula → Formula
   _∨_  : Formula → Formula → Formula 
   var  : Formula
   μ    : (c : Formula) →  μ? c ≡ false → v? c ≡ true → Formula

 v? : Formula → Bool
 v? unit = false
 v? (c ∧ c₁) = v? c ∣ v? c₁
 v? (c ∨ c₁) = v? c ∣ v? c₁
 v? var = true
 v? (μ _ _ _) = false

 μ? : Formula → Bool
 μ? unit = false
 μ? (c ∧ c₁) = μ? c ∣ μ? c₁
 μ? (c ∨ c₁) = μ? c ∣ μ? c₁
 μ? var = false
 μ? (μ _ _ _) = true






Context : Set
Context = List Formula


substVar : Formula → Formula  → Formula 
substVar A unit = unit
substVar A (c ∧ c₁) = substVar A c ∧ substVar A c₁
substVar A (c ∨ c₁) = substVar A c ∨ substVar A c₁
substVar A var = A
substVar A (μ c r d) = μ c r d



data Seq : Set where
  _⇒_ : Context → Formula → Seq


HContext :  Set
HContext = List Seq



closed : Formula → Bool
closed unit = true
closed (A ∧ B) = closed A & closed B
closed (A ∨ B) = closed A & closed B
closed var = false
closed (μ A x _) = true



closedC : Context → Bool
closedC c = and (Data.List.map closed c)

closedS : Seq → Bool
closedS (Γ  ⇒ A) = closed A & closedC Γ

closedH : HContext → Bool
closedH Φ = and (Data.List.map closedS Φ)

closedH-1 : {y : Context}{x : Formula} → (g : HContext) →  closedH ((y ⇒ x) ∷ g) ≡ true → closedC y ≡ true
closedH-1 {y} {x} g p with closed x | closedC y
closedH-1 {y} {x} g () | false | false
closedH-1 {y} {x} g () | true | false
closedH-1 {y} {x} g p | z | true = refl

closedH-2 : {y : Context}{x : Formula} → (g : HContext) →  closedH ((y ⇒ x) ∷ g) ≡ true → closed x ≡ true
closedH-2 {y} {x} g p with closed x 
closedH-2 {y} {x} g () | false 
closedH-2 {y} {x} g p  | true  = refl


closedH-3 : {y : Context}{x : Formula} → (g : HContext) →  closedH ((y ⇒ x) ∷ g) ≡ true → closedH g ≡ true
closedH-3 {y} {x} g p with closed x | closedC y
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
closedC-1 {x} g v with  closed x
closedC-1 {x} g () | false
closedC-1 {x} g v | true = v

closedC-2 : {x : Formula} → (g : Context) →  closedC (x ∷ g) ≡ true → closed x ≡ true
closedC-2 {x} g v with  closed x
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
             → (prf : μ? A ≡ false)
             → (prf2 : v? A ≡ true)
             → Φ ⊢  Γ ⇒ substVar (μ A prf prf2)  A
             → Φ ⊢  Γ ⇒ μ A prf prf2
             
  μ-l  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → (prf : μ? A ≡ false)
            → (prf2 : v? A ≡ true)
            → (var ∷  Γ ⇒  C) ∷  Φ  ⊢ A ∷  Γ ⇒ C
            → closed C ≡ true
            → closedH Φ ≡ true
            → closedC Γ ≡ true
            → Φ ⊢ μ A prf prf2 ∷  Γ ⇒ C

  hyp-use : ∀ {Φ : HContext }{S : Seq }
     → S ∈ Φ → Φ ⊢ S

  contr  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → Φ ⊢ A ∷ A ∷ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C


  weakn  : ∀ {Φ : HContext} {Γ : Context} {A : Formula}{C : Formula}
            → Φ ⊢ Γ ⇒ C
            → Φ ⊢ A ∷ Γ ⇒ C

  exchng  : ∀ {Φ : HContext} {Γ Γ₁ Γ₂ : Context} {A : Formula}{C : Formula}
            → Γ ≡  Γ₁ ++ Γ₂
            → Φ ⊢ Γ₁ ++ A ∷ Γ₂ ⇒ C
            → Φ ⊢ A ∷ Γ₁ ++ Γ₂ ⇒ C            


open import Data.Product
open import Data.Sum
open import Function

data Mu (F : Set → Set) :  Set where
  IN : ∀ {X : Set} → (X → Mu F) → F X → Mu F

In : {F : Set → Set} → F (Mu F) → Mu F
In m = IN id m



Fold : {F : Set → Set}{C : Set} → ((Y : Set) → (Y → C) → F Y → C) → Mu F  → C
Fold {F} alg (IN {X} f v) = alg X (Fold alg ∘ f) v 

OK : (A : Formula) → (ρ : Maybe Set) → Set
OK A ρ = (closed A ≡ true → ρ ≡ nothing) × (ρ ≡ nothing → closed A ≡ true)

⟦_⟧F  : (A : Formula) → (ρ : Maybe Set) →  Set
⟦ unit ⟧F ρ  = ⊤
⟦ A ∧ B ⟧F ρ  = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ 
⟦ A ∨ B ⟧F ρ  = ⟦ A ⟧F ρ  ⊎ ⟦ B ⟧F ρ
⟦ var ⟧F nothing  = ⊤ -- or must be ⊥?
⟦ var ⟧F  (just x)  = x
⟦ μ A prf q ⟧F (just x)  = Mu λ (X : Set) → ⟦ A ⟧F (just X)
⟦ μ A prf q ⟧F nothing  = Mu λ (X : Set) → ⟦ A ⟧F (just X)



⟦_⟧c : Context →  Maybe Set → Set
⟦ [] ⟧c ρs = ⊤
⟦ A ∷ Γ ⟧c ρs = ⟦ A ⟧F ρs × ⟦ Γ ⟧c  ρs


⟦_⟧s :  Seq → Maybe Set → Set
⟦ Γ ⇒ A ⟧s ρs = ⟦ Γ ⟧c ρs → ⟦ A ⟧F ρs

⟦_⟧H :  HContext → Maybe Set → Set
⟦ [] ⟧H ρs = ⊤
⟦ S ∷ Φ ⟧H ρs  = ⟦ S ⟧s ρs × ⟦ Φ ⟧H ρs





MuF2G : {F G : Set → Set } → (∀ (Y : Set) → F Y → G Y) →  Mu F → Mu G
MuF2G {F} {G} conv mf = Fold ( λ X f v → IN {G} f (conv  X v)) mf


weaken : {Y : Set} → (C : Formula) → ⟦ C ⟧F (just Y) → ⟦ C ⟧F nothing
weaken unit  = id
weaken (A ∧ B)  (v₁ , v₂) = weaken A  v₁  , weaken B  v₂
weaken (A ∨ B)  (inj₁ a) = inj₁ (weaken A  a)
weaken (A ∨ B)  (inj₂ b) = inj₂ (weaken B  b)
weaken var  v =  tt
weaken (μ C x v) = id


weakenC : {X : Set} → (Γ : Context) → closedC Γ ≡ true → ⟦ Γ ⟧c (just X) → ⟦ Γ ⟧c  nothing
weakenC [] p v = v
weakenC (x ∷ g) p (proj₃ , proj₄) = weaken x proj₃ , weakenC  g (closedC-1 {x} g p)  proj₄

weaken2 : {Y X : Set} → (C : Formula) → closed C ≡ true → ⟦ C ⟧F (just X) → ⟦ C ⟧F  (just Y)
weaken2 unit = λ x x₁ → x₁
weaken2 (A ∧ B) v (a , b) = weaken2 A  (closed-1 v)  a , weaken2 B (closed-2 v) b
weaken2 (A ∨ B) v (inj₁ a) = inj₁ (weaken2 A (closed-1 v) a)
weaken2 (A ∨ B) v (inj₂ b) = inj₂ (weaken2 B (closed-2 v) b)
weaken2 var ()
weaken2 (μ C x x₁) = λ x₂ → id


weaken2C : {Y X : Set} → (Γ : Context) → closedC Γ ≡ true → ⟦ Γ ⟧c (just X) → ⟦ Γ ⟧c  (just Y)
weaken2C [] p v = v
weaken2C (x ∷ g) p (proj₃ , proj₄) = weaken2 x (closedC-2 {x} g p) proj₃ , weaken2C  g (closedC-1 {x} g p)  proj₄

weaken2H : {Y X : Set} → (Φ : HContext) → closedH Φ ≡ true → ⟦ Φ ⟧H (just X) → ⟦ Φ ⟧H  (just Y)
weaken2H [] r v = tt
weaken2H ((x ⇒ x₁) ∷ C) r (a , b) = (λ z → weaken2 x₁ (closedH-2 {x} {x₁} C r) (a (weaken2C x (closedH-1 {x} {x₁} C r) z))) , weaken2H C (closedH-3 {x} {x₁} C r) b

sF : {Y : Set} → (C : Formula) → closed C ≡ true →  ⟦ C ⟧F nothing → ⟦ C ⟧F (just Y)
sF unit z v = v
sF (A ∧ B) z (a , b) = sF A (closed-1 z) a , sF B (closed-2 z) b
sF (A ∨ B) z (inj₁ a) = inj₁ (sF A (closed-1 z) a)
sF (A ∨ B) z (inj₂ b) = inj₂ (sF B (closed-2 z) b)
sF var () v
sF (μ C x w) v z  = z

sC : {Y : Set} → (Γ : Context) → closedC Γ ≡ true →  ⟦ Γ ⟧c nothing → ⟦ Γ ⟧c (just Y)
sC [] p v = v
sC (x ∷ c) p (A , As) = sF x (closedC-2 {x} c p) A , sC c (closedC-1 {x} c p) As


sH : {Y : Set} → (Φ : HContext) → closedH Φ ≡ true →  ⟦ Φ ⟧H nothing → ⟦ Φ ⟧H (just Y)
sH [] p v = v
sH ((x ⇒ x₁) ∷ c) p (a , As) = (λ z → sF x₁ (closedH-2 {x} {x₁} c p) (a (weakenC x (closedH-1 {x} {x₁} c p) z))) , sH c (closedH-3 {x} {x₁} c p) As




substEq : (A : Formula) → {B : Formula} → closed B ≡ true →  ⟦ substVar B A  ⟧F nothing →  ⟦ A ⟧F (just (⟦ B ⟧F nothing))
substEq unit p v = v
substEq (A ∧ A₁) p (v , w) = substEq A p v , substEq A₁ p w
substEq (A ∨ A₁) p (inj₁ x) = inj₁ (substEq A p x)
substEq (A ∨ A₁) p (inj₂ y) = inj₂ (substEq A₁ p y)
substEq var {unit} p  v = v
substEq var {B ∧ B₁} p  (v , w) = v , w
substEq var {B ∨ B₁} p (inj₁ x) = inj₁ x
substEq var {B ∨ B₁} p (inj₂ y) = inj₂ y
substEq var {var} ()
substEq var {μ B x x₁} p v =  v
substEq (μ A x x₁) p v = v 

{-  -}
⟦_⟧ : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ (Γ ⇒ A) → (ρs : Maybe Set)    → ⟦ Φ ⟧H ρs →  ⟦ Γ ⟧c ρs → ⟦ A ⟧F ρs
⟦ id-axiom ⟧ ρs v = λ { (x , _) → x }
⟦ unit-r ⟧ ρs v = λ _ → tt
⟦ unit-l c ⟧ ρs v = λ { (a , b) → ⟦ c ⟧ ρs v b  }
⟦ ∧-r A B ⟧ ρs v = λ φ → ⟦ A ⟧ ρs v φ ,  ⟦ B ⟧ ρs v φ
⟦ ∧-l A ⟧ ρs v = λ  { ((a , b) , c) → ⟦ A ⟧ ρs v (a , b , c ) }
⟦ ∨-r₁ {A = A} c ⟧ ρs v = λ g →  inj₁ (⟦ c ⟧ ρs v g)
⟦ ∨-r₂ {B = B} c ⟧ ρs v = λ g → inj₂ (⟦ c ⟧ ρs v g)
⟦ ∨-l {A = A} {B = B} {C = C} a b ⟧ ρs v = λ { (inj₁ a' , g) → ⟦ a ⟧ ρs v  (a' , g) ; (inj₂ b' , g) → ⟦ b ⟧ ρs v  (b' , g) }

⟦ μ-r {A = A} prf prf2 c ⟧ (just x) v = λ xs → In let z = ⟦ c ⟧ (just x) v xs in substEq A {μ A prf prf2} refl (weaken {x} (substVar (μ A prf prf2) A) z)
⟦ μ-r {A = A}  prf prf2 c ⟧ nothing v = λ xs → In let z = (⟦ c ⟧ nothing v xs) in substEq A {(μ A prf prf2)} refl z

⟦ μ-l {A =  A} {C = C} prf prf2  c a b z ⟧ (just x) v   = uncurry (Fold λ Y recf recv w → let z = ⟦ c ⟧ (just Y) ((λ { (q1 , q2) → weaken2 C a (recf q1 w) }) , weaken2H  _ b  v)  (recv , weaken2C  _ z w ) in weaken2 C a z )
⟦ μ-l {Φ = Φ}{Γ = Γ}{C = C} prf prf2 c a b z ⟧ nothing v    =  uncurry (Fold λ Y recf recv w →  let z  = ⟦ c ⟧ (just Y) ((λ { (q1 , q2) → sF C a  (recf q1 (weakenC Γ  z q2)) }) , sH _ b v) (recv , sC _ z w) in weaken C z)

⟦ hyp-use (here refl) ⟧ ρs (a , _) = a
⟦ hyp-use (there x) ⟧ ρs (_ , h) =  ⟦ hyp-use x ⟧ ρs h  
⟦ contr c ⟧ ρs v = λ { (a , g) → ⟦ c ⟧ ρs v (a , a , g) }
⟦ weakn c ⟧ ρs v = λ { (a , g) → ⟦ c ⟧ ρs v g }
⟦ exchng {Γ₁ = Γ₁} refl c ⟧ ρs v q = {!Γ !}




NatRaw : Formula 
NatRaw =  μ (unit ∨ var)  refl refl


Nat : Set
Nat = ⟦ NatRaw  ⟧F  nothing

z : Nat
z = In (inj₁ tt)

s : Nat → Nat
s n = In (inj₂ n)

Nat2ℕ : Nat → ℕ
Nat2ℕ (IN f (inj₁ tt)) = 0
Nat2ℕ (IN f (inj₂ y)) = suc (Nat2ℕ (f y))


addRaw :  [] ⊢ NatRaw ∧ NatRaw ∷ [] ⇒ NatRaw
addRaw = ∧-l (μ-l refl refl ((∨-l (unit-l id-axiom) ((μ-r refl refl ((∨-r₂ (hyp-use (here refl)))))))) refl refl  refl)

add : Nat × Nat → Nat
add (a , b) = ⟦ addRaw ⟧ nothing tt ((a , b) , tt)

add-lem1 : Nat2ℕ (add ((s (s z)) , (s (z)) )) ≡ Nat2ℕ ((s ((s (s z)))))
add-lem1 = refl

add-lem : ∀ (x y : Nat) → Nat2ℕ (add (x , y)) ≡ Nat2ℕ x + Nat2ℕ y
add-lem (IN x (inj₁ x₁)) y = refl
add-lem (IN x (inj₂ y₁)) y = cong suc (add-lem (x y₁) y)

----

constNRaw : [] ⊢ NatRaw ∷ [] ⇒ NatRaw
constNRaw = μ-r refl refl (∨-r₂ (μ-r refl refl (∨-r₁ unit-r)))

constN : Nat → Nat
constN v = ⟦ constNRaw ⟧ nothing tt (v , tt)

constN-lem :  ∀ x → Nat2ℕ (constN x) ≡ 1
constN-lem x = refl

-----

idNatRaw : [] ⊢ NatRaw ∷ [] ⇒ NatRaw
idNatRaw = μ-l refl refl (∨-l (unit-l (μ-r refl refl (∨-r₁  unit-r))) (μ-r refl refl (∨-r₂ (hyp-use (here refl))))) refl refl refl

idNat : Nat → Nat
idNat n = ⟦ idNatRaw ⟧ nothing tt (n , tt)

idNat-lem1 : Nat2ℕ (idNat (s (s (s z)))) ≡ 3
idNat-lem1 = refl

idNat-lem : ∀ x →  Nat2ℕ (idNat x) ≡ Nat2ℕ x
idNat-lem (IN x (inj₁ x₁)) = refl
idNat-lem (IN x (inj₂ y)) = cong suc (idNat-lem (x y))

---


dblNatRaw : [] ⊢ NatRaw ∷ [] ⇒ NatRaw
dblNatRaw = μ-l refl refl (∨-l (unit-l (μ-r refl refl (∨-r₁  unit-r))) (μ-r refl refl (∨-r₂ (μ-r refl refl (∨-r₂ (hyp-use (here refl))))))) refl refl refl

dblNat : Nat → Nat
dblNat n = ⟦ dblNatRaw ⟧ nothing tt (n , tt)


dblNat-lem1 : Nat2ℕ (dblNat (s (s (s z)))) ≡ 6
dblNat-lem1 = refl

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm zero zero = refl
+-comm zero (suc b) rewrite +-comm b zero = refl
+-comm (suc a) zero rewrite +-comm a zero = refl
+-comm (suc a) (suc b) rewrite +-comm b (suc a) | +-comm a (suc b) | +-comm a b = refl

dblNat-lem : ∀ x →  Nat2ℕ (dblNat x) ≡ 2 * Nat2ℕ x
dblNat-lem (IN x (inj₁ x₁)) = refl
dblNat-lem (IN x (inj₂ y)) rewrite dblNat-lem (x y)
  | +-comm (Nat2ℕ (x y)) (suc (Nat2ℕ (x y) + 0))
  | +-comm (Nat2ℕ (x y)) 0  = refl
