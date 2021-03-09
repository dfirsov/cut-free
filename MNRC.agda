{-#  OPTIONS --type-in-type #-}


open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.Any  hiding (map)
open import Data.Vec hiding (map; _++_; _∈_)
open import Data.Unit hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infix 25 _∧_
infix 25 _∨_
infix 4 _⇒_
infix 3 _,_⊢_

data Formula : ℕ → Set where
  unit : ∀ {n} → Formula n
  _∧_  : ∀ {n} → Formula n → Formula n → Formula n
  _∨_  : ∀ {n} → Formula n → Formula n → Formula n
  var  : ∀ {n} → Fin n → Formula n
  μ    : ∀ {n} → Formula (suc n) → Formula n

Context : ℕ → Set
Context n = List (Formula n)


weakenFA : {n : ℕ} → Fin (suc n) → Formula n → Formula (suc n)
weakenFA p unit = unit
weakenFA p (A ∧ B) = weakenFA p A ∧ weakenFA p B
weakenFA p (A ∨ B) = weakenFA p A ∨ weakenFA p B  
weakenFA p (var x) = var (punchIn p x) -- punchIn p x = if x≥p then x+1 else x
weakenFA p (μ f) = μ (weakenFA (suc p) f)


cmpr : {n : ℕ} → (a b : Fin n) → Dec (a ≡ b)
cmpr zero zero = yes refl
cmpr zero (suc b) = no λ { () }
cmpr (suc a) zero = no λ { () }
cmpr (suc a) (suc b)  with cmpr a b
cmpr (suc a) (suc .a) | yes refl = yes refl
cmpr (suc a) (suc b) | no ¬p = no λ { refl → ¬p refl } 

substVar : {n : ℕ} → Fin (suc n) → Formula n → Formula (suc n) → Formula n
substVar p  f unit = unit
substVar p f (A ∧ B) = substVar p  f A ∧ substVar p f B
substVar p f (A ∨ B) = substVar p f A ∨ substVar p f B
substVar p f (μ A) = μ (substVar (suc p)  (weakenFA zero f) A)
-- The function f(i,j) = if j>i then j-1 else j
substVar p f (var x) with cmpr p x
substVar p f (var x) | no ¬p = var (punchOut ¬p)
substVar p f (var x) | yes p₁ = f

{-
substVar : {n : ℕ} → Fin (suc n) → Formula n → Formula (suc n) → Formula n
substVar p f unit = unit
substVar p f (A ∧ B) = substVar p f A ∧ substVar p f B
substVar p f (A ∨ B) = substVar p f A ∨ substVar p f B
substVar p f (var zero) = f
substVar p f (var (suc x)) = var x 
substVar p f (μ A) = μ (substVar (suc p) (weakenFA zero f) A)
-}

data Seq (n : ℕ) : Set where
  _⇒_ : Context n → Formula n → Seq n

HContext : ℕ → Set
HContext n = List (Seq n)

weakenContext : {n : ℕ} → Context n  → Context (suc n)
weakenContext Γ  = map (weakenFA zero) Γ

weakenSeq : {n : ℕ} → Seq n  → Seq (suc n)
weakenSeq (Γ ⇒ A) = weakenContext Γ ⇒ weakenFA zero A

weakenHContext : {n : ℕ} → HContext n  → HContext (suc n)
weakenHContext Φ = map weakenSeq Φ

data _,_⊢_ : (n : ℕ) → HContext n → Seq n → Set where
  id-axiom : ∀ {n : ℕ}{Φ : HContext n}{Γ : Context n}{A : Formula n}
        → n , Φ ⊢ A ∷ Γ ⇒ A

  unit-r : ∀ {n : ℕ}{Φ : HContext n}{Γ : Context n} → n , Φ ⊢ Γ ⇒ unit
  unit-l : ∀ {n : ℕ}{Φ : HContext n}{Γ : Context n}{C : Formula n}
   → n , Φ ⊢   Γ ⇒ C  → n , Φ ⊢  unit ∷ Γ ⇒ C


  ∧-r  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B : Formula n}
             → n , Φ ⊢  Γ ⇒ A → n , Φ ⊢  Γ ⇒ B → n , Φ ⊢  Γ ⇒ A ∧ B
  ∧-l  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B C : Formula n}
             →   n , Φ ⊢  A ∷ B ∷ Γ ⇒ C → n , Φ ⊢  A ∧ B ∷ Γ ⇒ C

  
  ∨-r₁  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B : Formula n}
             → n , Φ ⊢  Γ ⇒ A → n , Φ ⊢  Γ ⇒ A ∨ B

  ∨-r₂  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B : Formula n}
             → n , Φ ⊢  Γ ⇒ B → n , Φ ⊢  Γ ⇒ A ∨ B


  ∨-l  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B C : Formula n}
             → n , Φ ⊢   A ∷ Γ ⇒ C 
             → n , Φ ⊢   B ∷ Γ ⇒ C 
             → n , Φ ⊢   A ∨ B ∷ Γ ⇒ C   

  μ-r  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula (suc n)}
             → n , Φ ⊢  Γ ⇒ substVar zero (μ A)  A
             → n , Φ ⊢  Γ ⇒ μ A

  μ-l  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula (suc n)}{C : Formula n}
            → (suc n) ,
               (var zero ∷ weakenContext Γ ⇒ weakenFA zero C) ∷ weakenHContext Φ
                     ⊢ A ∷ weakenContext Γ ⇒ weakenFA zero C 
            → n , Φ ⊢ μ A ∷  Γ ⇒ C

  hyp-use : ∀ {n : ℕ}{Φ : HContext n}{S : Seq n}
     → S ∈ Φ → n , Φ  ⊢ S

  contr  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula n}{C : Formula n}
            → n , Φ ⊢ A ∷ A ∷ Γ ⇒ C
            → n , Φ ⊢ A ∷ Γ ⇒ C


  weakn  : ∀ {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula n}{C : Formula n}
            → n , Φ ⊢ Γ ⇒ C
            → n , Φ ⊢ A ∷ Γ ⇒ C

  exchng  : ∀ {n : ℕ}{Φ : HContext n} {Γ Γ₁ Γ₂ : Context n} {A : Formula n}{C : Formula n}
            → Γ ≡  Γ₁ ++ Γ₂
            → n , Φ ⊢ A ∷ Γ ⇒ C            
            → n , Φ ⊢ Γ₁ ++ A ∷ Γ₂ ⇒ C


open import Data.Product
open import Data.Sum
open import Function

data Mu (F : Set → Set) :  Set where
  IN : ∀ {X : Set} → (X → Mu F) → F X → Mu F




In : {F : Set → Set} → F (Mu F) → Mu F
In m = IN id m

Fold : {F : Set → Set}{C : Set} → ((Y : Set) → (Y → C) → F Y → C) → Mu F  → C
Fold {F} alg (IN {X} f v) = alg X (Fold alg ∘ f) v 


⟦_⟧F  : {n : ℕ} → Formula n → Vec Set n → Set
⟦ unit ⟧F ρ = ⊤
⟦ A ∧ B ⟧F ρ = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ
⟦ A ∨ B ⟧F ρ = ⟦ A ⟧F ρ  ⊎ ⟦ B ⟧F ρ
⟦ var x ⟧F ρ = lookup x ρ
⟦ μ A ⟧F ρ = Mu λ (X : Set) → ⟦ A ⟧F (X ∷ ρ)  


⟦_⟧c : {n : ℕ} → Context n → Vec Set n → Set
⟦ [] ⟧c ρ = ⊤
⟦ A ∷ Γ ⟧c ρ = ⟦ A ⟧F ρ × ⟦ Γ ⟧c ρ

⟦_⟧s : {n : ℕ} → Seq n → Vec Set n → Set
⟦ Γ ⇒ A ⟧s ρ = ⟦ Γ ⟧c ρ → ⟦ A ⟧F ρ

⟦_⟧H : {n : ℕ} → HContext n → Vec Set n → Set
⟦ [] ⟧H ρ = ⊤
⟦ S ∷ Φ ⟧H ρ = ⟦ S ⟧s ρ × ⟦ Φ ⟧H ρ


insert : {X : Set} {n : ℕ} → X → Fin (suc n) → Vec X n → Vec X (suc n)
insert x zero v = x ∷ v
insert x (suc ()) []
insert x (suc p) (x₁ ∷ v) = x₁ ∷ insert x p v

substEq' : {n : ℕ} → (i : Fin (suc n))  →  (A : Formula (suc n)) → {B : Formula n} → {ρ : Vec Set n} → ⟦ substVar i B A  ⟧F ρ → ⟦ A ⟧F (insert (⟦ B ⟧F ρ) i ρ )
substEq' i unit v = v
substEq' i (A ∧ B) (a , b) = {!!} , {!!}
substEq' i (A ∨ B) (inj₁ a) = {!!}
substEq' i (A ∨ B) (inj₂ b) = {!!}
substEq' zero (var zero) {ρ = ρ} v = v
substEq' zero (var (suc x)) {ρ = ρ} v = v
substEq' (suc i) (var zero) v = {!!}
substEq' (suc i) (var (suc x)) v = {!!}
substEq' zero (μ A) {ρ = ρ} v = Fold (λ Y f fv → IN f {!substEq' (suc zero) A fv!}) v 
substEq' (suc b) (μ A) {ρ = ρ} (IN x x₁) = In {!substEq' (suc (suc b)) A x₁!}

substEq : {n : ℕ} → {i : Fin (suc n)} (A : Formula (suc n)) → {B : Formula n} → {ρ : Vec Set n} → ⟦ substVar i B A  ⟧F ρ ≡ ⟦ A ⟧F (insert (⟦ B ⟧F ρ) i ρ )
substEq unit = refl
substEq {n} (A ∧ A₁) {B} {ρ} rewrite (substEq {n} A {B} {ρ}) | (substEq {n} A₁ {B} {ρ}) = {!!}
substEq {n} (A ∨ A₁) {B} {ρ} rewrite (substEq {n} A {B} {ρ}) | (substEq {n} A₁ {B} {ρ}) = {!!}
substEq (var zero) = {!!}
substEq (var (suc x)) = {!!}
substEq (μ A) = {!substEq  A!}



inser-punch : {X : Set} {n : ℕ} → (x : X) → (j : Fin n) → (i : Fin (suc n)) → (ρ : Vec X n) →  lookup j ρ ≡ lookup (punchIn i j) (insert x i ρ)
inser-punch x j zero ρ = refl
inser-punch x zero (suc i) (x₁ ∷ ρ) = refl
inser-punch x (suc j) (suc i) (x₁ ∷ ρ) = inser-punch x j i ρ



MuF2G : {F G : Set → Set } → (∀ (Y : Set) → F Y → G Y) →  Mu F → Mu G
MuF2G {F} {G} conv mf = Fold ( λ X f v → IN {G} f (conv  X v)) mf

F→weakF : {n : ℕ}(i : Fin (suc n)){X : Set}(C : Formula n) → {ρ : Vec Set n}
  →  ⟦ C ⟧F ρ → ⟦ weakenFA i C ⟧F (insert X i ρ)
F→weakF i unit v = tt
F→weakF i (A ∧ B) (a , b) = (F→weakF i A a) , (F→weakF i B b)
F→weakF i (A ∨ B) (inj₁ a) = inj₁ (F→weakF i A a)
F→weakF i (A ∨ B) (inj₂ b) = inj₂ (F→weakF i B b)
F→weakF i (var x) {ρ} v = subst id (inser-punch _ _ i ρ) v
F→weakF {n} i {X} (μ C) {ρ} mv = MuF2G (λ Y  → F→weakF (suc i) C {Y ∷ ρ} ) mv


weakF→F : {n : ℕ}(i : Fin (suc n)){X : Set}(C : Formula n) → {ρ : Vec Set n}
  → ⟦ weakenFA i C ⟧F (insert X i ρ) →  ⟦ C ⟧F ρ
weakF→F i unit v = tt
weakF→F i (A ∧ B) (a , b) = (weakF→F i A a) , (weakF→F i B b)
weakF→F i (A ∨ B) (inj₁ a) = inj₁ (weakF→F i A a)
weakF→F i (A ∨ B) (inj₂ b) = inj₂ (weakF→F i B b)
weakF→F i (var x) {ρ} v = subst id (sym (inser-punch _ _ i ρ)) v
weakF→F {n} i {X} (μ C) {ρ} mv = MuF2G (λ Y  → weakF→F (suc i) C {Y ∷ ρ} ) mv


weakC→C : {n : ℕ}{X : Set}(Γ : Context n) → {ρ : Vec Set n} → ⟦ weakenContext Γ ⟧c (X ∷ ρ) → ⟦ Γ ⟧c ρ
weakC→C [] v = v
weakC→C (A ∷ Γ) (x , xs) = weakF→F zero A x , weakC→C Γ xs

C→weakC : {n : ℕ}{X : Set}(Γ : Context n) → {ρ : Vec Set n} → ⟦ Γ ⟧c ρ
 → ⟦ weakenContext Γ ⟧c (X ∷ ρ) 
C→weakC [] v = v
C→weakC (A ∷ Γ) (x , xs) = F→weakF zero A x , C→weakC Γ xs



weakS→S : {n : ℕ}{X : Set}(S : Seq n) → {ρ : Vec Set n} → ⟦ weakenSeq S ⟧s (X ∷ ρ) → ⟦ S ⟧s ρ
weakS→S (Γ  ⇒ A) f = weakF→F zero A ∘ f ∘ C→weakC Γ

S→weakS : {n : ℕ}{X : Set}(S : Seq n) → {ρ : Vec Set n} → ⟦ S ⟧s ρ → ⟦ weakenSeq S ⟧s (X ∷ ρ)
S→weakS (Γ  ⇒ A) f = F→weakF zero A ∘ f ∘ weakC→C Γ

weakH→H : {n : ℕ}{X : Set}(Φ : HContext n) → {ρ : Vec Set n}
 → ⟦ weakenHContext Φ ⟧H (X ∷ ρ) → ⟦ Φ ⟧H ρ 
weakH→H [] v = v
weakH→H (S ∷ Φ) (f , fs) = weakS→S S f , weakH→H Φ fs

H→weakH : {n : ℕ}{X : Set}(Φ : HContext n) → {ρ : Vec Set n}
  → ⟦ Φ ⟧H ρ  → ⟦ weakenHContext Φ ⟧H (X ∷ ρ)
H→weakH [] v = v
H→weakH (S ∷ Φ) (f , fs) = S→weakS S f , H→weakH Φ fs



⟦_⟧ : {n : ℕ}{Φ : HContext n}{S : Seq n} → n , Φ ⊢ S → (ρ : Vec Set n) → ⟦ Φ ⟧H ρ → ⟦ S ⟧s ρ
⟦ id-axiom ⟧ ρ φ =  λ { (a , _) → a }
⟦ unit-r ⟧ ρ φ = λ _ → tt
⟦ unit-l f ⟧ ρ φ = λ { (_ , xs) → ⟦ f  ⟧ ρ φ xs }
⟦ ∧-r f g ⟧ ρ φ = λ xs → ⟦ f ⟧ ρ φ xs , ⟦ g ⟧ ρ φ xs 
⟦ ∧-l f ⟧ ρ φ = λ { ((x , y) , xs) → ⟦ f ⟧ ρ φ (x , (y , xs)) }
⟦ ∨-r₁ f ⟧ ρ φ = λ xs → inj₁ (⟦ f ⟧ ρ φ xs)
⟦ ∨-r₂ f ⟧ ρ φ = λ xs → inj₂ (⟦ f ⟧ ρ φ xs)
⟦ ∨-l f g ⟧ ρ φ = λ { (inj₁ x , xs) → ⟦ f ⟧ ρ φ (x , xs) ; (inj₂ y , xs) →  ⟦ g ⟧ ρ φ (y , xs) }
⟦ μ-r  {n = n}  {A = A} f ⟧ ρ φ = λ xs → In {!(⟦ f ⟧ ρ φ xs)!}

--λ xs → In {!(weakF→F {n} zero  (⟦ f ⟧ ρ φ xs))!}

-- (subst id (sym (substEq A)) ((⟦ f ⟧ ρ φ xs)))

⟦ μ-l  {Φ = Φ} {Γ = Γ} {C = C} f ⟧ ρ φ = uncurry (Fold λ X recf q1 q2 → ((weakF→F zero {X = X} C {ρ})) (⟦ f  ⟧ (X ∷ ρ) ((λ { (x , b) →  (F→weakF zero C) (recf x (weakC→C Γ  b))  }) ,  ( (H→weakH Φ)) φ) (q1 ,  ((C→weakC Γ)) q2) ))
⟦ hyp-use (here refl) ⟧ ρ (f , _) = f
⟦ hyp-use (there x) ⟧ ρ (_ , φ') = ⟦ hyp-use x ⟧ ρ φ'
⟦ contr f ⟧ ρ φ = λ { (x , xs) → ⟦ f ⟧ ρ φ (x , (x , xs)) }
⟦ weakn f ⟧ ρ φ = λ { (x , xs) → ⟦ f ⟧ ρ φ xs }
⟦ exchng refl x₁ ⟧ ρ φ = {!!}




NatRaw : Formula 0
NatRaw =  μ (unit ∨ var zero)   

Nat : Set
Nat = ⟦ NatRaw  ⟧F [] 

Nat2ℕ : Nat → ℕ
Nat2ℕ (IN f (inj₁ tt)) = 0
Nat2ℕ (IN f (inj₂ y)) = suc (Nat2ℕ (f y))

z : Nat
z = In (inj₁ tt)

s : Nat → Nat
s n = In (inj₂ n)


addRaw : zero , [] ⊢ NatRaw ∧ NatRaw ∷ [] ⇒ NatRaw
addRaw = ∧-l (μ-l (∨-l (unit-l id-axiom) (μ-r (∨-r₂ (hyp-use (here refl))))))

add : Nat × Nat → Nat
add (a , b) = ⟦ addRaw ⟧ [] tt ((a , b) , tt)


lem : Nat2ℕ (add ((s (s z)) , (s (s z)) )) ≡ Nat2ℕ ((s (s (s (s z)))))
lem = refl





μBoolRaw : Formula 0
μBoolRaw = μ (unit ∨ unit)

μBool : Set
μBool = ⟦ μBoolRaw ⟧F []

μf : μBool
μf = In (inj₂ tt)

μt : μBool
μt = In (inj₁ tt)

WeirdRaw : Formula 0
WeirdRaw = μ (unit ∨ (μ (unit ∨ unit) ∧ var Data.Fin.zero))


Weird : Set
Weird = ⟦ WeirdRaw ⟧F []

wb : Weird
wb = In (inj₁ tt)

ws : Weird → μBool → Weird
ws w μb = In (inj₂ (μb , w))


BoolRaw : Formula 0
BoolRaw = unit ∨ unit


𝔹 : Set
𝔹 = ⟦ BoolRaw ⟧F []

t : 𝔹
t = inj₂ tt

f : 𝔹
f = inj₁ tt


doh : zero , [] ⊢ WeirdRaw ∷ [] ⇒ BoolRaw
doh = μ-l (∨-l (∨-r₁ unit-r) (∧-l (μ-l (∨-l (weakn (hyp-use (there (here refl)))) (∨-r₂ unit-r) ))))



doh1 : ⟦ doh ⟧ [] tt  (ws (ws wb μt) μt , tt) ≡ f
doh1 = refl

doh2 : ⟦ doh ⟧ [] tt  (ws (ws wb μf) μt , tt) ≡ t
doh2 = refl


