{-#  OPTIONS --type-in-type #-}


open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any hiding (map; lookup)
open import Data.Vec hiding (map; _++_)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Unit hiding (_≟_)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Sum hiding (map)
open import Function

infix 25 _⊗_
infix 25 _∧_
infix 25 _⊕_
infix 4 _⇒_
infix 3 _,_⊢_

data Formula : ℕ → Set where
  one : ∀ {n} → Formula n
  _⊗_ : ∀ {n} → Formula n → Formula n → Formula n
  top : ∀ {n} → Formula n  
  _∧_  : ∀ {n} → Formula n → Formula n → Formula n
  zero : ∀ {n} → Formula n  
  _⊕_  : ∀ {n} → Formula n → Formula n → Formula n
  var  : ∀ {n} → Fin n → Formula n
  μ    : ∀ {n} → Formula (suc n) → Formula n

Context : ℕ → Set
Context n = List (Formula n)

data Seq (n : ℕ) : Set where
  _⇒_ : Context n → Formula n → Seq n

HContext : ℕ → Set
HContext n = List (Seq n)


weakF : {n : ℕ} → Fin (suc n) → Formula n → Formula (suc n)
weakF i one = one
weakF i (A ⊗ B) = weakF i A ⊗ weakF i B
weakF i top = top
weakF i (A ∧ B) = weakF i A ∧ weakF i B
weakF i zero = zero
weakF i (A ⊕ B) = weakF i A ⊕ weakF i B  
weakF i (var j) = var (punchIn i j) -- punchIn p x = if x≥p then x+1 else x
weakF i (μ F) = μ (weakF (suc i) F)

substF : {n : ℕ} → Fin (suc n) → Formula n → Formula (suc n) → Formula n
substF i C one = one
substF i C (A ⊗ B) = substF i C A ⊗ substF i C B
substF i C top = top
substF i C (A ∧ B) = substF i C A ∧ substF i C B
substF i C zero = zero
substF i C (A ⊕ B) = substF i C A ⊕ substF i C B
substF i C (μ A) = μ (substF (suc i)  (weakF zero C) A)
-- The function f(i,j) = if j>i then j-1 else j
substF i C (var j) with i ≟ j
substF i C (var j) | no ¬p = var (punchOut ¬p)
substF i C (var j) | yes refl = C




weakContext : {n : ℕ} → Context n  → Context (suc n)
weakContext Γ  = map (weakF zero) Γ

weakSeq : {n : ℕ} → Seq n  → Seq (suc n)
weakSeq (Γ ⇒ A) = weakContext Γ ⇒ weakF zero A

weakHContext : {n : ℕ} → HContext n  → HContext (suc n)
weakHContext Φ = map weakSeq Φ

data _,_⊢_ : (n : ℕ) → HContext n → Seq n → Set where
  id-axiom : {n : ℕ}{Φ : HContext n}{A : Formula n}
        → n , Φ ⊢ A ∷ [] ⇒ A

  -- multiplicatives
  
  one-r : {n : ℕ}{Φ : HContext n} → n , Φ ⊢ [] ⇒ one

  one-l : {n : ℕ}{Φ : HContext n}{Γ : Context n}{C : Formula n}
   → n , Φ ⊢ Γ ⇒ C  → n , Φ ⊢  one ∷ Γ ⇒ C

  ⊗-r  : {n : ℕ}{Φ : HContext n} {Γ Δ : Context n} {A B : Formula n}
             → n , Φ ⊢  Γ ⇒ A → n , Φ ⊢ Δ ⇒ B → n , Φ ⊢  Γ ++ Δ ⇒ A ⊗ B

  ⊗-l  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B C : Formula n}
             →   n , Φ ⊢  A ∷ B ∷ Γ ⇒ C → n , Φ ⊢  A ∧ B ∷ Γ ⇒ C

  -- additives

  top-r : {n : ℕ}{Φ : HContext n}{Γ : Context n} → n , Φ ⊢ Γ ⇒ one

  ∧-r : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B : Formula n}
             → n , Φ ⊢  Γ ⇒ A → n , Φ ⊢  Γ ⇒ B → n , Φ ⊢  Γ ⇒ A ∧ B

  ∧-l₁ : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B C : Formula n}
             →  n , Φ ⊢  A ∷ Γ ⇒ C → n , Φ ⊢  A ∧ B ∷ Γ ⇒ C
  ∧-l₂ : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B C : Formula n}
             →  n , Φ ⊢  B ∷ Γ ⇒ C → n , Φ ⊢  A ∧ B ∷ Γ ⇒ C

  zero-l : {n : ℕ}{Φ : HContext n} {Γ : Context n} {C : Formula n}
            → n , Φ ⊢ zero ∷ Γ ⇒ C 

  ⊕-r₁  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B : Formula n}
             → n , Φ ⊢  Γ ⇒ A → n , Φ ⊢  Γ ⇒ A ⊕ B

  ⊕-r₂  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B : Formula n}
             → n , Φ ⊢  Γ ⇒ B → n , Φ ⊢  Γ ⇒ A ⊕ B

  ⊕-l  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A B C : Formula n}
             → n , Φ ⊢   A ∷ Γ ⇒ C 
             → n , Φ ⊢   B ∷ Γ ⇒ C 
             → n , Φ ⊢   A ⊕ B ∷ Γ ⇒ C   

  μ-r  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula (suc n)}
             → n , Φ ⊢  Γ ⇒ substF zero (μ A)  A
             → n , Φ ⊢  Γ ⇒ μ A

  μ-l  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula (suc n)}{C : Formula n}
            → suc n ,
               (var zero ∷ weakContext Γ ⇒ weakF zero C) ∷ weakHContext Φ
                     ⊢ A ∷ weakContext Γ ⇒ weakF zero C 
            → n , Φ ⊢ μ A ∷  Γ ⇒ C

  hyp-use : {n : ℕ}{Φ : HContext n}{S : Seq n}
     → S ∈ Φ → n , Φ  ⊢ S

  ctr  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula n}{C : Formula n}
            → n , Φ ⊢ A ∷ A ∷ Γ ⇒ C
            → n , Φ ⊢ A ∷ Γ ⇒ C


  wk  : {n : ℕ}{Φ : HContext n} {Γ : Context n} {A : Formula n}{C : Formula n}
            → n , Φ ⊢ Γ ⇒ C
            → n , Φ ⊢ A ∷ Γ ⇒ C

  exch  : {n : ℕ}{Φ : HContext n} {Γ Γ₁ Γ₂ : Context n} {A : Formula n}{C : Formula n}
            → Γ ≡  Γ₁ ++ Γ₂         
            → n , Φ ⊢ Γ₁ ++ A ∷ Γ₂ ⇒ C
            → n , Φ ⊢ A ∷ Γ ⇒ C  



data Mu (F : Set → Set) :  Set where
  IN : {X : Set} → (X → Mu F) → F X → Mu F

In : {F : Set → Set} → F (Mu F) → Mu F
In {F} m = IN {_} {Mu F} id m

Fold : {F : Set → Set}{C : Set} → ((Y : Set) → (Y → C) → F Y → C) → Mu F  → C
Fold {F} alg (IN {X} f x) = alg X (Fold alg ∘ f) x 

MuF2G : {F G : Set → Set} → ((Y : Set) → F Y → G Y) → Mu F → Mu G
MuF2G {F} {G} f2g x = Fold {F}  ( λ Y f y → IN {G} {Y} f (f2g Y y)) x




⟦_⟧F  : {n : ℕ} → Formula n → Vec Set n → Set
⟦ one ⟧F ρ = ⊤
⟦ A ⊗ B ⟧F ρ = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ
⟦ top ⟧F ρ = ⊤
⟦ A ∧ B ⟧F ρ = ⟦ A ⟧F ρ  × ⟦ B ⟧F ρ
⟦ zero ⟧F ρ = ⊥
⟦ A ⊕ B ⟧F ρ = ⟦ A ⟧F ρ  ⊎ ⟦ B ⟧F ρ
⟦ var i ⟧F ρ = lookup ρ i
⟦ μ A ⟧F ρ = Mu λ (X : Set) → ⟦ A ⟧F (X ∷ ρ)  


⟦_⟧c : {n : ℕ} → Context n → Vec Set n → Set
⟦ [] ⟧c ρ = ⊤
⟦ A ∷ Γ ⟧c ρ = ⟦ A ⟧F ρ × ⟦ Γ ⟧c ρ

⟦_⟧s : {n : ℕ} → Seq n → Vec Set n → Set
⟦ Γ ⇒ A ⟧s ρ = ⟦ Γ ⟧c ρ → ⟦ A ⟧F ρ

⟦_⟧H : {n : ℕ} → HContext n → Vec Set n → Set
⟦ [] ⟧H ρ = ⊤
⟦ S ∷ Φ ⟧H ρ = ⟦ S ⟧s ρ × ⟦ Φ ⟧H ρ


{-
-- weaking and substitution lemmata proved as equalities of sets 
-- using function extensionality

postulate funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
    
weakF-lem : {n : ℕ}(i : Fin (suc n)){X : Set}(A : Formula n) {ρ : Vec Set n} →
   ⟦ weakF i A ⟧F (insert ρ i X) ≡  ⟦ A ⟧F ρ
weakF-lem i one = refl
weakF-lem i (A ⊗ B) = cong₂ _×_ (weakF-lem i A) (weakF-lem i B) 
weakF-lem i top = refl
weakF-lem i (A ∧ B) = cong₂ _×_ (weakF-lem i A) (weakF-lem i B) 
weakF-lem i zero = refl
weakF-lem i (A ⊕ B) = cong₂ _⊎_ (weakF-lem i A) (weakF-lem i B) 
weakF-lem i {X} (var j) {ρ} = insert-punchIn ρ i X j
weakF-lem i (μ F) {ρ} = cong Mu (funext λ Y → weakF-lem (suc i) F {Y ∷ ρ})

subst-lem : {n : ℕ} (i : Fin (suc n)) {C : Formula n} (A : Formula (suc n)) {ρ : Vec Set n} →
   ⟦ substF i C A ⟧F ρ ≡ ⟦ A ⟧F (insert ρ i (⟦ C ⟧F ρ))
subst-lem i one = refl
subst-lem i (A ⊗ B) = cong₂ _×_ (subst-lem i A) (subst-lem i B)
subst-lem i top = refl
subst-lem i (A ∧ B) = cong₂ _×_ (subst-lem i A) (subst-lem i B)
subst-lem i zero = refl
subst-lem i (A ⊕ B) = cong₂ _⊎_ (subst-lem i A) (subst-lem i B)
subst-lem i (var j) with i ≟ j
subst-lem i {C} (var .i) {ρ} | yes refl = sym (insert-lookup ρ i (⟦ C ⟧F ρ)) 
subst-lem i {C} (var j) {ρ} | no ¬p = trans
                  (cong (λ h → lookup h (punchOut ¬p)) (sym (remove-insert ρ i (⟦ C ⟧F ρ))))
                  (remove-punchOut (insert ρ i (⟦ C ⟧F ρ)) ¬p)
subst-lem i {C} (μ A) {ρ} = cong Mu (funext (λ Y → trans
                  (subst-lem (suc i) {weakF 0F C} A {Y ∷ ρ})
                  (cong (λ h → ⟦ A ⟧F (Y ∷ insert ρ i h)) (weakF-lem 0F C))))
-}                  


-- weaking and substitution lemmata proved as bijections between sets
-- without using function extensionality 

weakF-lem-from : {n : ℕ}(i : Fin (suc n)){X : Set}(C : Formula n){ρ : Vec Set n} →
   ⟦ weakF i C ⟧F (insert ρ i X) →  ⟦ C ⟧F ρ
weakF-lem-from i one tt = tt
weakF-lem-from i (A ⊗ B) (x₁ , x₂) = weakF-lem-from i A x₁ , weakF-lem-from i B x₂
weakF-lem-from i top tt = tt
weakF-lem-from i (A ∧ B) (x₁ , x₂) = weakF-lem-from i A x₁ , weakF-lem-from i B x₂
weakF-lem-from i (A ⊕ B) (inj₁ x) = inj₁ (weakF-lem-from i A x)
weakF-lem-from i (A ⊕ B) (inj₂ x) = inj₂ (weakF-lem-from i B x)
weakF-lem-from i {X} (var j) {ρ} = subst id (insert-punchIn ρ i X j)
weakF-lem-from i (μ A) {ρ} = MuF2G (λ Y → weakF-lem-from (suc i) A {Y ∷ ρ} )

weakF-lem-to : {n : ℕ}(i : Fin (suc n)){X : Set}(C : Formula n){ρ : Vec Set n} →
   ⟦ C ⟧F ρ → ⟦ weakF i C ⟧F (insert ρ i X)
weakF-lem-to i one tt = tt
weakF-lem-to i (A ⊗ B) (x₁ , x₂) = weakF-lem-to i A x₁ , weakF-lem-to i B x₂
weakF-lem-to i top tt = tt
weakF-lem-to i (A ∧ B) (x₁ , x₂) = weakF-lem-to i A x₁ , weakF-lem-to i B x₂
weakF-lem-to i (A ⊕ B) (inj₁ x) = inj₁ (weakF-lem-to i A x)
weakF-lem-to i (A ⊕ B) (inj₂ x) = inj₂ (weakF-lem-to i B x)
weakF-lem-to i {X} (var j) {ρ} = subst id (sym (insert-punchIn ρ i X j))
weakF-lem-to i (μ A) {ρ} = MuF2G (λ Y → weakF-lem-to (suc i) A {Y ∷ ρ})


monot : {n : ℕ} (i : Fin (suc n))(A : Formula (suc n)){ρ : Vec Set n}{X X' : Set} → 
   (X → X') → ⟦ A ⟧F (insert ρ i X) → ⟦ A ⟧F (insert ρ i X')
monot i one f tt = tt
monot i (A ⊗ B) f (x₁ , x₂) =  monot i A f x₁ , monot i B f x₂  
monot i top f tt = tt
monot i (A ∧ B) f (x₁ , x₂) =  monot i A f x₁ , monot i B f x₂ 
monot i (A ⊕ B) f (inj₁ x) = inj₁ (monot i A f x) 
monot i (A ⊕ B) f (inj₂ x) = inj₂ (monot i B f x)
monot i (var j) f with i ≟ j
monot i (var .i) {ρ} {X} {X'} f | yes refl =
             subst id (sym (insert-lookup ρ i X')) ∘ f ∘ subst id (insert-lookup ρ i X)
monot i (var j) f | no ¬p = {!!}
monot i (μ A) {ρ} f = MuF2G (λ Y → monot (suc i) A {Y ∷ ρ} f)


subst-lem-from : {n : ℕ} (i : Fin (suc n)) {C : Formula n} (A : Formula (suc n)) {ρ : Vec Set n} →
   ⟦ substF i C A ⟧F ρ → ⟦ A ⟧F (insert ρ i (⟦ C ⟧F ρ))
subst-lem-from i one tt = tt
subst-lem-from i (A ⊗ B) (x₁ , x₂) = subst-lem-from i A x₁ , subst-lem-from i B x₂ 
subst-lem-from i top tt = tt
subst-lem-from i (A ∧ B) (x₁ , x₂) = subst-lem-from i A x₁ , subst-lem-from i B x₂
subst-lem-from i (A ⊕ B) (inj₁ x) = inj₁ (subst-lem-from i A x)
subst-lem-from i (A ⊕ B) (inj₂ x) = inj₂ (subst-lem-from i B x)
subst-lem-from i (var j) with i ≟ j
subst-lem-from i {C} (var .i) {ρ} | yes refl = subst id (sym (insert-lookup ρ i (⟦ C ⟧F ρ)))
subst-lem-from i {C} (var j) {ρ} | no ¬p = subst id (trans
                  (cong (λ h → lookup h (punchOut ¬p)) (sym (remove-insert ρ i (⟦ C ⟧F ρ))))
                  (remove-punchOut (insert ρ i (⟦ C ⟧F ρ)) ¬p))
subst-lem-from i {C} (μ A) {ρ} = MuF2G (λ Y →
                  monot (suc i) A {Y ∷ ρ} (weakF-lem-from 0F C)
                  ∘ subst-lem-from (suc i) {weakF 0F C} A {Y ∷ ρ})

subst-lem-to : {n : ℕ} (i : Fin (suc n)) {C : Formula n} (A : Formula (suc n)) {ρ : Vec Set n} →
   ⟦ A ⟧F (insert ρ i (⟦ C ⟧F ρ)) → ⟦ substF i C A ⟧F ρ
subst-lem-to i one tt = tt
subst-lem-to i (A ⊗ B) (x₁ , x₂) = subst-lem-to i A x₁ , subst-lem-to i B x₂ 
subst-lem-to i top tt = tt
subst-lem-to i (A ∧ B) (x₁ , x₂) = subst-lem-to i A x₁ , subst-lem-to i B x₂ 
subst-lem-to i (A ⊕ B) (inj₁ x) = inj₁ (subst-lem-to i A x)
subst-lem-to i (A ⊕ B) (inj₂ x) = inj₂ (subst-lem-to i B x)
subst-lem-to i {C} (var j) {ρ} with i ≟ j
subst-lem-to i {C} (var .i) {ρ} | yes refl = subst id (insert-lookup ρ i (⟦ C ⟧F ρ))
subst-lem-to i {C} (var j) {ρ} | no ¬p = subst id (trans
                  (sym (remove-punchOut (insert ρ i (⟦ C ⟧F ρ)) ¬p))
                  (cong (λ h → lookup h (punchOut ¬p)) (remove-insert ρ i (⟦ C ⟧F ρ))))
subst-lem-to i {C} (μ A) {ρ} = MuF2G (λ Y →
                  subst-lem-to (suc i) {weakF 0F C} A {Y ∷ ρ} 
                  ∘ monot (suc i) A {Y ∷ ρ} (weakF-lem-to 0F C))
                  

weakC-lem-from : {n : ℕ}{X : Set}(Γ : Context n){ρ : Vec Set n} →
   ⟦ weakContext Γ ⟧c (X ∷ ρ) → ⟦ Γ ⟧c ρ
weakC-lem-from [] tt = tt
weakC-lem-from (A ∷ Γ) (x , xs) = weakF-lem-from zero A x , weakC-lem-from Γ xs

weakC-lem-to : {n : ℕ}{X : Set}(Γ : Context n){ρ : Vec Set n} →
   ⟦ Γ ⟧c ρ → ⟦ weakContext Γ ⟧c (X ∷ ρ) 
weakC-lem-to [] tt = tt
weakC-lem-to (A ∷ Γ) (x , xs) = weakF-lem-to zero A x , weakC-lem-to Γ xs


weakS-lem-from : {n : ℕ}{X : Set}(S : Seq n){ρ : Vec Set n} →
   ⟦ weakSeq S ⟧s (X ∷ ρ) → ⟦ S ⟧s ρ
weakS-lem-from (Γ ⇒ A) f = weakF-lem-from zero A ∘ f ∘ weakC-lem-to Γ

weakS-lem-to : {n : ℕ}{X : Set}(S : Seq n){ρ : Vec Set n} →
   ⟦ S ⟧s ρ → ⟦ weakSeq S ⟧s (X ∷ ρ)
weakS-lem-to (Γ ⇒ A) f = weakF-lem-to zero A ∘ f ∘ weakC-lem-from Γ

weakH-lem-from : {n : ℕ}{X : Set}(Φ : HContext n){ρ : Vec Set n} →
   ⟦ weakHContext Φ ⟧H (X ∷ ρ) → ⟦ Φ ⟧H ρ 
weakH-lem-from [] tt = tt
weakH-lem-from (S ∷ Φ) (f , fs) = weakS-lem-from S f , weakH-lem-from Φ fs

weakH-lem-to : {n : ℕ}{X : Set}(Φ : HContext n){ρ : Vec Set n} →
   ⟦ Φ ⟧H ρ  → ⟦ weakHContext Φ ⟧H (X ∷ ρ)
weakH-lem-to [] tt = tt
weakH-lem-to (S ∷ Φ) (f , fs) = weakS-lem-to S f , weakH-lem-to Φ fs


splitC : {n : ℕ}{Γ Δ : Context n}{ρ : Vec Set n} →
   ⟦ Γ ++ Δ ⟧c ρ → ⟦ Γ ⟧c ρ × ⟦ Δ ⟧c ρ 
splitC {_} {[]} xs =  tt , xs
splitC {_} {A ∷ Γ} (x , xs) with splitC {_} {Γ} xs
... | xs₁ , xs₂ =  (x , xs₁) , xs₂


⟦_⟧ : {n : ℕ}{Φ : HContext n}{S : Seq n} → n , Φ ⊢ S → (ρ : Vec Set n) → ⟦ Φ ⟧H ρ → ⟦ S ⟧s ρ
⟦ id-axiom ⟧ ρ fs (x , tt) = x
⟦ one-r ⟧ ρ fs tt =  tt
⟦ one-l f ⟧ ρ fs (tt , xs) =  ⟦ f ⟧ ρ fs xs 
⟦ ⊗-r f g ⟧ ρ fs xs with splitC xs
... | xs₁ , xs₂ = ⟦ f ⟧ ρ fs xs₁ , ⟦ g ⟧ ρ fs xs₂
⟦ ⊗-l f ⟧ ρ fs ((x₁ , x₂) , xs) = ⟦ f ⟧ ρ fs (x₁ , x₂ , xs) 
⟦ top-r ⟧ ρ fs  _ = tt
⟦ ∧-r f g ⟧ ρ fs xs =  ⟦ f ⟧ ρ fs xs , ⟦ g ⟧ ρ fs xs 
⟦ ∧-l₁ f ⟧ ρ fs ((x , _) , xs) = ⟦ f ⟧ ρ fs (x , xs) 
⟦ ∧-l₂ f ⟧ ρ fs ((_ , x) , xs) = ⟦ f ⟧ ρ fs (x , xs)
⟦ ⊕-r₁ f ⟧ ρ fs xs = inj₁ (⟦ f ⟧ ρ fs xs)
⟦ ⊕-r₂ f ⟧ ρ fs xs = inj₂ (⟦ f ⟧ ρ fs xs)
⟦ ⊕-l f g ⟧ ρ fs (inj₁ x , xs) = ⟦ f ⟧ ρ fs (x , xs)
⟦ ⊕-l f g ⟧ ρ fs (inj₂ x , xs) = ⟦ g ⟧ ρ fs (x , xs)
⟦ μ-r {A = A} f ⟧ ρ fs xs = In (subst-lem-from 0F A (⟦ f ⟧ ρ fs xs))

⟦ μ-l {Φ = Φ} {Γ = Γ} {C = C} f ⟧ ρ fs = uncurry (Fold λ X recf q1 q2 →
     weakF-lem-from zero {X} C {ρ} (⟦ f ⟧ (X ∷ ρ)
        (( λ { (x , b) → weakF-lem-to zero C (recf x (weakC-lem-from Γ b)) }) , weakH-lem-to Φ fs)
        (q1 , weakC-lem-to Γ q2))) 
⟦ hyp-use (here refl) ⟧ ρ (f , _) = f
⟦ hyp-use (there x) ⟧ ρ (_ , fs) = ⟦ hyp-use x ⟧ ρ fs
⟦ ctr f ⟧ ρ fs (x , xs) = ⟦ f ⟧ ρ fs (x , x , xs) 
⟦ wk f ⟧ ρ fs (x , xs) = ⟦ f ⟧ ρ fs xs 
⟦ exch refl x₁ ⟧ ρ fs = {!!}



{-

NatRaw : Formula 0
NatRaw =  μ (one ⊕ var zero)   

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
addRaw = ∧-l (μ-l (⊕-l (one-l id-axiom) (μ-r (⊕-r₂ (hyp-use (here refl))))))

add : Nat × Nat → Nat
add (a , b) = ⟦ addRaw ⟧ [] tt ((a , b) , tt)


lem : Nat2ℕ (add ((s (s z)) , (s (s z)) )) ≡ Nat2ℕ ((s (s (s (s z)))))
lem = refl





μBoolRaw : Formula 0
μBoolRaw = μ (one ⊕ one)

μBool : Set
μBool = ⟦ μBoolRaw ⟧F []

μf : μBool
μf = In (inj₂ tt)

μt : μBool
μt = In (inj₁ tt)

WeirdRaw : Formula 0
WeirdRaw = μ (one ⊕ (μ (one ⊕ one) ∧ var zero))


Weird : Set
Weird = ⟦ WeirdRaw ⟧F []

wb : Weird
wb = In (inj₁ tt)

ws : Weird → μBool → Weird
ws w μb = In (inj₂ (μb , w))


BoolRaw : Formula 0
BoolRaw = one ⊕ one


𝔹 : Set
𝔹 = ⟦ BoolRaw ⟧F []

t : 𝔹
t = inj₂ tt

f : 𝔹
f = inj₁ tt


doh : zero , [] ⊢ WeirdRaw ∷ [] ⇒ BoolRaw
doh = μ-l (⊕-l (⊕-r₁ one-r) (∧-l (μ-l (⊕-l (weakn (hyp-use (there (here refl)))) (⊕-r₂ one-r) ))))



doh1 : ⟦ doh ⟧ [] tt  (ws (ws wb μt) μt , tt) ≡ f
doh1 = refl

doh2 : ⟦ doh ⟧ [] tt  (ws (ws wb μf) μt , tt) ≡ t
doh2 = refl


-}
