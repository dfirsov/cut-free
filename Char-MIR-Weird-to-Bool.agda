{-#  OPTIONS --type-in-type #-}

module Char-MIR-Weird-to-Bool where


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

open import MIR 

hyp-free : {Φ : HContext}{Γ : Context}{A : Formula} → Φ ⊢ Γ ⇒ A → Bool
hyp-free id-axiom = true
hyp-free unit-r = true
hyp-free (unit-l d) = hyp-free d
hyp-free (∧-r d d₁) = hyp-free d & hyp-free d₁
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





rrb'''d :  {A B : Formula}{Γ Γ' : Context}
 (d : just (var ∷ Γ' ⇒ A) ⊢ Γ ⇒ B)
  → var-freeC Γ ≡ true
  → hyp-free d ≡ true
rrb'''d id-axiom p = refl
rrb'''d unit-r p = refl
rrb'''d (unit-l d) p = rrb'''d d p
rrb'''d (∧-r d d₁) p rewrite rrb'''d d p | rrb'''d d₁ p = refl
rrb'''d (∧-l d) p = rrb'''d d {!p!}
rrb'''d (∨-r₁ d) p = rrb'''d d p
rrb'''d (∨-r₂ d) p = rrb'''d d p
rrb'''d (∨-l d d₁) p rewrite rrb'''d d {!!} | rrb'''d d₁ {!!} = refl
rrb'''d (μ-r d) p = rrb'''d d p
rrb'''d (μ-l d x x₁) p = rrb'''d  d p
rrb'''d hyp-use ()
rrb'''d (weakn d) p = rrb'''d d  (closed-2 p)
rrb'''d (exchng x d) p = rrb'''d d {!!}


rrb'''c :  (d  : just (var ∷ [] ⇒ unit ∨ unit) ⊢  var ∷ [] ⇒ unit)
    → hyp-free d ≡ true
rrb'''c unit-r = refl
rrb'''c (weakn unit-r) = refl
rrb'''c (weakn (exchng () d)) 
rrb'''c (exchng herex d)  = rrb'''c d 
rrb'''c (exchng (therex ()) d) 


rrk' : (d : just (var ∷ [] ⇒ (unit ∨ unit)) ⊢ var ∷ [] ⇒ (unit ∨ unit))
    → hyp-free d ≡ false
    → (φ : ⟦ just (var ∷ [] ⇒  (unit ∨ unit)) ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (w , tt) ≡ φ (w , tt)
rrk' (∨-r₁ d) pf φ w b rewrite rrb'''c  d with pf 
... | () 
rrk' (∨-r₂ d) pf φ w b rewrite rrb'''c  d with pf 
... | () 
rrk' hyp-use pf φ w b = refl
rrk' (weakn d) pf φ w b rewrite rrb'''d d refl with pf
... | ()
rrk' (exchng herex d) pf φ w b = rrk' d pf φ w b
rrk' (exchng (therex ()) d) pf φ w b



mutual

  rrb'''a :  (d  : just (var ∷ [] ⇒ unit ∨ unit) ⊢
       μ (unit ∨ unit) ∷ var ∷ [] ⇒ unit)
    → hyp-free d ≡ true
  rrb'''a unit-r  = refl
  rrb'''a (μ-l d x ()) 
  rrb'''a (weakn d)  = rrb'''c  d 
  rrb'''a (exchng herex d) = rrb'''a d 
  rrb'''a (exchng (therex herex) d) = rrb'''b d 
  rrb'''a (exchng (therex (therex ())) d) 


  rrb'''b :  (d  : just (var ∷ [] ⇒ unit ∨ unit) ⊢
       var ∷ μ (unit ∨ unit) ∷ [] ⇒ unit)
    → hyp-free d ≡ true
  rrb'''b unit-r = refl
  rrb'''b (weakn d) = rrb'''d d refl 
  rrb'''b (exchng herex d)  = rrb'''b d 
  rrb'''b (exchng (therex herex) d) = rrb'''a d 
  rrb'''b (exchng (therex (therex ())) d) 



rrb''' :  (d  : just (var ∷ [] ⇒ unit ∨ unit) ⊢
     (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit)
  → hyp-free d ≡ true
rrb''' unit-r = refl
rrb''' (∧-l d) = rrb'''a  d 
rrb''' (weakn unit-r)  = refl
rrb''' (weakn (exchng () d)) 
rrb''' (exchng herex d) = rrb''' d 
rrb''' (exchng (therex ()) d) 



rrb'' :  (d  : just (var ∷ [] ⇒ unit ∨ unit) ⊢
     unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit)
  → hyp-free d ≡ true
rrb'' unit-r = refl
rrb'' (∨-l d d₁)  rewrite rrb'''d d refl = rrb''' d₁
rrb'' (weakn d) = rrb'''d d refl
rrb'' (exchng herex d) = rrb'' d 
rrb'' (exchng (therex ()) d) 


mutual

  rroo' : (d : just (var ∷ [] ⇒ (unit ∨ unit)) ⊢ var ∷ μ (unit ∨ unit)  ∷ [] ⇒ (unit ∨ unit))
    → hyp-free d ≡ false
    → (φ : ⟦ just (var ∷ [] ⇒  (unit ∨ unit)) ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (w , μb , tt) ≡ φ (w , tt)
  rroo' (∨-r₁ d) pf φ w b rewrite rrb'''b d with pf
  ... | () 
  rroo' (∨-r₂ d) pf φ w b rewrite rrb'''b d with pf
  ... | () 
  rroo' (weakn d) pf φ w b rewrite rrb'''d d refl with pf
  ... | ()
  rroo' (exchng herex d) pf φ w b = rroo' d pf φ w b
  rroo' (exchng (therex herex) d) pf φ w b = rro' d pf φ w b
  rroo' (exchng (therex (therex ())) d) pf φ w b


  rro' : (d : just (var ∷ [] ⇒ (unit ∨ unit)) ⊢ μ (unit ∨ unit) ∷ var ∷ [] ⇒ (unit ∨ unit))
    → hyp-free d ≡ false
    → (φ : ⟦ just (var ∷ [] ⇒  (unit ∨ unit)) ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (μb , w , tt) ≡ φ (w , tt)
  rro' (∨-r₁ d) pf φ w b rewrite rrb'''a d with pf
  ... | ()
  rro' (∨-r₂ d) pf φ w b rewrite rrb'''a d with pf
  ... | ()
  rro' (μ-l d x ()) pf φ w b
  rro' (weakn (∨-r₁ d)) pf φ w b rewrite rrb'''c d with pf
  ... | ()
  rro' (weakn (∨-r₂ d)) pf φ w b rewrite rrb'''c d with pf
  ... | ()
  rro' (weakn hyp-use) pf φ w b = refl
  rro' (weakn (weakn d)) pf φ w b rewrite rrb'''d d refl with pf
  ... | ()
  rro' (weakn (exchng herex d)) pf φ w b rewrite rrk' d pf φ w b = refl
  rro' (weakn (exchng (therex ()) d)) pf φ w b
  rro' (exchng herex d) pf φ w b = rro' d pf φ w b
  rro' (exchng (therex herex) d) pf φ w b = rroo'  d pf φ w b
  rro' (exchng (therex (therex ())) d) pf φ w b



rrq' : (d : just (var ∷ [] ⇒ (unit ∨ unit)) ⊢  (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ (unit ∨ unit))
  → hyp-free d ≡ false
  → (φ : ⟦ just (var ∷ [] ⇒  (unit ∨ unit)) ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ ( (μb , w) , tt) ≡ φ (w , tt)
rrq' (∧-l d) pf φ w b  = rro' d pf φ w b
rrq' (∨-r₁ d) pf φ w b rewrite rrb''' d with pf
... | () 
rrq' (∨-r₂ d) pf φ w b rewrite rrb''' d with pf
... | ()
rrq' (weakn d) pf φ w b rewrite rrb'''d  d refl with pf
... | () 
rrq' (exchng herex d) pf φ w b = rrq' d pf φ w b
rrq' (exchng (therex ()) d) pf φ w b



rrb' : (d : just (var ∷ [] ⇒ (unit ∨ unit)) ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ (unit ∨ unit))
  → hyp-free d ≡ false
  → (φ : ⟦ just (var ∷ [] ⇒  (unit ∨ unit)) ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ (inj₂ (μb , w) , tt) ≡ φ (w , tt)
rrb' (∨-r₁ d) pf φ w b rewrite rrb'' d  with pf
... | () 
rrb' (∨-r₂ d) pf φ w b rewrite rrb'' d  with pf
... | () 
rrb' (∨-l d d₁) pf φ w b = rrq' d₁ {!!} φ w b
rrb' (weakn d) pf φ w b rewrite rrb'''d d refl with pf
... | () 
rrb' (exchng herex d) pf φ w b = rrb' d pf φ w b
rrb' (exchng (therex ()) d) pf φ w b


rrw111 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ var ∷ [] ⇒ unit)
    → hyp-free d ≡ true
rrw111 unit-r = refl
rrw111 (weakn d) = rrb'''d  d refl
rrw111 (exchng herex d) = rrw111 d
rrw111 (exchng (therex ()) d)    

mutual

  rrw11 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  μ (unit ∨ unit) ∷ var ∷ [] ⇒ unit)
    → hyp-free d ≡ true
  rrw11 unit-r = refl
  rrw11 (μ-l d x ())
  rrw11 (weakn d) = rrw111 d
  rrw11 (exchng herex d) = rrw11 d 
  rrw11 (exchng (therex herex) d) = rrw12 d 
  rrw11 (exchng (therex (therex ())) d)

  rrw12 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  var ∷ μ (unit ∨ unit) ∷ [] ⇒ unit)
    → hyp-free d ≡ true
  rrw12 unit-r = refl
  rrw12 (weakn d) = rrb'''d  d refl
  rrw12 (exchng herex d) = rrw12 d 
  rrw12 (exchng (therex herex) d) = rrw11 d
  rrw12 (exchng (therex (therex ())) d)






rrw1 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit)
  → hyp-free d ≡ true
rrw1 unit-r = refl
rrw1 (∧-l d) = rrw11 d
rrw1 (weakn d) = rrb'''d d refl
rrw1 (exchng herex d) = rrw1 d
rrw1 (exchng (therex ()) d)


rrw211 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ var ∷ [] ⇒ unit ∨ unit)
    → hyp-free d ≡ true
rrw211 (∨-r₁ d) = rrw111  d
rrw211 (∨-r₂ d) = rrw111  d
rrw211 (weakn d) = rrb'''d d refl
rrw211 (exchng herex d) = rrw211 d
rrw211 (exchng (therex ()) d)



mutual

  rrw21 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  μ (unit ∨ unit) ∷ var ∷ [] ⇒ unit ∨ unit)
    → hyp-free d ≡ true
  rrw21 (∨-r₁ d) = rrw11 d
  rrw21 (∨-r₂ d) = rrw11 d
  rrw21 (μ-l d x ())
  rrw21 (weakn d) = rrw211 d
  rrw21 (exchng herex d) = rrw21 d
  rrw21 (exchng (therex herex) d) = rrw22 d
  rrw21 (exchng (therex (therex ())) d)

  rrw22 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  var ∷ μ (unit ∨ unit) ∷ [] ⇒ unit ∨ unit)
    → hyp-free d ≡ true
  rrw22 (∨-r₁ d) = rrw12 d 
  rrw22 (∨-r₂ d) = rrw12 d
  rrw22 (weakn d) = rrb'''d d refl
  rrw22 (exchng herex d) = rrw22 d
  rrw22 (exchng (therex herex) d) = rrw21 d
  rrw22 (exchng (therex (therex ())) d)

rrw2 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit ∨ unit)
  → hyp-free d ≡ true
rrw2 (∧-l d) = rrw21 d 
rrw2 (∨-r₁ d) = rrw1 d
rrw2 (∨-r₂ d) = rrw1 d
rrw2 (weakn d) = rrb'''d d refl
rrw2 (exchng herex d) = rrw2 d
rrw2 (exchng (therex ()) d)


rrw31 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit)
 → hyp-free d ≡ true
rrw31 unit-r = refl
rrw31 (∨-l d d₁) rewrite rrw1 d₁ | rrb'''d d refl = refl
rrw31 (weakn d) = rrb'''d d refl
rrw31 (exchng herex d) = rrw31 d
rrw31 (exchng (therex ()) d)



rrw3 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit ∨ unit)
  → hyp-free d ≡ true
rrw3 (∨-r₁ d) = rrw31 d 
rrw3 (∨-r₂ d) = rrw31 d
rrw3 (∨-l d d₁) rewrite rrw2 d₁ | rrb'''d d refl = refl
rrw3 (weakn d) = rrb'''d d refl
rrw3 (exchng herex d) = rrw3 d
rrw3 (exchng (therex ()) d)



rrw : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit)
  → hyp-free d ≡ true 
rrw unit-r = refl
rrw (∨-l d d₁) rewrite rrb'''d d refl = rrw1 d₁ 
rrw (weakn d) = rrb'''d d refl
rrw (exchng herex d) = rrw d
rrw (exchng (therex ()) d)

mutual
 rrb1121 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ var ∷ μ (unit ∨ unit) ∷ [] ⇒ (unit ∨ unit)) → hyp-free d ≡ true
 rrb1121 (∨-r₁ d) = rrw12 d
 rrb1121 (∨-r₂ d) = rrw12 d
 rrb1121 (weakn d) = rrb'''d d refl
 rrb1121 (exchng herex d) = rrb1121 d
 rrb1121 (exchng (therex herex) d) = rrb1122 d
 rrb1121 (exchng (therex (therex ())) d)

 rrb1122 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ μ (unit ∨ unit) ∷ var ∷ [] ⇒ (unit ∨ unit)) → hyp-free d ≡ true
 rrb1122 (∨-r₁ d) = rrw11 d
 rrb1122 (∨-r₂ d) = rrw11 d
 rrb1122 (μ-l d x ())
 rrb1122 (weakn d) = rrw211 d
 rrb1122 (exchng herex d) = rrb1122 d
 rrb1122 (exchng (therex herex) d) = rrb1121 d
 rrb1122 (exchng (therex (therex ())) d)



rrb1111 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ var ∷ [] ⇒ unit ∨ (unit ∨ unit))
    → hyp-free d ≡ false
    → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (w , tt) ≡ φ (w , tt)
rrb1111 (∨-r₁ d) pf p w b rewrite rrw111 d with pf
... | ()
rrb1111 (∨-r₂ d) pf p w b rewrite rrw211 d with pf
... | ()
rrb1111 hyp-use pf p w b = refl
rrb1111 (weakn d) pf p w b rewrite rrb'''d d refl with pf
... | ()
rrb1111 (exchng herex d) pf p w b = rrb1111 d pf p w b
rrb1111 (exchng (therex ()) d) pf p w b


mutual

  rrb111 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ μ (unit ∨ unit) ∷ var ∷ [] ⇒ unit ∨ (unit ∨ unit))
    → hyp-free d ≡ false
    → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (μb , w , tt) ≡ φ (w , tt)
  rrb111 (∨-r₁ d) pf p w b rewrite rrw11 d with pf
  ... | ()
  rrb111 (∨-r₂ d) pf p w b rewrite rrw21 d with pf
  ... | ()
  rrb111 (μ-l d x ()) pf p w b
  rrb111 (weakn d) pf p w b rewrite rrb1111 d pf p w b = refl
  rrb111 (exchng herex d) pf p w b = rrb111 d pf p w b
  rrb111 (exchng (therex herex) d) pf p w b = rrb112 d pf p  w b
  rrb111 (exchng (therex (therex ())) d) pf p w b


  rrb112 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ var ∷ μ (unit ∨ unit) ∷ [] ⇒ unit ∨ (unit ∨ unit))
    → hyp-free d ≡ false
    → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (w , μb , tt) ≡ φ (w , tt)
  rrb112 (∨-r₁ d) pf p w b rewrite rrw12 d with pf
  ... | ()
  rrb112 (∨-r₂ d) pf p w b rewrite rrb1121 d with pf
  ... | ()
  rrb112 (weakn d) pf p w b rewrite rrb'''d d refl with pf
  ... | ()
  rrb112 (exchng herex d) pf p w b = rrb112 d pf p w b
  rrb112 (exchng (therex herex) d) pf p w b = rrb111 d pf p w b
  rrb112 (exchng (therex (therex ())) d) pf p w b


rrb11 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit ∨ (unit ∨ unit))
  → hyp-free d ≡ false
  → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ ((μb , w) , tt) ≡ φ (w , tt)
rrb11 (∧-l d) pf p w b = rrb111 d pf p w b
rrb11 (∨-r₁ d) pf p w b rewrite rrw1 d with pf
... | ()
rrb11 (∨-r₂ d) pf p w b rewrite rrw2 d with pf
... | ()
rrb11 (weakn d) pf p w b rewrite rrb'''d d refl with pf 
... | () 
rrb11 (exchng herex d) pf p w b = rrb11 d pf p w b
rrb11 (exchng (therex ()) d) pf p w b


rrb1 : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit ∨ (unit ∨ unit))
  → hyp-free d ≡ false
  → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ (inj₂ (μb , w) , tt) ≡ φ (w , tt)
rrb1 (∨-r₁ d) pf p w b rewrite rrw d  with pf
... | () 
rrb1 (∨-r₂ d) pf p w b rewrite rrw3 d with pf
... | () 
rrb1 (∨-l d d₁) pf p w b = rrb11 d₁ {!!}  p w b
rrb1 (weakn d) pf p w b rewrite rrb'''d d refl with pf
... | ()
rrb1 (exchng herex d) pf p w b = rrb1 d pf p w b
rrb1 (exchng (therex ()) d) pf p w b


rrb : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit ∨ (unit ∨ unit))
  → hyp-free d ≡ false
  → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ (inj₂ (μb , w) , tt) ≡ φ (w , tt)
rrb (∨-r₁ d) pf φ w b rewrite rrw d with pf
... | () 
rrb (∨-r₂ d) pf φ w b rewrite rrw3 d with pf
... | ()
rrb (∨-l d d₁) pf φ w b = rrb11 d₁ {!!} φ w b  
rrb (weakn (∨-r₁ d)) pf φ w b rewrite rrb'''d d  refl with pf
... | ()
rrb (weakn (∨-r₂ d)) pf φ w b rewrite rrb'''d d  refl with pf
... | ()
rrb (weakn (exchng () d)) pf φ w b
rrb (exchng herex d) pf φ w b = rrb d pf φ w b
rrb (exchng (therex ()) d) pf φ w b



qqq''' : {Φ : HContext} (d : Φ ⊢ var ∷ [] ⇒ unit ∨ unit)
  → {pf : hyp-free d ≡ true}
  → (φ : ⟦ Φ ⟧H (just Weird))
  → (w : Weird)
  → ⟦ d ⟧ (just Weird) φ (( ws w μf) , tt) ≡  ⟦ d ⟧ (just Weird) φ ( ( ws w μt) , tt)
qqq''' (∨-r₁ d) p w = refl
qqq''' (∨-r₂ d) p w = refl
qqq''' hyp-use {()} p w 
qqq''' (weakn (∨-r₁ d)) p w = refl
qqq''' (weakn (∨-r₂ d)) p w = refl
qqq''' (weakn hyp-use) {()} p w
qqq''' (weakn (exchng () d)) p w
qqq''' (exchng herex d) {pf} p w = qqq''' d {pf} _ _ 
qqq''' (exchng (therex ()) d) p w



kkk''' : {Φ : HContext} (d : Φ ⊢ var ∷ [] ⇒ unit ∨ (unit ∨ unit))
  → {pf : hyp-free d ≡ true}
  → (φ : ⟦ Φ ⟧H (just Weird))
  → (w : Weird)
  → ⟦ d ⟧ (just Weird) φ (( ws w μf) , tt) ≡  ⟦ d ⟧ (just Weird) φ ( ( ws w μt) , tt)
kkk''' (∨-r₁ d) p w = refl
kkk''' (∨-r₂ d) {pf} p w rewrite qqq''' d {pf} p w = refl
kkk''' hyp-use {()} p w 
kkk''' (weakn (∨-r₁ d)) p w = refl
kkk''' (weakn (∨-r₂ d)) p w = refl
kkk''' (weakn hyp-use) {()} p w
kkk''' (weakn (exchng () d)) p w
kkk''' (exchng herex d) {pf} p w = kkk''' d {pf} _ _ 
kkk''' (exchng (therex ()) d) p w


mutual

  qqq''p : {Φ : HContext} (d : Φ ⊢  var ∷ μ (unit ∨ unit)  ∷ [] ⇒ (unit ∨ unit))
    → {pf : hyp-free d ≡ true}
    → (φ : ⟦ Φ ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (ws w μt , μb  , tt) ≡  ⟦ d ⟧ (just Weird) φ ((ws w μf , μb , tt))
  qqq''p (∨-r₁ d) {pf} φ w b = refl
  qqq''p (∨-r₂ d) {pf} φ w b = refl
  qqq''p hyp-use {()} φ w b  
  qqq''p (weakn d) {pf} φ w b = refl
  qqq''p (exchng herex d) {pf} φ w b = qqq''p d {pf} _ w b 
  qqq''p (exchng (therex herex) d) {pf} φ w b = qqq''q d {pf} _ w b 
  qqq''p (exchng (therex (therex ())) d) {pf} φ w b    

  qqq''q : {Φ : HContext} (d : Φ ⊢   μ (unit ∨ unit) ∷ var ∷ [] ⇒ (unit ∨ unit))
    → {pf : hyp-free d ≡ true}
    → (φ : ⟦ Φ ⟧H (just Weird))
    → (w : Weird)
    → (μb : μBool)
    → ⟦ d ⟧ (just Weird) φ (μb , ws w μt , tt) ≡  ⟦ d ⟧ (just Weird) φ ((μb , ws w μf , tt))
  qqq''q (∨-r₁ d) φ w b = refl
  qqq''q (∨-r₂ d) φ w b = refl
  qqq''q hyp-use {()} φ w b    
  qqq''q (μ-l d x ()) φ w b
  qqq''q (weakn d) {pf} φ w b rewrite qqq''' d {pf} φ w = refl 
  qqq''q (exchng herex d) {pf} φ w b = qqq''q d {pf} φ w b
  qqq''q (exchng (therex herex) d) {pf} φ w b = qqq''p d {pf} φ w b
  qqq''q (exchng (therex (therex ())) d) φ w b


qqq'' :  {Φ : HContext}(d : Φ ⊢   (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ (unit ∨ unit))
  → {pf : hyp-free d ≡ true}
  → (φ : ⟦ Φ ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ ((μb , ws w μf) , tt) ≡  ⟦ d ⟧ (just Weird) φ ( (μb , ws w μt) , tt)
qqq'' (∧-l d) {pf} φ w b = sym (qqq''q  d {pf} φ  w b)
qqq'' (∨-r₁ d) φ w b = refl
qqq'' (∨-r₂ d) φ w b = refl
qqq'' hyp-use {()} φ w b    
qqq'' (weakn (∨-r₁ d)) φ w b = refl
qqq'' (weakn (∨-r₂ d)) φ w b = refl
qqq'' (weakn hyp-use) {()} φ w b 
qqq'' (weakn (exchng () d)) φ w b
qqq'' (exchng herex d) {pf} φ w b = qqq'' d {pf} _ _ _
qqq'' (exchng (therex ()) d) φ w b


qqq' : {Φ : HContext}(d : Φ ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ (unit ∨ unit))
  → {pf : hyp-free d ≡ true}
  → (φ : ⟦ Φ ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ (inj₂ (μb , ws w μf) , tt) ≡  ⟦ d ⟧ (just Weird) φ (inj₂ (μb , ws w μt) , tt)
qqq' (∨-r₁ d) φ w b = refl
qqq' (∨-r₂ d) φ w b = refl
qqq' (∨-l d d₁) {pf} φ w b = qqq'' d₁ {closed-2 pf} φ w b 
qqq' (weakn (∨-r₁ d)) φ w b = refl
qqq' hyp-use {()} φ w b 
qqq' (weakn (∨-r₂ d)) φ w b = refl
qqq' (weakn hyp-use) {()} φ w b
qqq' (weakn (exchng () d)) φ w b
qqq' (exchng herex d) {pf} φ w b = qqq' d {pf} φ w b
qqq' (exchng (therex ()) d) φ w b


mutual

 kkk'q : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢   var ∷ μ (unit ∨ unit) ∷ [] ⇒ unit ∨ (unit ∨ unit))
   → {pf : hyp-free d ≡ true}
   → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
   → (w : Weird)
   → (μb : μBool)
   → ⟦ d ⟧ (just Weird) φ ( ws w μf , μb , tt) ≡  ⟦ d ⟧ (just Weird) φ (ws w μt , μb  , tt)
 kkk'q (∨-r₁ d) {pf} φ w b = refl
 kkk'q (∨-r₂ d) {pf} φ w b rewrite qqq''p d {pf} φ w b = refl
 kkk'q (weakn d) {pf} φ w b = refl
 kkk'q (exchng herex d) {pf} φ w b = kkk'q d {pf} _ _ _
 kkk'q (exchng (therex herex) d) {pf} φ w b = kkk'p d {pf} _ _ _ 
 kkk'q (exchng (therex (therex ())) d) {pf} φ w b  


 kkk'p : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢   μ (unit ∨ unit) ∷ var ∷ [] ⇒ unit ∨ (unit ∨ unit))
   → {pf : hyp-free d ≡ true}
   → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
   → (w : Weird)
   → (μb : μBool)
   → ⟦ d ⟧ (just Weird) φ ( μb , ws w μf , tt) ≡  ⟦ d ⟧ (just Weird) φ (μb , ws w μt , tt)
 kkk'p (∨-r₁ d) {pf} φ w b = refl
 kkk'p (∨-r₂ d) {pf} φ w b rewrite qqq''q d {pf} φ w b = refl
 kkk'p (μ-l d x ()) {pf} φ w b
 kkk'p (weakn d) {pf} φ w b rewrite kkk'''  d {pf} φ w = refl
 kkk'p (exchng herex d) {pf} φ w b = kkk'p d {pf} _ _ _
 kkk'p (exchng (therex herex) d) {pf} φ w b = kkk'q d {pf} _ _ _
 kkk'p (exchng (therex (therex ())) d) {pf} φ w b



kkk' : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢   (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit ∨ (unit ∨ unit))
  → {pf : hyp-free d ≡ true}
  → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ ( (μb , ws w μf) , tt) ≡  ⟦ d ⟧ (just Weird) φ ((μb , ws w μt) , tt)
kkk' (∧-l d) {pf} φ w b = kkk'p d {pf} φ w b
kkk' (∨-r₁ d) {pf} φ w b = refl
kkk' (∨-r₂ d) {pf} φ w b rewrite qqq'' d {pf} φ w b = refl
kkk' (weakn (∨-r₁ d)) {pf} φ w b = refl
kkk' (weakn (∨-r₂ d)) {pf} φ w b = refl
kkk' (weakn (exchng () d)) {pf} φ w b
kkk' (exchng herex d) {pf} φ w b = kkk' d {pf} _ _ _
kkk' (exchng (therex ()) d) {pf} φ w b  


kkk : (d : just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ unit ∨ (unit ∨ unit))
  → {pf : hyp-free d ≡ true}
  → (φ : ⟦ just (var ∷ [] ⇒ unit ∨ (unit ∨ unit)) ⟧H (just Weird))
  → (w : Weird)
  → (μb : μBool)
  → ⟦ d ⟧ (just Weird) φ (inj₂ (μb , ws w μf) , tt) ≡  ⟦ d ⟧ (just Weird) φ (inj₂ (μb , ws w μt) , tt) 
kkk (∨-r₁ d) φ w b = refl
kkk  (∨-r₂ d) {pf} φ w b rewrite qqq' {just (var ∷ [] ⇒ unit ∨ (unit ∨ unit))} d {pf} φ w b =   refl
kkk (∨-l d d₁) {pf} φ w b = kkk' d₁  {closed-2 pf} φ w b
kkk (weakn (∨-r₁ d)) φ w b = refl
kkk (weakn (∨-r₂ d)) φ w b = refl
kkk (weakn (exchng () d)) φ w b
kkk (exchng herex d) {pf} φ w b = kkk d {pf} φ w b
kkk (exchng (therex ()) d) φ w b





mutual

  brru : (d : nothing ⊢ WeirdRaw ∷ [] ⇒ unit ∨ BoolRaw) → ⟦ d ⟧ nothing  tt  (ws (ws wb μf) μt , tt) ≡ ⟦ d ⟧ nothing  tt  (ws (ws wb μt) μt , tt)
  brru (∨-r₁ d) = refl
  brru (∨-r₂ d) rewrite brr d = refl
  brru (μ-l d x x₁) with (hyp-free d)  | inspect hyp-free  d
  brru (μ-l d x x₁) | false | Reveal_·_is_.[ eq ] rewrite  rrb d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (ws wb μf) μt
     | rrb d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (wb) μf

     | rrb d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (ws wb μt) μt
     | rrb d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (wb) μt
    =  refl
  brru (μ-l d x x₁) | true | Reveal_·_is_.[ eq ] = kkk d {eq} _ _ _
  brru (weakn (∨-r₁ d)) = refl
  brru (weakn (∨-r₂ d)) = refl
  brru (weakn (exchng x d)) = refl
  brru (exchng herex d) = brru d
  brru (exchng (therex ()) d)

  brr : (d : nothing ⊢ WeirdRaw ∷ [] ⇒ BoolRaw) → ⟦ d ⟧ nothing  tt  (ws (ws wb μf) μt , tt) ≡ ⟦ d ⟧ nothing  tt  (ws (ws wb μt) μt , tt)
  brr (∨-r₁ d) = refl
  brr (∨-r₂ d) = refl
  brr (μ-l d x x₁) with (hyp-free d)  | inspect hyp-free  d
  brr (μ-l d x x₁) | false | Reveal_·_is_.[ eq ] rewrite  rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (ws wb μf) μt
     | rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (wb) μf

     | rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (ws wb μt) μt
     | rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (wb) μt
    =  refl
  brr (μ-l d x x₁) | true | Reveal_·_is_.[ eq ] = qqq' d {eq} _ _ _

  brr (weakn (∨-r₁ d)) = refl
  brr (weakn (∨-r₂ d)) = refl
  brr (weakn (exchng () d))
  brr (exchng herex d) = brr d
  brr (exchng (therex ()) d)


{-
mutual

  dqqq''p : {Φ : HContext} (d : Φ ⊢  var ∷ μ (unit ∨ unit)  ∷ [] ⇒ (unit ∨ unit))
    → {pf : hyp-free d ≡ true}
    → {pf'' : isJust Φ ≡ true}    
    → (φ : ⟦ Φ ⟧H (just Weird))
    → (w : Weird)
    → ⟦ d ⟧ (just Weird) φ (w , μf , tt) ≡  ⟦ d ⟧ (just Weird) φ (w , μt , tt)
  dqqq''p (∨-r₁ d) {pf} φ w  = refl
  dqqq''p (∨-r₂ d) {pf} φ w  = refl
  dqqq''p hyp-use {()} φ w   
  dqqq''p (weakn (∨-r₁ d)) {pf} φ w = refl
  dqqq''p (weakn (∨-r₂ d)) {pf} φ w = refl
  dqqq''p (weakn (μ-l d x x₁)) {pf} φ w = {!!}
  dqqq''p (weakn hyp-use) {()} φ w
  dqqq''p (weakn (weakn d)) {pf} φ w = refl
  dqqq''p (weakn (exchng x d)) {pf} φ w = {!!}
  dqqq''p (exchng herex d) {pf}{pf'} φ w  = dqqq''p d {pf}{pf'} _ w  
  dqqq''p (exchng (therex herex) d) {pf}{pf'} φ w  = dqqq''q d {pf}{pf'} _ w 
  dqqq''p (exchng (therex (therex ())) d) {pf} φ w     


  dqqq''q : {Φ : HContext} (d : Φ ⊢   μ (unit ∨ unit) ∷ var ∷ [] ⇒ (unit ∨ unit))
    → {pf : hyp-free d ≡ true}
    → {pf'' : isJust Φ ≡ true}
    → (φ : ⟦ Φ ⟧H (just Weird))
    → (w : Weird)
    → ⟦ d ⟧ (just Weird) φ (μf , w , tt) ≡  ⟦ d ⟧ (just Weird) φ ((μt , w , tt))
  dqqq''q (∨-r₁ d) φ w = refl
  dqqq''q (∨-r₂ d) φ w  = refl
  dqqq''q hyp-use {()} φ w 
  dqqq''q (μ-l d x ()) φ w 
  dqqq''q (weakn d) {pf} φ w  rewrite qqq''' d {pf} φ w = refl 
  dqqq''q (exchng herex d) {pf}{pf'} φ w  = dqqq''q d {pf}{pf'} φ w 
  dqqq''q (exchng (therex herex) d) {pf} {pf'} φ w  = dqqq''p d {pf}{pf'} φ w 
  dqqq''q (exchng (therex (therex ())) d) φ w 


dqqq'' :  {Φ : HContext}(d : Φ ⊢   (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ (unit ∨ unit))
  → {pf : hyp-free d ≡ true}
  → {pf'' : isJust Φ ≡ true}  
  → (φ : ⟦ Φ ⟧H (just Weird))
  → (w : Weird)
  → ⟦ d ⟧ (just Weird) φ ((μf , w) , tt) ≡  ⟦ d ⟧ (just Weird) φ ( (μt , w) , tt)
dqqq'' (∧-l d) {pf} {pf'} φ w  = dqqq''q d {pf}{pf'}  _ _
dqqq'' (∨-r₁ d) φ w  = refl
dqqq'' (∨-r₂ d) φ w  = refl
dqqq'' hyp-use {()} φ w     
dqqq'' (weakn (∨-r₁ d)) φ w  = refl
dqqq'' (weakn (∨-r₂ d)) φ w  = refl
dqqq'' (weakn hyp-use) {()} φ w 
dqqq'' (weakn (exchng () d)) φ w 
dqqq'' (exchng herex d) {pf} {pf'} φ w  = dqqq'' d {pf} {pf'} _ _ 
dqqq'' (exchng (therex ()) d) φ w 


dqqq' : {Φ : HContext}(d : Φ ⊢  unit ∨ (μ (unit ∨ unit) ∧ var) ∷ [] ⇒ (unit ∨ unit))
  → {pf : hyp-free d ≡ true}
  → {pf'' : isJust Φ ≡ true}
  → (φ : ⟦ Φ ⟧H (just Weird))
  → (w : Weird)
  → ⟦ d ⟧ (just Weird) φ (inj₂ (μf , w) , tt) ≡  ⟦ d ⟧ (just Weird) φ (inj₂ (μt , w) , tt)

dqqq' (∨-r₁ d) φ w  = refl
dqqq' (∨-r₂ d) φ w  = refl
dqqq' {Φ} (∨-l d d₁) {pf} {pf'} φ w = dqqq'' {Φ} d₁ {closed-2 pf}{pf'}  _ _
dqqq' (weakn (∨-r₁ d)) φ w = refl
dqqq' hyp-use {()} φ w  
dqqq' (weakn (∨-r₂ d)) φ w = refl
dqqq' (weakn hyp-use) {()} φ w 
dqqq' (weakn (exchng () d)) φ w 
dqqq' (exchng herex d) {pf} {pf''} φ w  = dqqq' d {pf} {pf''} φ w 
dqqq' (exchng (therex ()) d) φ w 



mutual
  brrum : (d : nothing ⊢ WeirdRaw ∷ [] ⇒ BoolRaw) → ⟦ d ⟧ nothing  tt  ( (ws wb μf) , tt) ≡ ⟦ d ⟧ nothing  tt  ((ws wb μt) , tt)
  brrum (μ-l d x x₁) with (hyp-free d)  | inspect hyp-free  d
  brrum (μ-l d x x₁) | false | Reveal_·_is_.[ eq ]  rewrite  rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (ws wb μf) μt
   |  rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (wb) μf
   | rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (ws wb μt) μt
     | rrb' d eq (λ q →
         Fold
         (λ Y rf rv w → ⟦ d ⟧ (just Y) (λ q₁ → rf (proj₁ q₁) w) (rv , w))
         (proj₁ q) tt) (wb) μt  = refl
  brrum (μ-l d x x₁) | true | Reveal_·_is_.[ eq ] = dqqq' d {eq} {refl} _ _ 
  brrum (∨-r₁ d) = refl
  brrum (∨-r₂ d) = refl
  brrum (weakn (∨-r₁ d)) = refl
  brrum (weakn (∨-r₂ d)) = refl
  brrum (weakn (exchng () d))
  brrum (exchng herex d) = brrum d
  brrum (exchng (therex ()) d)
-}
