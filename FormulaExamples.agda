
module FormulaExamples where

open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import Data.Unit

open import Formula
open import LFP


{- Booleans  -}
BoolRaw : Formula
BoolRaw = unit ∨ unit


𝔹 : Set
𝔹 = ⟦ BoolRaw ⟧F nothing

t : 𝔹
t = inj₁ tt

f : 𝔹
f = inj₂ tt


{- Naturals -}
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

hb : ∀ b → Nat2ℕ (ℕ2Nat b) ≡ b
hb zero = refl
hb (suc b) rewrite hb b = refl
