

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


data _∈_,_  {X : Set} : X → List X → List X → Set where
  herex : {x : X}{xs : List X} → x ∈ (x ∷ xs) , xs
  therex : {x y : X}{xs ys : List X} → x ∈ xs , ys → x ∈ (y ∷ xs) , (y ∷ ys)


blah : 1 ∈ (2 ∷ 3 ∷ 4 ∷ 1 ∷ 5 ∷ 6 ∷ 7 ∷ []) , (2 ∷ 3 ∷  4 ∷ 5 ∷ 6 ∷ 7 ∷ [])
blah = therex (therex (therex herex))

_⊆_ : {X : Set} → List X → List X → Set
xs ⊆ ys = ∀ x → x ∈ xs → x ∈ ys

{-
DupFree : {X : Set} → List X → Set
DupFree xs = ∀ x → (p1 p2 : x ∈ xs) → p1 ≡ p2





postulate
  dupFreeList : {X : Set} → List X → List X
  dupFreeSub : {X : Set} → (l : List X) → dupFreeList l ⊆ l
  dupFreeDF  : {X : Set} → (l : List X) → DupFree (dupFreeList l)
  
  pr1 : {X : Set} → (x : X) → (l : List X) → dupFreeList (x ∷ x ∷ l) ≡ dupFreeList (x ∷ l)
-}
