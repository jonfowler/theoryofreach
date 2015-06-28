module Subs where

open import Helpful

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Function
open import Relation.Nullary 


postulate ext : {A B : Set}{f g : A → B} →  ((x : A) → f x ≡ g x) → f ≡ g
 
data VarSet : Set where
  ∅ : VarSet
  V1 : VarSet
  _∪_ : VarSet → VarSet → VarSet
  
data Var : VarSet → Set where
  here : Var V1
  inL : ∀{X Y} → Var X → Var (X ∪ Y) 
  inR : ∀{X Y} → Var Y → Var (X ∪ Y) 
  
Empty : VarSet → Set
Empty V = ¬ (Var V) 

data ValG (A : Set) : Set where
  Z : ValG A 
  S : ValG A → ValG A
  fvar : A → ValG A 
  
Val : VarSet → Set
Val X = ValG (Var X)

valMap : {A B : Set} → (A → B) → ValG A → ValG B
valMap f Z = Z
valMap f (S v) = S (valMap f v)
valMap f (fvar x) = fvar (f x)

-- Type of Substitutions, Sub_{X→Y} in paper

SubG : Set → Set → Set
SubG A B = A → ValG B 

_⇀_ : VarSet → VarSet → Set
_⇀_ X Y = SubG (Var X) (Var Y)

Inp : VarSet → Set
Inp X = X ⇀ ∅ 

-- Monad on Val, bind is application of substitution
_>>=_ : {X Y : Set} →  ValG X → SubG X Y → ValG Y
fvar x >>= σ = σ x
Z >>= σ = Z
S a >>= σ = S (a >>= σ)

-- The identity substitution
return : {X : Set} → SubG X X 
return = fvar 

-- Composition of substitutions (kleisli composition)
_>=>_ : {X Y Z : Set} → SubG X Y → SubG Y Z → SubG X Z
_>=>_ f g a = f a >>= g

-- The Monad laws
>>=-left : {X Y : Set} → (x : X) → (f : SubG X Y) → return x >>= f ≡ f x
>>=-left x f = refl

>>=-right : {X : Set} → (a : ValG X) → a >>= return ≡ a
>>=-right (fvar x) = refl
>>=-right Z = refl
>>=-right (S a) = cong S (>>=-right a) 

>>=-assoc : {X Y Z : Set} → (a : ValG X) → (f : SubG X Y) → (g : SubG Y Z) → 
             (a >>= f) >>= g ≡ a >>= (λ a → (f a >>= g))
>>=-assoc (fvar x) f g = refl
>>=-assoc Z f g = refl
>>=-assoc (S a) f g = cong S (>>=-assoc a f g)


_⊑ₚ_ : ∀{X Y} → Val X → Val Y → Set 
n ⊑ₚ m = ∃ (λ σ → m ≡ n >>= σ)

_⊑_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
σ ⊑ τ = ∃ (λ σ' → τ ≡ σ >=> σ')

_⊏_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
σ ⊏ τ = σ ⊑ τ × ¬ (τ ⊑ σ)


 

