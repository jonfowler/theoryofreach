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
 
VarSet : Set 
VarSet = ℕ
  
Var : VarSet → Set
Var = Fin 

Empty : VarSet → Set
Empty V = V ≡ 0 

data Val (X : VarSet) : Set where
  Z : Val X
  S : Val X → Val X
  fvar : Var X → Val X

--Var? : (V : VarSet) → Dec (Var V)
--Var? ∅ = no (λ ())
--Var? V1 = yes here -- (λ ¬e → ¬e here) 
--Var? (X ∪ Y) with Var? X | Var? Y 
--Var? (X ∪ Y) | yes p1 | b = yes (inL p1) -- yes (λ {(inL x) → p1 x ; (inR y) → p2 y})
--Var? (X ∪ Y) | no ¬p | yes p = yes (inR p)
--Var? (X ∪ Y) | no ¬p | no ¬p₁ = no (λ {(inL x) → ¬p x; (inR x) → ¬p₁ x}) -- no (λ ¬e → ¬p (λ x → ¬e (inL x)))

-- Type of Substitutions, Sub_{X→Y} in paper
_⇀_ : VarSet → VarSet → Set
_⇀_ X Y = Var X → Val Y

Inp : VarSet → Set
Inp X = X ⇀ 0 

-- Monad on Val, bind is application of substitution
_>>=_ : {X Y : VarSet} →  Val X → (X ⇀ Y) → Val Y
fvar x >>= f = f x
Z >>= f = Z
S a >>= f = S (a >>= f)

-- The identity substitution
return : {X : VarSet} → X ⇀ X 
return = fvar

-- Composition of substitutions (kleisli composition)
_>=>_ : {X Y Z : VarSet} → (X ⇀ Y) → (Y ⇀ Z) → X ⇀ Z
_>=>_ f g a = f a >>= g

-- The Monad laws
>>=-left : {X Y : VarSet} → (x : Var X) → (f : (X ⇀ Y)) → return x >>= f ≡ f x
>>=-left x f = refl

>>=-right : {X : VarSet} → (a : Val X) → a >>= return ≡ a
>>=-right (fvar x) = refl
>>=-right Z = refl
>>=-right (S a) = cong S (>>=-right a) 

>>=-assoc : {X Y Z : VarSet} → (a : Val X) → (f : X ⇀ Y) → (g : Y ⇀ Z) → 
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


 

