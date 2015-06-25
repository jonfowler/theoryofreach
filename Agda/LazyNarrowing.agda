module LazyNarrowing where

open import Exp
open import Helpful
open import Subs

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Function

-- Suspended Expression - Section ?
data _⊸_ {V : ℕ}{X : VarSet} : Exp V X → Var X → Set where
  susp : (x : Var X) → fvar x ⊸ x
  subj-susp : ∀{e e₀ eₛ x} → e ⊸ x → case e alt₀ e₀ altₛ eₛ ⊸ x
  
-- Updating Variable Set
_[_//_] : (X : VarSet) → (x : Var X) → VarSet → VarSet
suc X [ zero // Y ] = Y + X
suc X [ suc x // Y ] = suc (X [ x // Y ])

-- Point update substitution
_/_ : {X Y : VarSet} → (x : Var X) → Val Y → X ⇀ (X [ x // Y ]) 
_/_ {suc X}{Y} zero a zero = a >>= (λ y → fvar (inject+ X y))
_/_ {suc X}{Y} zero a (suc x') = fvar (raise Y x') 
_/_ (suc x) a zero = fvar zero
_/_ (suc x) a (suc x') = ((x / a) x') >>= (λ y → fvar (suc y))  

-- Minimal one-point bindings
data MinVal : {X : VarSet} → Val X → Set where
   bindZ : MinVal {0} Z
   bindS : MinVal {1} (S (fvar zero))

-- Definiton of lazy narrowing set
data Narr {X : VarSet} (x : Var X) : {Y : VarSet} → X ⇀ Y → Set where
   narr : ∀{Y} {a : Val Y} → MinVal a → Narr x (x / a)
   
-- The functor laws for ⟦_⟧
⟦⟧-id : ∀{V X} → (e : Exp V X) → e ⟦ return ⟧ ≡ e
⟦⟧-id Z = refl
⟦⟧-id (S e) = cong S (⟦⟧-id e)
⟦⟧-id (var x) = refl
⟦⟧-id (fvar x) = refl
⟦⟧-id (case e alt₀ e₀ altₛ eₛ) = cong₃ case_alt₀_altₛ_ (⟦⟧-id e) (⟦⟧-id e₀) (⟦⟧-id eₛ)

⟦⟧-var :  ∀{V X Y} → (x : Var X) → (σ : X ⇀ Y)
          → _⟦_⟧ {V} (fvar x) σ ≡ ⌈ σ x ⌉
⟦⟧-var x f = refl

embed-func : ∀{V X Y} → (a : Val X) → (σ : X ⇀ Y) → ⌈ a ⌉ ⟦ σ ⟧ ≡ ⌈_⌉ {V} (a >>= σ)
embed-func (fvar x) σ = refl
embed-func Z σ = refl
embed-func (S a) σ = cong S (embed-func a σ)

⟦⟧-func :  ∀{V X Y Z} → (e : Exp V X) → (σ : X ⇀ Y) → (σ' : Y ⇀ Z) 
        → e ⟦ σ ⟧ ⟦ σ' ⟧ ≡ e ⟦ σ >=> σ' ⟧
⟦⟧-func Z σ σ' = refl
⟦⟧-func (S e) σ σ' = cong S (⟦⟧-func e σ σ')
⟦⟧-func (var x) σ σ' = refl
⟦⟧-func (fvar x) σ σ' = embed-func (σ x) σ'
⟦⟧-func (case e alt₀ e₁ altₛ e₂) σ σ' = cong₃ case_alt₀_altₛ_ (⟦⟧-func e σ σ') (⟦⟧-func e₁ σ σ') (⟦⟧-func e₂ σ σ')

 

data _⇝_ {V : ℕ}{X : VarSet} : {Y : VarSet} → Exp V X → Exp V Y × X ⇀ Y → Set where 
  narr : ∀{e x Y} → e ⊸ x → (σ : X ⇀ Y) → Narr x σ → e ⇝ (e ⟦ σ ⟧ , σ)
  red : ∀{e e'} → (r : e ↦ e') → e ⇝ (e' , return)
  
data _⇝⁺_ {V : ℕ}{X : VarSet} : {Y : VarSet} → Exp V X → Exp V Y × X ⇀ Y → Set where 
   [] : ∀ {e Y} → (o : Empty Y) → (τ : X ⇀ Y) → e ⇝⁺ (e ⟦ τ ⟧ , τ)
   _∷_ : ∀ {e Y Z e' e'' σ τ} →
         _⇝_ {Y = Y} e (e' , σ) → _⇝⁺_ {Y = Z} e' (e'' , τ) → e ⇝⁺ (e'' , σ >=> τ)
          
 
