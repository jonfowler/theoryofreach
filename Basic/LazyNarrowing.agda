module Basic.LazyNarrowing where

open import Basic.Exp
open import Basic.Helpful
open import Basic.Subs

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
  
-- Minimal one-point bindings
data MinVal : {X : VarSet} → Val X → Set where
   bindZ : MinVal {∅} Z
   bindS : MinVal {V1} (S (fvar here))

-- Definiton of lazy narrowing set
data Narr {X : VarSet} (x : Var X) : {Y : VarSet} → X ⇀ Y → Set where
   narr : ∀{Y} {a : Val Y} → MinVal a → Narr x (x / a)
   
-- The functor laws for ⟦_⟧
⟦⟧-return : ∀{V X} → (e : Exp V X) → e ⟦ return ⟧ ≡ e
⟦⟧-return Z = refl
⟦⟧-return (S e) = cong S (⟦⟧-return e)
⟦⟧-return • = refl
⟦⟧-return (var x) = refl
⟦⟧-return (fvar x) = refl
⟦⟧-return (case e alt₀ e₀ altₛ eₛ) = cong₃ case_alt₀_altₛ_ (⟦⟧-return e) (⟦⟧-return e₀) (⟦⟧-return eₛ)

⟦⟧-var :  ∀{V X Y} → (x : Var X) → (σ : X ⇀ Y)
          → _⟦_⟧ {V} (fvar x) σ ≡ ⌈ σ x ⌉
⟦⟧-var x f = refl

embed-lift : ∀{V X Y} → (a : Val X) → (σ : X ⇀ Y) → ⌈ a ⌉ ⟦ σ ⟧ ≡ ⌈_⌉ {V} (a >>= σ)
embed-lift (fvar x) σ = refl
embed-lift Z σ = refl
embed-lift (S a) σ = cong S (embed-lift a σ)

⟦⟧-func :  ∀{V X Y Z} → (e : Exp V X) → (σ : X ⇀ Y) → (σ' : Y ⇀ Z) 
        → e ⟦ σ ⟧ ⟦ σ' ⟧ ≡ e ⟦ σ >=> σ' ⟧
⟦⟧-func Z σ σ' = refl
⟦⟧-func (S e) σ σ' = cong S (⟦⟧-func e σ σ')
⟦⟧-func • σ σ' = refl
⟦⟧-func (var x) σ σ' = refl
⟦⟧-func (fvar x) σ σ' = embed-lift (σ x) σ'
⟦⟧-func (case e alt₀ e₁ altₛ e₂) σ σ' = cong₃ case_alt₀_altₛ_ (⟦⟧-func e σ σ') (⟦⟧-func e₁ σ σ') (⟦⟧-func e₂ σ σ')

 -- Defintion of lazy narrowing small step reduction
data _⇝_ {V : ℕ}{X : VarSet} : {Y : VarSet} → Exp V X → Exp V Y × X ⇀ Y → Set where 
  narr : ∀{e x Y} → e ⊸ x → (σ : X ⇀ Y) → Narr x σ → e ⇝ (e ⟦ σ ⟧ , σ)
  red : ∀{e e'} → (r : e ↦ e') → e ⇝ (e' , return)
  
-- Sequencing lazy narrowing steps
data _⇝⁺_ {V : ℕ}{X : VarSet} : {Y : VarSet} → Exp V X → Exp V Y × X ⇀ Y → Set where 
   [] : ∀ {e} → (τ : X ⇀ ∅) → e ⇝⁺ (e ⟦ τ ⟧ , τ)
   _∷_ : ∀ {e Y Z e' e'' σ τ} →
         _⇝_ {Y = Y} e (e' , σ) → _⇝⁺_ {Y = Z} e' (e'' , τ) → e ⇝⁺ (e'' , σ >=> τ)
          
-- Lazy narrowing reachability
data ReachF {V : ℕ}{X : VarSet} (e : Exp V X) (τ : Inp X) : Set where
  reachF : e ⇝⁺ (• , τ) → ReachF e τ
 
