module Func.LazyNarrowing where

open import Basic.Helpful
open import Basic.Subs

open import Func.Exp

open import Data.Vec hiding (_>>=_)
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Function

-- Suspended Expression - Section ?
data _⊸_ {V : ℕ}{Γ : Cxt V}{X : VarSet} : {t : Type} → Exp Γ X t → Var X → Set where
  susp : (x : Var X) → fvar x ⊸ x
  subj-susp : ∀{t}{x : Var X}{e : Exp Γ X Nat}{e₀ : Exp Γ X t}{eₛ : Exp (Nat ∷ Γ) X t} → 
                  e ⊸ x → case e alt₀ e₀ altₛ eₛ ⊸ x
  fun-susp : ∀{u t}{x : Var X}{f : Exp Γ X (u ↠ t)}{e : Exp Γ X u} → 
                  f ⊸ x → app f e ⊸ x
  fix-susp : ∀{t}{x : Var X}{f : Exp Γ X (t ↠ t)} → 
                  f ⊸ x → fix f ⊸ x

  
-- Minimal one-point bindings
data MinVal : {X : VarSet} → Val X → Set where
   bindZ : MinVal {∅} Z
   bindS : MinVal {V1} (S (fvar here))

-- Definiton of lazy narrowing set
data Narr {X : VarSet} (x : Var X) : {Y : VarSet} → X ⇀ Y → Set where
   narr : ∀{Y} {a : Val Y} → MinVal a → Narr x (x / a)
   
-- The functor laws for ⟦_⟧
⟦⟧-return : ∀{V X t}{Γ : Cxt V} → (e : Exp Γ X t) → e ⟦ return ⟧ ≡ e
⟦⟧-return Z = refl
⟦⟧-return (S e) = cong S (⟦⟧-return e)
⟦⟧-return • = refl
⟦⟧-return (var x o) = refl
⟦⟧-return (fvar x) = refl
⟦⟧-return (case e alt₀ e₀ altₛ eₛ) = cong₃ case_alt₀_altₛ_ (⟦⟧-return e) (⟦⟧-return e₀) (⟦⟧-return eₛ)
⟦⟧-return (app f e) = cong₂ app (⟦⟧-return f) (⟦⟧-return e)
⟦⟧-return (lam f) = cong lam (⟦⟧-return f)
⟦⟧-return (fix f) = cong fix (⟦⟧-return f)

⟦⟧-var :  ∀{V X Y}{Γ : Cxt V} → (x : Var X) → (σ : X ⇀ Y)
          → _⟦_⟧ {Γ = Γ} (fvar x) σ ≡ ⌈ σ x ⌉
⟦⟧-var x f = refl

embed-lift : ∀{V X Y}{Γ : Cxt V} → (a : Val X) → (σ : X ⇀ Y) → ⌈ a ⌉ ⟦ σ ⟧ ≡ ⌈_⌉ {Γ = Γ} (a >>= σ)
embed-lift (fvar x) σ = refl
embed-lift Z σ = refl
embed-lift (S a) σ = cong S (embed-lift a σ)

⟦⟧-func :  ∀{V X Y Z t}{Γ : Cxt V} → (e : Exp Γ X t) → (σ : X ⇀ Y) → (σ' : Y ⇀ Z) 
        → e ⟦ σ ⟧ ⟦ σ' ⟧ ≡ e ⟦ σ >=> σ' ⟧
⟦⟧-func Z σ σ' = refl
⟦⟧-func (S e) σ σ' = cong S (⟦⟧-func e σ σ')
⟦⟧-func • σ σ' = refl
⟦⟧-func (var x o) σ σ' = refl
⟦⟧-func (fvar x) σ σ' = embed-lift (σ x) σ'
⟦⟧-func (case e alt₀ e₁ altₛ e₂) σ σ' = cong₃ case_alt₀_altₛ_ (⟦⟧-func e σ σ') (⟦⟧-func e₁ σ σ') (⟦⟧-func e₂ σ σ')
⟦⟧-func (app f e) σ σ' = cong₂ app (⟦⟧-func f σ σ') (⟦⟧-func e σ σ') 
⟦⟧-func (lam f) σ σ' = cong lam (⟦⟧-func f σ σ') 
⟦⟧-func (fix f) σ σ' = cong fix (⟦⟧-func f σ σ')

 -- Defintion of lazy narrowing small step reduction
data _⇝_ {V : ℕ}{Γ : Cxt V}{X : VarSet}{t : Type} 
            : {Y : VarSet} → Exp Γ X t → Exp Γ Y t × X ⇀ Y → Set where 
  narr : ∀{e x Y} → e ⊸ x → (σ : X ⇀ Y) → Narr x σ → e ⇝ (e ⟦ σ ⟧ , σ)
  red : ∀{e e'} → (r : e ↦ e') → e ⇝ (e' , return)
  
-- Sequencing lazy narrowing steps
data _⇝⁺_ {V : ℕ}{Γ : Cxt V}{X : VarSet}{t : Type} : {Y : VarSet} → Exp Γ X t → Exp Γ Y t × X ⇀ Y → Set where 
   [] : ∀ {e} → (τ : X ⇀ ∅) → e ⇝⁺ (e ⟦ τ ⟧ , τ)
   _∷_ : ∀ {e Y Z e' e'' σ τ} →
         _⇝_ {Y = Y} e (e' , σ) → _⇝⁺_ {Y = Z} e' (e'' , τ) → e ⇝⁺ (e'' , σ >=> τ)
          
-- Lazy narrowing reachability
data ReachF {V : ℕ}{Γ : Cxt V}{X : VarSet}{t : Type}(e : Exp Γ X t) (τ : Inp X) : Set where
  reachF : e ⇝⁺ (• , τ) → ReachF e τ
 
