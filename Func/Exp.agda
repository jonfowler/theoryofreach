module Func.Exp where

open import Basic.Helpful
open import Basic.Subs

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Function

data Type : Set where
  Nat : Type
  _↠_ : Type -> Type -> Type
  
Cxt : ℕ → Set 
Cxt = Vec Type 

-- The expression grammar with free variables, Exp V X has de bruijn index V and free variables given by X.
data Exp {V : ℕ} (Γ : Cxt V) (X : VarSet) : Type → Set where
  Z : Exp Γ X Nat
  S :  Exp Γ X Nat → Exp Γ X Nat
  • : ∀{t} → Exp Γ X t
  app : ∀{u t} → Exp Γ X (u ↠ t) → Exp Γ X u → Exp Γ X t
  lam : ∀{u t} → Exp (u ∷ Γ) X t → Exp Γ X (u ↠ t)
  case_alt₀_altₛ_ : ∀{t} → (e : Exp Γ X Nat) → (e₀ : Exp Γ X t) 
                             → (eₛ : Exp (Nat ∷ Γ) X t) → Exp Γ X t
  var : ∀{t} → (v : Fin V) → (Γ [ v ]= t)  → Exp Γ X t
  fvar : (x : Var X) → Exp Γ X Nat
  
-- de bruijn substitution, defined at end of file.
_⟪_⟫ : ∀{V X u t}{Γ : Cxt V} → Exp (u ∷ Γ) X t → Exp Γ X u → Exp Γ X t

-- the small step semantics for the language.
data _↦_ {V : ℕ}{Γ : Cxt V}{X : VarSet} {t : Type} : Exp Γ X t → Exp Γ X t → Set where
  caseZ : ∀ e₀ eₛ → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : ∀ e e₀ eₛ → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  case• : ∀ e₀ eₛ → case • alt₀ e₀ altₛ eₛ ↦ • 
  prom : ∀{e e' e₀ eₛ} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
  subs : ∀{u f}{e : Exp Γ X u} → app (lam f) e ↦ f ⟪ e ⟫
  promsub : ∀{u f f'}{e : Exp Γ X u}   → f ↦ f' → app f e ↦ app f' e
               
-- Transistive closure
data _↦*_ {V : ℕ}{Γ : Cxt V}{X : VarSet}{t : Type} : Exp Γ X t → Exp Γ X t → Set where
  [] : ∀{e} → e ↦* e 
  _∷_ : ∀{e e' e''} → (r : e ↦ e') → (r* : e' ↦* e'') → e ↦* e''
  
-- Embedding of values into expressions.
⌈_⌉ : ∀{V X}{Γ : Cxt V} → Val X → Exp Γ X Nat
⌈ fvar x ⌉ = fvar x
⌈ Z ⌉ = Z
⌈ S a ⌉ = S ⌈ a ⌉
  
-- The application of a free variable substitution, σ : X ⇀ Y , to a expression
_⟦_⟧ : ∀{V X Y t}{Γ : Cxt V} →  (e : Exp Γ X t) → X ⇀ Y → Exp Γ Y t
Z ⟦ σ ⟧ = Z
S e ⟦ σ ⟧ = S (e ⟦ σ ⟧)
• ⟦ σ ⟧ = •
var x o ⟦ σ ⟧ = var x o
fvar x ⟦ σ ⟧ = ⌈ σ x ⌉
(case e alt₀ e₀ altₛ eₛ) ⟦ σ ⟧ = case e ⟦ σ ⟧ alt₀ e₀ ⟦ σ ⟧ altₛ eₛ ⟦ σ ⟧ 
app f e ⟦ σ ⟧ = app (f ⟦ σ ⟧) (e ⟦ σ ⟧)
lam f ⟦ σ ⟧ = lam (f ⟦ σ ⟧)

-- The definition of reachability 
data Reach {V : ℕ}{Γ : Cxt V}{X : VarSet}{t : Type} (e : Exp Γ X t) (τ : Inp X) : Set where
  reach : e ⟦ τ ⟧ ↦* • → Reach e τ
  

-- The definiton of de bruijn substitution follows
sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucCxt : ∀{V V' u t}{Γ' : Cxt V'}(Γ : Cxt V) → (v : Fin (V + V')) → 
         Γ ++ Γ' [ v ]= t → Γ ++ u ∷ Γ' [ sucVar V v ]= t
sucCxt [] v o = there o
sucCxt (t ∷ Γ) zero here = here
sucCxt (x ∷ Γ) (suc v) (there o) = there (sucCxt Γ v o)

sucExp : ∀{V V' t u X}{Γ' : Cxt V'} → (Γ : Cxt V) → Exp (Γ ++ Γ') X t → Exp (Γ ++ u ∷ Γ') X t
sucExp Γ Z = Z
sucExp Γ (S x) = S (sucExp Γ x)
sucExp Γ • = •
sucExp {V = V} Γ (var x o) = var (sucVar V x) (sucCxt Γ x o)
sucExp Γ (fvar x) = fvar x
sucExp Γ (case e alt₀ e₁ altₛ e₂) = 
       case (sucExp Γ e) alt₀ (sucExp Γ e₁) altₛ sucExp (Nat ∷ Γ) e₂
sucExp Γ (app f e) = app (sucExp Γ f) (sucExp Γ e)
sucExp Γ (lam {u = u} f) = lam (sucExp (u ∷ Γ) f)

rep : ∀{V V' t u X}{Γ' : Cxt V'}(Γ : Cxt V) → Exp (Γ ++ u ∷ Γ') X t → Exp Γ' X u → Exp (Γ ++ Γ') X t
rep Γ Z ef = Z
rep Γ (S x) ef = S (rep Γ x ef)
rep Γ • ef = •
rep [] (var zero here) ef = ef 
rep [] (var (suc v) (there o)) ef = var v o
rep (x ∷ Γ) (var zero here) ef = var zero here
rep (x ∷ Γ) (var (suc v) (there o)) ef = sucExp [] (rep Γ (var v o) ef )
rep Γ (fvar a) ef = fvar a
rep Γ (case e alt₀ e₁ altₛ e₂) ef = case rep Γ e ef alt₀ rep Γ e₁ ef altₛ rep (Nat ∷ Γ) e₂ ef
rep Γ (app {u = u} f e) ef = app (rep Γ f ef) (rep Γ e ef)
rep Γ (lam {u = u} f) ef = lam (rep (u ∷ Γ) f ef)

_⟪_⟫ = rep [] 
