module Exp where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Helpful
open import Data.Empty
open import Function
open import Subs

data Exp (V : ℕ) (X : VarSet) : Set where
  Z : Exp V X 
  S :  Exp V X → Exp V X
  var : Fin V → Exp V X 
  fvar : (x : Var X) → Exp V X
  case_alt₀_altₛ_ : (e : Exp V X) → (e₀ : Exp V X) → (eₛ : Exp (suc V) X) → Exp V X
  
⌈_⌉ : ∀{V X} → Val X → Exp V X
⌈ fvar x ⌉ = fvar x
⌈ Z ⌉ = Z
⌈ S a ⌉ = S ⌈ a ⌉

sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucExp : ∀{V' X}(V : ℕ) → Exp (V + V') X → Exp (V + suc V') X
sucExp V Z = Z
sucExp V (S x) = S (sucExp V x)
sucExp V (var x) = var (sucVar V x) 
sucExp V (fvar x) = fvar x
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂


rep : ∀{V' X} (V : ℕ) → Exp (V + suc V') X → Exp V' X → Exp (V + V') X
rep V Z ef = Z
rep V (S x) ef = S (rep V x ef)
rep zero (var zero) ef = ef
rep zero (var (suc x)) ef = var x
rep (suc V) (var zero) ef = var zero
rep (suc V) (var (suc x)) ef with rep V (var x) ef
... | e' = sucExp 0 e'
rep V (fvar a) ef = fvar a
rep V (case e alt₀ e₁ altₛ e₂) ef = case rep V e ef alt₀ rep V e₁ ef altₛ rep (suc V) e₂ ef

_⟪_⟫ : ∀{V X} → Exp (suc V) X → Exp V X → Exp V X
_⟪_⟫ = rep 0

data _↦_ {V : ℕ}{X : VarSet} : Exp V X → Exp V X → Set where
  caseZ :  (e₀ : Exp V X) → (eₛ : Exp (suc V) X) → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : (e : Exp V X) → (e₀ : Exp V X) → (eₛ : Exp (suc V) X)   
                → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : {e e' e₀ : Exp V X}{eₛ : Exp (suc V) X} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               
data _↦*_ {V : ℕ}{X : VarSet} : Exp V X → Exp V X → Set where
  [] : ∀{e} → e ↦* e 
  _∷_ : ∀{e e' e''} → (r : e ↦ e') → (r* : e' ↦* e'') → e ↦* e''
 
 
--_⇀_ : Set → Set → Set
--_⇀_ X N = {V' : ℕ} → X → Exp V' N

_⟦_⟧ : ∀{V X Y} →  (e : Exp V X) → X ⇀ Y → Exp V Y
Z ⟦ σ ⟧ = Z
S e ⟦ σ ⟧ = S (e ⟦ σ ⟧)
var x ⟦ σ ⟧ = var x
fvar x ⟦ σ ⟧ = ⌈ σ x ⌉
(case e alt₀ e₀ altₛ eₛ) ⟦ σ ⟧ = case e ⟦ σ ⟧ alt₀ e₀ ⟦ σ ⟧ altₛ eₛ ⟦ σ ⟧ 

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

data _⊸_ {V : ℕ}{X : VarSet} : Exp V X → Var X → Set where
  susp : (x : Var X) → fvar x ⊸ x
  subj-susp : ∀{e e₀ eₛ x} → e ⊸ x → case e alt₀ e₀ altₛ eₛ ⊸ x
  
Narr : Set₁
Narr = {V : ℕ}{X Y : VarSet} → Exp V X → (X ⇀ Y) → Set
  
data NRed {V : ℕ}{X : VarSet}(P : Narr) : {Y : VarSet} → Exp V X → Exp V Y × X ⇀ Y → Set where 
  narr : ∀{e Y}(σ : X ⇀ Y) →  P {Y = Y} e σ → NRed P e (e ⟦ σ ⟧ , σ)
  red : ∀{e e'} → (r : e ↦ e') → NRed P e (e' , ⇀-id)
  


data NRed⁺ {V : ℕ}{X : VarSet}(P : Narr) : {Y : VarSet} → Exp V X → Exp V Y × X ⇀ Y → Set where 
   [] : ∀ {e Y} → (o : Empty Y) → (τ : X ⇀ Y) → NRed⁺ P e (e ⟦ τ ⟧ , τ)
   _∷_ : ∀ {e Y Z e' e'' σ τ} →
         NRed P {Y} e (e' , σ) → NRed⁺ P {Z} e' (e'' , τ) → NRed⁺ P e (e'' , σ >=> τ)
         
sucExp-fromV : ∀{V' X}(V : ℕ) → (a : Val X) →  
              sucExp {V'} V ⌈ a ⌉ ≡ ⌈ a ⌉
sucExp-fromV V (fvar x) = refl
sucExp-fromV V Z = refl
sucExp-fromV V (S a) = cong S (sucExp-fromV V a)

sucExp-func : ∀{V' X Y}(V : ℕ) → (e : Exp (V + V') X) → (σ : X ⇀ Y) → 
            sucExp V (e ⟦ σ ⟧) ≡ sucExp V e ⟦ σ ⟧
sucExp-func V Z σ = refl
sucExp-func V (S e) σ = cong S (sucExp-func V e σ)
sucExp-func V (var v) σ = refl
sucExp-func V (fvar x) σ = sucExp-fromV V (σ x) 
sucExp-func V (case e alt₀ e₁ altₛ e₂) σ = cong₃ case_alt₀_altₛ_ (sucExp-func V e σ) (sucExp-func V e₁ σ) (sucExp-func (suc V) e₂ σ) 

rep-fromV : ∀{V' X}(V : ℕ) → (e : Exp V' X) →  (a : Val X) →  
          rep V ⌈ a ⌉ e ≡ ⌈ a ⌉
rep-fromV V e (fvar x) = refl
rep-fromV V e Z = refl
rep-fromV V e (S a) = cong S (rep-fromV V e a)

rep-func : ∀{V' X Y} (V : ℕ) → (e : Exp (V + suc V') X) → (e' : Exp V' X) → (σ : X ⇀ Y) →  rep V (e ⟦ σ ⟧) (e' ⟦ σ ⟧) ≡ (rep V e e') ⟦ σ ⟧
rep-func V Z e' σ = refl
rep-func V (S e) e' σ = cong S (rep-func V e e' σ)
rep-func zero (var zero) e' σ = refl
rep-func zero (var (suc x)) e' σ = refl
rep-func (suc V) (var zero) e' σ = refl
rep-func (suc V) (var (suc v)) e' σ = let 
    eq = rep-func V (var v) e' σ 
  in trans (cong (sucExp 0) eq) (sucExp-func 0 (rep V (var v) e') σ)
rep-func V (fvar x) e' σ = rep-fromV V (e' ⟦ σ ⟧) (σ x)
rep-func V (case e alt₀ e₁ altₛ e₂) e' σ = cong₃ case_alt₀_altₛ_ (rep-func V e e' σ) (rep-func V e₁ e' σ) (rep-func (suc V) e₂ e' σ)

↦-lift : ∀{V X Y}{e e' : Exp V X} → e ↦ e' → (σ : X ⇀ Y) → e ⟦ σ ⟧ ↦ e' ⟦ σ ⟧
↦-lift (caseZ e₀ eₛ) σ = caseZ (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧)
↦-lift (caseS e e₀ eₛ) σ = coerce₁ (caseS (e ⟦ σ ⟧) (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧))
  where 
    coerce₁ = subst (λ e' → ((case (S e) alt₀ e₀ altₛ eₛ) ⟦ σ ⟧) ↦ e') (rep-func zero eₛ e σ) 
↦-lift (prom r) σ = prom (↦-lift r σ)

NRed⁺-sound : ∀{V X Y}{P : Narr}{τ : X ⇀ Y}{e : Exp V X}{e' : Exp V Y} → 
              (r : NRed⁺ P e (e' , τ )) → e ⟦ τ ⟧ ↦* e'
NRed⁺-sound ([] o τ)  = []
NRed⁺-sound {e = e}{e'} (_∷_ {τ = τ} (narr σ p) r⁺) = coerce₁ (NRed⁺-sound r⁺) 
  where coerce₁ = subst (λ a → a ↦* e') (⟦⟧-func e σ τ)
NRed⁺-sound (_∷_ {τ = τ} (red r) r⁺) = ↦-lift r τ ∷ NRed⁺-sound r⁺

Susp : ∀{V X} → Exp V X → Set
Susp e = ∃ (λ x → e ⊸ x)

↦-unlift : ∀{V X Y}{e : Exp V X}{e' : Exp V Y} → (σ : X ⇀ Y) → e ⟦ σ ⟧ ↦ e' → ¬ (Susp e) →  Σ (Exp V X) (λ e'' → e ↦ e'' × e'' ⟦ σ ⟧ ≡ e')
↦-unlift {e = Z} b () ¬s
↦-unlift {e = S e} b () ¬s
↦-unlift {e = var x} b () ¬s
↦-unlift {e = fvar x} b r ¬s = ⊥-elim (¬s (x , susp x))
↦-unlift {e = case Z alt₀ e₁ altₛ e₂} b (caseZ ._ ._) ¬s = e₁ , caseZ e₁ e₂ , refl
↦-unlift {e = case Z alt₀ e₁ altₛ e₂} b (prom ()) ¬s
↦-unlift {m}{V} {e = case S e alt₀ e₁ altₛ e₂} b (caseS ._ ._ ._) ¬s = 
  e₂ ⟪ e ⟫ , caseS e e₁ e₂ , sym (rep-func zero e₂ e b)
↦-unlift {e = case S e alt₀ e₁ altₛ e₂} b (prom ()) ¬s
↦-unlift {e = case var x alt₀ e₁ altₛ e₂} b (prom ()) ¬s
↦-unlift {e = case fvar x alt₀ e₁ altₛ e₂} b r ¬s = ⊥-elim (¬s (x , subj-susp (susp x)))
↦-unlift {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} b (prom r) ¬s 
  with ↦-unlift {e = case e alt₀ e₁ altₛ e₂} b r (λ {(x , sus) → ¬s (x , (subj-susp sus))})
↦-unlift {V} {X} {Y} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} b (prom r) ¬s 
  | e'' , r' , eq = case e'' alt₀ e₃ altₛ e₄  , prom r' , cong₃ case_alt₀_altₛ_ eq refl refl

Susp? : ∀{V X} → (e : Exp V X) → Dec (Susp e)
Susp? Z = no (λ {( x , () )} )
Susp? (S e) = no (λ {( x , () )} )
Susp? (var x) = no (λ {( x , () )} )
Susp? (fvar x) = yes (x , susp x)
Susp? (case e alt₀ e₁ altₛ e₂) with Susp? e
Susp? (case e alt₀ e₁ altₛ e₂) | yes (x , s) = yes (x , subj-susp s)
Susp? (case e alt₀ e₁ altₛ e₂) | no ¬p = no (λ {(x , subj-susp s) → ¬p (x , s)})
 
