
module Sound where

open import Helpful
open import Subs
open import Exp
open import LazyNarrowing

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Function

-- replace lift, this lifts the application through a replace
replace-lift : ∀{V' X Y} (V : ℕ) → (e : Exp (V + suc V') X) → (e' : Exp V' X) → (σ : X ⇀ Y) →  rep V (e ⟦ σ ⟧) (e' ⟦ σ ⟧) ≡ (rep V e e') ⟦ σ ⟧

-- lemma 2 - the lifting leema
↦-lift : ∀{V X Y}{e e' : Exp V X} → e ↦ e' → (σ : X ⇀ Y) → e ⟦ σ ⟧ ↦ e' ⟦ σ ⟧
↦-lift (caseZ e₀ eₛ) σ = caseZ (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧)
↦-lift (caseS e e₀ eₛ) σ = coerce₁ (caseS (e ⟦ σ ⟧) (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧))
  where 
    coerce₁ = subst (λ e' → ((case (S e) alt₀ e₀ altₛ eₛ) ⟦ σ ⟧) ↦ e') (replace-lift zero eₛ e σ) 
↦-lift (case• e₀ eₛ) σ = case• (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧)
↦-lift (prom r) σ = prom (↦-lift r σ)

-- Statement of soundness
⇝⁺-sound : ∀{V X Y}{τ : X ⇀ Y}{e : Exp V X}{e' : Exp V Y} → 
              (r : e ⇝⁺ (e' , τ )) → e ⟦ τ ⟧ ↦* e'

-- Proof of soundness
-- case 1)
⇝⁺-sound ([] τ)  = []

-- case 2)
⇝⁺-sound {e = e}{e'} (_∷_ {τ = τ} (narr s σ n) r⁺) = coerce₁ (⇝⁺-sound r⁺) 
  where coerce₁ = subst (λ a → a ↦* e') (⟦⟧-func e σ τ)

-- case 3)
⇝⁺-sound (_∷_ {τ = τ} (red r) r⁺) = ↦-lift r τ ∷ ⇝⁺-sound r⁺


-- ReachF is sound
reachF-sound : ∀{V X}{e : Exp V X}{τ : Inp X} → ReachF e τ → Reach e τ
reachF-sound (reachF x) = reach (⇝⁺-sound x)





-- Proof for replace lift
sucExp-fromV : ∀{V' X}(V : ℕ) → (a : Val X) →  
              sucExp {V'} V ⌈ a ⌉ ≡ ⌈ a ⌉
sucExp-fromV V (fvar x) = refl
sucExp-fromV V Z = refl
sucExp-fromV V (S a) = cong S (sucExp-fromV V a)

sucExp-lift : ∀{V' X Y}(V : ℕ) → (e : Exp (V + V') X) → (σ : X ⇀ Y) → 
            sucExp V (e ⟦ σ ⟧) ≡ sucExp V e ⟦ σ ⟧
sucExp-lift V Z σ = refl
sucExp-lift V (S e) σ = cong S (sucExp-lift V e σ)
sucExp-lift V • σ = refl
sucExp-lift V (var v) σ = refl
sucExp-lift V (fvar x) σ = sucExp-fromV V (σ x) 
sucExp-lift V (case e alt₀ e₁ altₛ e₂) σ = cong₃ case_alt₀_altₛ_ (sucExp-lift V e σ) (sucExp-lift V e₁ σ) (sucExp-lift (suc V) e₂ σ) 

rep-fromV : ∀{V' X}(V : ℕ) → (e : Exp V' X) →  (a : Val X) →  
          rep V ⌈ a ⌉ e ≡ ⌈ a ⌉
rep-fromV V e (fvar x) = refl
rep-fromV V e Z = refl
rep-fromV V e (S a) = cong S (rep-fromV V e a)

replace-lift V Z e' σ = refl
replace-lift V (S e) e' σ = cong S (replace-lift V e e' σ)
replace-lift V • e' σ = refl
replace-lift zero (var zero) e' σ = refl
replace-lift zero (var (suc x)) e' σ = refl
replace-lift (suc V) (var zero) e' σ = refl
replace-lift (suc V) (var (suc v)) e' σ = let 
    eq = replace-lift V (var v) e' σ 
  in trans (cong (sucExp 0) eq) (sucExp-lift 0 (rep V (var v) e') σ)
replace-lift V (fvar x) e' σ = rep-fromV V (e' ⟦ σ ⟧) (σ x)
replace-lift V (case e alt₀ e₁ altₛ e₂) e' σ = cong₃ case_alt₀_altₛ_ (replace-lift V e e' σ) (replace-lift V e₁ e' σ) (replace-lift (suc V) e₂ e' σ)


