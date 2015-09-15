
module Func.Sound where

open import Basic.Helpful
open import Basic.Subs

open import Func.Exp
open import Func.LazyNarrowing

open import Data.Vec
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Function

-- replace lift, this lifts the application through a replace
replace-lift : ∀{V V' X Y t u}{Γ' : Cxt V'}(Γ : Cxt V) → (e : Exp (Γ ++ u ∷ Γ') X t) 
             → (e' : Exp Γ' X u) → (σ : X ⇀ Y) →  rep Γ (e ⟦ σ ⟧) (e' ⟦ σ ⟧) ≡ (rep Γ e e') ⟦ σ ⟧

-- lemma 2 - the lifting leema
↦-lift : ∀{V X Y t}{Γ : Cxt V}{e e' : Exp Γ X t} → e ↦ e' → (σ : X ⇀ Y) → e ⟦ σ ⟧ ↦ e' ⟦ σ ⟧
↦-lift (caseZ e₀ eₛ) σ = caseZ (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧)
↦-lift (caseS e e₀ eₛ) σ = coerce₁ (caseS (e ⟦ σ ⟧) (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧))
  where 
    coerce₁ = subst (λ e' → ((case (S e) alt₀ e₀ altₛ eₛ) ⟦ σ ⟧) ↦ e') (replace-lift [] eₛ e σ) 
↦-lift (case• e₀ eₛ) σ = case• (e₀ ⟦ σ ⟧) (eₛ ⟦ σ ⟧)
↦-lift (prom r) σ = prom (↦-lift r σ)
↦-lift (subs f e) σ = coerce₁ (subs (f ⟦ σ ⟧) (e ⟦ σ ⟧)) 
  where
    coerce₁ = subst (λ e' → app (lam (f ⟦ σ ⟧)) (e ⟦ σ ⟧) ↦ e') (replace-lift [] f e σ)
↦-lift (app• e) σ = app• (e ⟦ σ ⟧)
↦-lift (promsub r) σ = promsub (↦-lift r σ) 
↦-lift fix• σ = fix•
↦-lift (fix f) σ = coerce₁ (fix (f ⟦ σ ⟧))
  where coerce₁ = subst (λ e' → fix (lam (f ⟦ σ ⟧)) ↦ e') (replace-lift [] f (fix (lam f)) σ)
↦-lift (promfix r) σ = promfix (↦-lift r σ)

-- Statement of soundness
⇝⁺-sound : ∀{V X Y t}{Γ : Cxt V}{τ : X ⇀ Y}{e : Exp Γ X t}{e' : Exp Γ Y t} → 
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
reachF-sound : ∀{V X t}{Γ : Cxt V}{e : Exp Γ X t}{τ : Inp X} → ReachF e τ → Reach e τ
reachF-sound (reachF x) = reach (⇝⁺-sound x)


-- Proof for replace lift
sucExp-fromV : ∀{V V' X u}{Γ' : Cxt V'}(Γ : Cxt V) → (a : Val X) →  
              sucExp {u = u} {Γ' = Γ'} Γ ⌈ a ⌉ ≡ ⌈ a ⌉
sucExp-fromV Γ (fvar x) = refl
sucExp-fromV Γ Z = refl
sucExp-fromV Γ (S a) = cong S (sucExp-fromV Γ a) 

sucExp-lift : ∀{V V' X Y t u}{Γ' : Cxt V'}(Γ : Cxt V) → (e : Exp (Γ ++ Γ') X t) → (σ : X ⇀ Y) → 
            sucExp {u = u} Γ (e ⟦ σ ⟧) ≡ sucExp Γ e ⟦ σ ⟧
sucExp-lift Γ Z σ = refl
sucExp-lift Γ (S e) σ = cong S (sucExp-lift Γ e σ)
sucExp-lift Γ • σ = refl
sucExp-lift Γ (var v o) σ = refl
sucExp-lift Γ (fvar x) σ = sucExp-fromV Γ (σ x) 
sucExp-lift Γ (case e alt₀ e₁ altₛ e₂) σ = cong₃ case_alt₀_altₛ_ (sucExp-lift Γ e σ) (sucExp-lift Γ e₁ σ) (sucExp-lift (Nat ∷ Γ) e₂ σ) 
sucExp-lift Γ (app f e) σ = cong₂ app (sucExp-lift Γ f σ) (sucExp-lift Γ e σ) 
sucExp-lift Γ (lam {u = u} f) σ = cong lam (sucExp-lift (u ∷ Γ) f σ)
sucExp-lift Γ (fix f) σ = cong fix (sucExp-lift Γ f σ) 

rep-fromV : ∀{V V' X t}{Γ' : Cxt V'}(Γ : Cxt V) → (e : Exp Γ' X t) → (a : Val X) →  
          rep Γ ⌈ a ⌉ e ≡ ⌈ a ⌉
rep-fromV V e (fvar x) = refl
rep-fromV V e Z = refl
rep-fromV V e (S a) = cong S (rep-fromV V e a)

replace-var : ∀{V V' X Y t u}{Γ' : Cxt V'}(Γ : Cxt V) → 
            (v : Fin (V + suc V')) → (o : Γ ++ u ∷ Γ' [ v ]= t)
    → (e' : Exp Γ' X u) → (σ : X ⇀ Y) →  rep Γ (var v o) (e' ⟦ σ ⟧) ≡ rep Γ (var v o) e' ⟦ σ ⟧
replace-var [] zero here e' σ = refl
replace-var [] (suc v) (there o) e' σ = refl
replace-var (t ∷ Γ) zero here e' σ = refl
replace-var (x ∷ Γ) (suc v) (there o) e' σ = trans (cong (sucExp []) eq) (sucExp-lift [] (rep Γ (var v o) e') σ)
  where eq = replace-var Γ v o e' σ

replace-lift Γ Z e' σ = refl
replace-lift Γ (S e) e' σ = cong S (replace-lift Γ e e' σ)
replace-lift Γ • e' σ = refl
replace-lift Γ (var v o) e' σ = replace-var Γ v o e' σ
replace-lift Γ (fvar x) e' σ = rep-fromV Γ (e' ⟦ σ ⟧) (σ x)
replace-lift Γ (case e alt₀ e₁ altₛ e₂) e' σ = cong₃ case_alt₀_altₛ_ (replace-lift Γ e e' σ) (replace-lift Γ e₁ e' σ) (replace-lift (Nat ∷ Γ) e₂ e' σ)
replace-lift Γ (app f e) e' σ = cong₂ app (replace-lift Γ f e' σ) (replace-lift Γ e e' σ)
replace-lift Γ (lam {u = u} f) e' σ = cong lam (replace-lift (u ∷ Γ) f e' σ)
replace-lift Γ (fix f) e' σ = cong fix (replace-lift Γ f e' σ)

