module Complete where



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
  
_[|_//_] : ∀ {X Y Z} → (τ : X ⇀ Z) → (x : Var X) →  Y ⇀ Z → X [ x // Y ] ⇀ Z 
_[|_//_] τ here σ v = σ v
_[|_//_] τ (inL x) σ (inL x') = ((λ a → τ (inL a)) [| x // σ ]) x' 
_[|_//_] τ (inL x) σ (inR x') = τ (inR x')
_[|_//_] τ (inR x) σ (inL x') = τ (inL x')
_[|_//_] τ (inR x) σ (inR x') = ((τ ∘ inR) [| x // σ ]) x'

point-eq : ∀{ X Y Z} → (a : Val Y) → (b : Val Z) → (τ : X ⇀ Z) → (x : Var X) → τ x ≡ b → (o : a ⊑ₚ b) → (x' : Var X) → τ x' ≡ ((x / a) >=> (τ [| x // proj₁ o ])) x'
point-eq a .(τ here) τ here refl (σ , eq') here = eq'
point-eq a b τ (inL x) eq o (inL x') = let 
  r = point-eq a b (λ a → (τ (inL a))) x eq o x' 
  eq2 =  sym (>>=-assoc ((x / a) x') (λ z → fvar (inL z)) (τ [| inL x // proj₁ o ])) 
    in trans r eq2 
point-eq a b τ (inL x) eq o (inR x') = refl
point-eq a b τ (inR x) eq o (inL x') = refl
point-eq a b τ (inR x) eq o (inR x') = let 
  r = point-eq a b (λ a → (τ (inR a))) x eq o x' 
  eq2 =  sym (>>=-assoc ((x / a) x') (λ z → fvar (inR z)) (τ [| inR x // proj₁ o ])) 
    in trans r eq2 

complete-narr : ∀ {X} → (τ : Inp X) → (x : Var X) → ∃₂ (λ Y σ → LNarr x {Y} σ × σ ⊑ τ)
complete-narr τ x with τ x | inspect τ x
complete-narr τ x | fvar () | eq
complete-narr {X} τ x | Z | [ eq ] = let ab = ((λ { () }) , refl)
  in X [ x // ∅ ] , x / Z , narr bindZ , τ [| x // proj₁ ab ] , ext (point-eq Z Z τ x eq ab)
complete-narr {X} τ x | S c | [ eq ] = let ab = (λ {here → c}) , refl 
  in X [ x // V1 ] , x / (S (fvar here)) , narr bindS , τ [| x // proj₁ ab ] , ext (point-eq (S (fvar here)) (S c) τ x eq ab)
 

Susp? : ∀{V X} → (e : Exp V X) → Dec (Susp e)
Susp? Z = no (λ {( x , () )} )
Susp? (S e) = no (λ {( x , () )} )
Susp? (var x) = no (λ {( x , () )} )
Susp? (fvar x) = yes (x , susp x)
Susp? (case e alt₀ e₁ altₛ e₂) with Susp? e
Susp? (case e alt₀ e₁ altₛ e₂) | yes (x , s) = yes (x , subj-susp s)
Susp? (case e alt₀ e₁ altₛ e₂) | no ¬p = no (λ {(x , subj-susp s) → ¬p (x , s)})
 

