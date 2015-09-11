module Basic.Complete where

open import Basic.Helpful
open import Basic.Subs
open import Basic.Exp
open import Basic.LazyNarrowing
open import Basic.Sound
open import Basic.WellFound

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Function
open import Relation.Unary using (_⇒_)

Susp : ∀{V X} → Exp V X → Set
Susp e = ∃ (λ x → e ⊸ x)

-- the unlift lemma
↦-unlift : ∀{V X Y}{e : Exp V X}{e' : Exp V Y} → (σ : X ⇀ Y) → e ⟦ σ ⟧ ↦ e' → ¬ (Susp e) →  Σ (Exp V X) (λ e'' → e ↦ e'' × e'' ⟦ σ ⟧ ≡ e')
↦-unlift {e = Z} b () ¬s
↦-unlift {e = •} b () ¬s
↦-unlift {e = S e} b () ¬s
↦-unlift {e = var x} b () ¬s
↦-unlift {e = fvar x} b r ¬s = ⊥-elim (¬s (x , susp x))

↦-unlift {e = case Z alt₀ e₁ altₛ e₂} b (caseZ ._ ._) ¬s = e₁ , caseZ e₁ e₂ , refl
↦-unlift {e = case Z alt₀ e₁ altₛ e₂} b (prom ()) ¬s

↦-unlift {e = case • alt₀ e₁ altₛ e₂} b (case• ._ ._) ¬s = • , case• e₁ e₂ , refl
↦-unlift {e = case • alt₀ e₁ altₛ e₂} b (prom ()) ¬s

↦-unlift {m}{V} {e = case S e alt₀ e₁ altₛ e₂} b (caseS ._ ._ ._) ¬s = 
  e₂ ⟪ e ⟫ , caseS e e₁ e₂ , sym (replace-lift zero e₂ e b)
↦-unlift {e = case S e alt₀ e₁ altₛ e₂} b (prom ()) ¬s
↦-unlift {e = case var x alt₀ e₁ altₛ e₂} b (prom ()) ¬s
↦-unlift {e = case fvar x alt₀ e₁ altₛ e₂} b r ¬s = ⊥-elim (¬s (x , subj-susp (susp x)))

↦-unlift {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} b (prom r) ¬s 
  with ↦-unlift {e = case e alt₀ e₁ altₛ e₂} b r (λ {(x , sus) → ¬s (x , (subj-susp sus))})
↦-unlift {V} {X} {Y} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} b (prom r) ¬s 
  | e'' , r' , eq = case e'' alt₀ e₃ altₛ e₄  , prom r' , cong₃ case_alt₀_altₛ_ eq refl refl
  
-- calculation of suspension
Susp? : ∀{V X} → (e : Exp V X) → Dec (Susp e)
Susp? Z = no (λ {( x , () )} )
Susp? (S e) = no (λ {( x , () )} )
Susp? • = no (λ {(x , () )} )
Susp? (var x) = no (λ {( x , () )} )
Susp? (fvar x) = yes (x , susp x)
Susp? (case e alt₀ e₁ altₛ e₂) with Susp? e
Susp? (case e alt₀ e₁ altₛ e₂) | yes (x , s) = yes (x , subj-susp s)
Susp? (case e alt₀ e₁ altₛ e₂) | no ¬p = no (λ {(x , subj-susp s) → ¬p (x , s)})
  
-- The "eliminator" for a variable set with one replacement
_[|_//_] : ∀ {X Y Z} → (τ : X ⇀ Z) → (x : Var X) →  Y ⇀ Z → X [ x // Y ] ⇀ Z 
_[|_//_] τ here σ x' = σ x'
_[|_//_] τ (inL x) σ (inL x') = ((τ ∘ inL) [| x // σ ]) x'
_[|_//_] τ (inL x) σ (inR x') = τ (inR x')
_[|_//_] τ (inR x) σ (inL x') = τ (inL x')
_[|_//_] τ (inR x) σ (inR x') = ((τ ∘ inR) [| x // σ ]) x'

-- The construction to split a substitution over a value
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

-- LEMMA the narrowing set is complete
complete-narr : ∀ {X} → (τ : Inp X) → (x : Var X) → ∃₂ (λ Y σ → Narr x {Y} σ × σ ⊑ τ)
complete-narr τ x with τ x | inspect τ x
complete-narr τ x | fvar () | eq
complete-narr {X} τ x | Z | [ eq ] = let ab = ((λ { () }) , refl)
  in X [ x // ∅ ] , x / Z , narr bindZ , τ [| x // proj₁ ab ] , ext (point-eq Z Z τ x eq ab)
complete-narr {X} τ x | S c | [ eq ] = let ab = (λ {here → c}) , refl 
  in X [ x // V1 ] , x / (S (fvar here)) , narr bindS , τ [| x // proj₁ ab ] , ext (point-eq (S (fvar here)) (S c) τ x eq ab)
  
-- simple embedding of variable
embed : {X Y : VarSet} →  (x : Var X) → (y : Var Y) → Var (X [ x // Y ])
embed here y = y
embed (inL x) y = inL (embed x y)
embed (inR x) y = inR (embed x y)

-- looking at a value is a one point update is the same
point-look : {X Y : VarSet} → (x : Var X) → (a : Val Y) → (x / a) x ≡ a >>= (fvar ∘ embed x)
point-look here a = sym (>>=-right a)
point-look (inL x) a = let 
  eq = cong (λ a' → a' >>= (λ x → fvar (inL x))) (point-look x a)
    in trans eq (>>=-assoc a (fvar ∘ embed x) (λ x → fvar (inL x)))
point-look (inR x) a = let 
  eq = cong (λ a' → a' >>= (λ x → fvar (inR x))) (point-look x a)
    in trans eq (>>=-assoc a (fvar ∘ embed x) (λ x → fvar (inR x)))

-- A point update is advancing if the value is not a free variable
point-adv : ∀{X Y} → (x : Var X)  → (a : Val Y) → ((y : Var Y) → a ≠ fvar y)  →  ¬ ((x / a) ⊑ return)
point-adv x (fvar y) ne (σ , eq) = ⊥-elim (ne y refl)  
point-adv x Z ne (σ , eq) with subst (λ p → return x ≡ p >>= σ) (point-look x Z) (cong (λ f → f x) eq)
point-adv x Z ne (σ , eq) | ()
point-adv x (S a) ne (σ , eq) with subst (λ p → return x ≡ p >>= σ) (point-look x (S a)) (cong (λ f → f x) eq)
point-adv x (S a) ne (σ , eq) | ()

-- LEMMA every substitution in the narrowing set is advancing
adv-narr : {X Y : VarSet} → (x : Var X) → (σ : X ⇀ Y) → Narr x σ → return ⊏ σ
adv-narr x .(x / Z) (narr bindZ) = (x / Z , refl) , point-adv x Z (λ y → λ ())
adv-narr x .(x / S (fvar here)) (narr bindS) = (x / S (fvar here) , refl) , point-adv x (S (fvar here)) (λ y → λ ())


-- THE current version does not use the general version of well foundness in the paper, instead we use a specific wellfoundness for a one point update.
adv-specific : ∀{X Y Z}{σ : X ⇀ Y}{τ : Y ⇀ Z} → (x : Var X) → Narr x σ → count τ < count (σ >=> τ) 
adv-specific {τ = τ} x (narr bindZ) = <-count x ((λ ()) , (λ y → λ ())) τ
adv-specific {τ = τ} x (narr bindS) = <-count x ((λ {here → isS here}) , (λ y → λ ())) τ

-- Completeness - (Acc _<_ (count τ)) is the wellfounded condition
⇝⁺-complete' : ∀{V X}{e : Exp V X}{e' : Exp V ∅} → (τ : X ⇀ ∅) → Acc _<_ (count τ) →
              e ⟦ τ ⟧ ↦* e' → e ⇝⁺ (e' , τ )
⇝⁺-complete' τ wf [] = [] τ
⇝⁺-complete' {e = e}{e' = e''} τ wf (_∷_ {e' = e'} r r*) with Susp? e
⇝⁺-complete' τ wf (r ∷ r*)  | yes (x , sus) with complete-narr τ x 
⇝⁺-complete' {e = e}{e' = e''} ._ (acc wf) (r ∷ r*) | yes (x , sus) | X₁ , σ , nar , τ' , refl = 
    narr sus σ nar ∷ ⇝⁺-complete' τ' (wf (adv-specific x nar)) (coerce₁ (r ∷ r*))
   where coerce₁ = subst (λ x₁ → x₁ ↦* e'') (sym (⟦⟧-func e σ τ'))
⇝⁺-complete' {e = e}{e' = e''} τ wf (_∷_ {e' = e'} r r*) | no ¬p with ↦-unlift τ r ¬p 
⇝⁺-complete' τ wf (r ∷ r*) | no ¬p | et , r' , refl = red r' ∷ ⇝⁺-complete' τ wf r* 

⇝⁺-complete : ∀{V X}{e : Exp V X}{e' : Exp V ∅} → (τ : X ⇀ ∅) →
              e ⟦ τ ⟧ ↦* e' → e ⇝⁺ (e' , τ )
⇝⁺-complete τ r = ⇝⁺-complete' τ (acc-< (count τ)) r

-- ReachF is complete
reachF-complete : ∀{V X}{e : Exp V X}{τ : Inp X} → Reach e τ → ReachF e τ
reachF-complete {τ = τ} (reach r) = reachF (⇝⁺-complete τ r)

-- "Equivalence"
_⇔_ : (P : Set) → (Q : Set) → Set
P ⇔ Q = (P → Q) × (Q → P)

-- Together
reachF-correct : ∀{V X}{e : Exp V X}{τ : Inp X} → Reach e τ ⇔ ReachF e τ
reachF-correct = reachF-complete , reachF-sound


