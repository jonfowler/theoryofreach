module WellFound where

open import Subs
open import Helpful
open import LazyNarrowing 

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Empty
open import Function
open import Relation.Nullary 
open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Fin hiding (_+_; _≤_; _<_)

-- WellFoundness for one point updates with no free variables values. This is not as general as the well foundness given in the paper but is sufficient for our purposes. Will be updated to the general result at some point.

--holesV : ValG Unit → VarSet
--holesV Z = ∅
--holesV (S a) = holesV a
--holesV (fvar x) = V1
--
--SubStr : VarSet → Set
--SubStr X = (Var X → ValG Unit)
--
--holes : ∀{X} → SubStr X → VarSet
--holes {∅} f = ∅
--holes {V1} f = holesV (f here)
--holes {X1 ∪ X2} f = holes (f ∘ inL) ∪ holes (f ∘ inR) 
--
--holes-id : ∀{X} → (f : SubStr X) → ((x : Var X) → f x ≡ fvar unit) → holes f ≡ X
--holes-id {∅} f eq = refl
--holes-id {V1} f eq = cong holesV (eq here)
--holes-id {X ∪ X₁} f eq = cong₂ _∪_ 
--         (holes-id (f ∘ inL) (eq ∘ inL )) 
--         (holes-id (f ∘ inR) (eq ∘ inR))
--         
--_>>=ₕ_ : {C : Set} → (s : ValG Unit) → (Var (holesV s) → ValG C) → ValG C
--_>>=ₕ_ Z f = Z
--_>>=ₕ_ (S s) f = S (s >>=ₕ f)
--_>>=ₕ_ (fvar x) f = f here 
--
--_>=>ₕ_ : {X : VarSet}{C : Set} → (s : SubStr X) → (Var (holes s) → ValG C) → (Var X → ValG C)
--_>=>ₕ_ s f here = (s here) >>=ₕ f
--_>=>ₕ_ s f (inL x) = _>=>ₕ_ (s ∘ inL)  (f ∘ inL) x 
--_>=>ₕ_ s f (inR x) = _>=>ₕ_ (s ∘ inR)  (f ∘ inR) x
--
--_⇀W_ : VarSet → VarSet → Set 
--X ⇀W Y = Σ (SubStr X) (λ s → Var (holes s) → Var Y)
--
--embedV : ∀{Y} →  Val Y → Σ (ValG Unit) (λ x → Var (holesV x) → Var Y)
--embedV Z = Z , λ ()
--embedV (S s) with embedV s
--embedV (S s) | s' , m = S s' , m
--embedV (fvar x) = (fvar unit) , (λ {here → x})
--
--embed : ∀{X Y} → X ⇀ Y → X ⇀W Y
--embed {∅} f = (λ ()) , λ ()
--embed {V1} f with embedV (f here) 
--embed {V1} f | s , m = (λ {here → s}) , m
--embed {X1 ∪ X2} f with embed (f ∘ inL) | embed (f ∘ inR)
--embed {X1 ∪ X2} f | s1 , m1 | s2 , m2 = 
--  (λ {(inL x) → s1 x ; (inR x) → s2 x}) , 
--  (λ {(inL x) → m1 x ; (inR x) → m2 x}) 
--  
--idW : ∀ X → X ⇀W X
--idW X = (λ x → fvar unit) , coerce₁ id 
--  where coerce₁ = subst (λ x → Var x → Var X) (sym (holes-id (λ _ → fvar unit) (λ x → refl))) 
--  
--
--newmV : ∀{Y Z} → (a : ValG Unit) → (m : Var (holesV a) → Var Y)
--                  (s' : SubStr Y) → (m' : Var (holes s') → Var Z) →
--                  Var (holesV (a >>=ₕ (s' ∘ m))) → Var Z 
--newmV Z m s' m' ()
--newmV (S a) m s' m' x = newmV a m s' m' x
--newmV (fvar unit) m s' m' x' = {!!}
--
--newm : ∀{X Y Z} → (s : SubStr X) → (m : Var (holes s) → Var Y)
--                  (s' : SubStr Y) → (m' : Var (holes s') → Var Z) →
--                  Var (holes (s >=>ₕ (s' ∘ m))) → Var Z 
--newm {∅} s m s' m' ()
--newm {V1} s m s' m' x = {!!}
--newm {X ∪ X₁} s m s' m' (inL x) = (newm (s ∘ inL) (m ∘ inL) s' m') x
--newm {X ∪ X₁} s m s' m' (inR x) = (newm (s ∘ inR) (m ∘ inR) s' m') x
--
--_>=>W_ : ∀{X Y Z} → X ⇀W Y → Y ⇀W Z → X ⇀W Z
--(s , m) >=>W (s' , m') = s >=>ₕ (s' ∘ m) , {!m'!}

countₚ : {X : VarSet} → Val X → ℕ
countₚ (fvar x) = 0 
countₚ Z = 1
countₚ (S a) = 1 + countₚ a

countOver : {X : VarSet} → (Var X → ℕ) → ℕ
countOver {∅} f = 0
countOver {V1} f = f here 
countOver {X1 ∪ X2} f = countOver (f ∘ inL) + countOver (f ∘ inR)

count : ∀{X Y} → X ⇀ Y → ℕ
count σ = countOver (λ x → countₚ (σ x))

data _∈ₚ_ {X : VarSet} (x : Var X) : (Val X) → Set where
  here : x ∈ₚ (fvar x) 
  inS : ∀{a} → x ∈ₚ a → x ∈ₚ (S a)
  
Pos : {X : VarSet} → Val X → Set
Pos a = ∃ (λ y → y ∈ₚ a)

SPos : ∀{X}{a : Val X} → Pos a → Pos (S a)
SPos (x , p) = x , inS p

_∈_ : {X Y : VarSet} → (y : Var Y) → X ⇀ Y → Set
y ∈ σ = ∃ (λ x → y ∈ₚ σ x)

PosSet : ∀{X Y} →  X ⇀ Y → Set₁
PosSet σ = ∀ x → Pos (σ x) → Set

Onto : ∀{X Y} → X ⇀ Y → Set
Onto σ = ∀ y → y ∈ σ

OntoSet : ∀{X Y}{σ : X ⇀ Y} → Onto σ → PosSet σ
OntoSet o x (y' , p) = o y' ≡ (x , p)

outS : ∀{Y}{a : Val Y}{y : Var Y}{p p' : y ∈ₚ a} → inS p ≡ inS p' → p ≡ p'
outS refl = refl

outR : ∀{X Y}{x x' : Var X} → inR {Y} x ≡ inR x' → x ≡ x'
outR refl = refl

outL : ∀{X Y}{x x' : Var X} → inL {X}{Y} x ≡ inL x' → x ≡ x'
outL refl = refl

out2 : {A : Set}{P : A → Set}{a : A}{p p' : P a} → (_,_ {B = P} a p) ≡ (a , p') → p ≡ p'
out2 refl = refl

decP : ∀{Y}{a : Val Y}{y : Var Y} → (p p' : y ∈ₚ a) → Dec (p ≡ p')
decP here here = yes refl
decP (inS p) (inS p') with decP p p'
decP (inS p) (inS p') | yes eq = yes (cong inS eq)
decP (inS p) (inS p') | no ¬p = no (λ x → ¬p (outS x))

decX : ∀{X} → (x x' : Var X) → Dec (x ≡ x')
decX here here = yes refl
decX (inL x) (inL x') with decX x x'
decX (inL x) (inL x') | yes p = yes (cong inL p)
decX (inL x) (inL x') | no ¬p = no (¬p ∘ outL)
decX (inL x) (inR x') = no (λ ())
decX (inR x) (inL x') = no (λ ())
decX (inR x) (inR x') with decX x x'
decX (inR x) (inR x') | yes p = yes (cong inR p)
decX (inR x) (inR x') | no ¬p = no (¬p ∘ outR)

--outStup : ∀{Y}{σ : V1 ⇀ Y}{y : Var Y}{p p' : y ∈ₚ σ here} → (here , p) ≡ (here , p') → p ≡ p'
--outStup = {!!}

decXP : ∀{X Y}{σ : X ⇀ Y}{y : Var Y} → (xp xp' : y ∈ σ) → Dec (xp ≡ xp') 
decXP (x , p) (x' , p') with decX x x'
decXP (x , p) (.x , p') | yes refl with decP p p'
decXP (x , p) (.x , p') | yes refl | yes eq = yes (cong (λ q → (x , q)) eq)
decXP (x , p) (.x , p') | yes refl | no ¬p = no (¬p ∘ out2)
decXP (x , p) (x' , p') | no ¬p = no (¬p ∘ (cong proj₁)) 

decOnto : ∀{X Y}{σ : X ⇀ Y} → (o : Onto σ) → (x : Var X) → (p : Pos (σ x)) → Dec (OntoSet o x p)
decOnto o x (y , p) = decXP (o y) (x , p)

forget : {A : Set} → Dec A → Bool
forget (yes p) = true
forget (no ¬p) = false

countNPₚ : ∀{Y Z} → (a : Val Y) → (τ : Y ⇀ Z) → 
        ((p : Pos a) → Bool) → ℕ
countNPₚ Z τ P = 1
countNPₚ (S a) τ P = 1 + countNPₚ a τ (P ∘ SPos)
countNPₚ (fvar x) τ P with P (x , here) 
countNPₚ (fvar x) τ P₁ | true = 0
countNPₚ (fvar x) τ P₁ | false = countₚ (τ x)

countPₚ : ∀{Y Z} → (a : Val Y) → (τ : Y ⇀ Z) → 
        ((p : Pos a) → Bool) → ℕ
countPₚ Z τ P = 0 
countPₚ (S a) τ P = countPₚ a τ (P ∘ SPos)
countPₚ (fvar x) τ P with P (x , here) 
countPₚ (fvar x) τ P₁ | true = countₚ (τ x)
countPₚ (fvar x) τ P₁ | false = 0

add0 : ∀{x} → x ≡ x + 0
add0 {zero} = refl
add0 {suc x} = cong suc add0 

addsuc : ∀{x y} → suc (x + y)  ≡ x + suc y 
addsuc {zero} = refl
addsuc {suc x} = cong suc (addsuc {x})

add-assoc : {x y z : ℕ} → x + y + z ≡ x + (y + z)
add-assoc {zero} = refl
add-assoc {suc x} = cong suc (add-assoc {x})

add-comm : {x y : ℕ} → x + y ≡ y + x
add-comm {zero} = add0
add-comm {suc x}{y} = trans (cong suc (add-comm {x})) (addsuc {y})

countEq : ∀{Y Z} → (a : Val Y) → (τ : Y ⇀ Z) → 
        (P : (p : Pos a) → Bool) → countₚ (a >>= τ) ≡ countNPₚ a τ P + countPₚ a τ P
countEq Z τ P = refl
countEq (S a) τ P = cong suc (countEq a τ (P ∘ SPos))
countEq (fvar x) τ P with P (x , here)
countEq (fvar x) τ P | true = refl
countEq (fvar x) τ P | false = add0

countOverAdd : ∀{X}(f g : Var X → ℕ) → countOver f + countOver g ≡ countOver (λ x → f x + g x)
countOverAdd {∅} f g = refl
countOverAdd {V1} f g = refl
countOverAdd {X ∪ Y} f g = begin 
   c1 + c2 + (c3 + c4) ≡⟨ trans (add-assoc {c1}) (cong (_+_ c1) (sym (add-assoc {c2})) ) ⟩ 
   c1 + ((c2 + c3) + c4) ≡⟨ cong (λ x → c1 + (x + c4)) (add-comm {c2}) ⟩  
   c1 + ((c3 + c2) + c4) ≡⟨ trans ( cong (_+_ c1) (add-assoc {c3})) (sym (add-assoc {c1})) ⟩
   (c1 + c3) + (c2 + c4) 
          ≡⟨ cong₂ _+_ (countOverAdd (f ∘ inL) (g ∘ inL)) (countOverAdd (f ∘ inR) (g ∘ inR)) ⟩ 
   countOver (λ z → f (inL z) + g (inL z)) + countOver (λ z → f (inR z) + g (inR z)) ∎ 
     where c1 = countOver (f ∘ inL)
           c2 = countOver (f ∘ inR)
           c3 = countOver (g ∘ inL)
           c4 = countOver (g ∘ inR)
           
countNP : ∀{X Y Z} → (σ : X ⇀ Y) → {P : PosSet σ} → (τ : Y ⇀ Z) → 
        (∀ x → (p : Pos (σ x)) → Bool) → ℕ
countNP σ τ P = countOver (λ x → countNPₚ (σ x) τ (P x)) 

countP : ∀{X Y Z} → (σ : X ⇀ Y) → (τ : Y ⇀ Z) → 
        (∀ x → (p : Pos (σ x)) → Bool) → ℕ
countP σ τ P = countOver (λ x → countPₚ (σ x) τ (P x)) 

data Subset : VarSet → Set where
  all : ∀ {X} → Subset X
  toL : ∀{X Y} → Subset X → Subset (X ∪ Y)
  toR : ∀{X Y} → Subset Y → Subset (X ∪ Y)
  
shield : ∀{X Y}{σ : X ⇀ Y} → Subset X → ((x : Var X) → (p : Pos (σ x)) → Bool) → (x : Var X) → (p : Pos (σ x)) → Bool
shield all f x p = f x p
shield (toL s) f (inL x) p = shield s (f ∘ inL) x p
shield (toL s) f (inR x) p = false
shield (toR s) f (inL x) p = false
shield (toR s) f (inR x) p = shield s (f ∘ inR) x p

countShield : ∀{X Y} → Subset X → (σ : X ⇀ Y) → ℕ
countShield all σ = count σ
countShield (toL s) σ = countShield s (σ ∘ inL)
countShield (toR s) σ = countShield s (σ ∘ inR)

lemma4 : ∀{X Y Z}(σ : X ⇀ Y)(τ : Y ⇀ Z) → (o : Onto σ) 
         → countP σ τ (λ x p → forget (decOnto o x p)) ≡ countShield s τ
lemma4 = {!!}

lemma5 : ∀{X Y Z}(σ : X ⇀ Y)(τ : Y ⇀ Z) → (o : Onto σ) → countP σ τ (λ x p → forget (decOnto o x p)) ≡ count τ
lemma5 {Y = ∅} σ τ o = {!!}  
lemma5 {Y = V1} σ τ o = {!!}
lemma5 {Y = Y1 ∪ Y2} σ τ o = {!!}


--countNP {∅} σ τ P = 0
--countNP {V1} σ τ P with P {!σ here!} {!!} 
--...| c = {!!}
--countNP {X1 ∪ X2} σ τ P = countNP (σ ∘ inL) τ (P ∘ inL) + countNP (σ ∘ inR) τ (P ∘ inR)

--data WFSub {X : VarSet} : {Y : VarSet} → X ⇀ Y → Set where
--   [] : WFSub return 
--   _∷_ : ∀{Y Z} → (x : Var X) → (a : Val Y) → {σ : X [ x // Y ] ⇀ Z} → 
--                               WFSub σ → WFSub ((x / a) >=> σ)
--
--Var1 : VarSet → Set
--Var1 Y = Σ (Var Y) (λ y → (x : Var Y) → x ≡ y)  
--
--Var2 : VarSet → Set
--Var2 Y = Σ (Var Y) (λ y → Σ (Var Y) (λ y' → y ≠ y'))
--
--outL : ∀{Y X}{y y' : Var Y} → inL {Y = X} y ≡ inL y' → y ≡ y'
--outL refl = refl
--
--outR : ∀{Y X}{y y' : Var Y} → inR {X = X} y ≡ inR y' → y ≡ y'
--outR refl = refl
--
--Varn? : (Y : VarSet) → (Empty Y ⊎ Var1 Y) ⊎ Var2 Y
--Varn? ∅ = inj₁ (inj₁ (λ ()))
--Varn? V1 = inj₁ (inj₂ (here , (λ {here → refl})))
--Varn? (Y ∪ Y₁) with (Varn? Y) | (Varn? Y₁) 
--Varn? (Y ∪ Y₁) | inj₁ (inj₁ x) | inj₁ (inj₁ x₁) = inj₁ (inj₁ (λ {(inL y) → x y; (inR y) → x₁ y}))
--Varn? (Y ∪ Y₁) | inj₁ (inj₁ x) | inj₁ (inj₂ (y , eq)) = 
--      inj₁ (inj₂ (inR y , (λ {(inL y') → ⊥-elim (x y'); (inR y') → cong inR (eq y')})))
--Varn? (Y ∪ Y₁) | inj₁ (inj₂ (y , eq)) | inj₁ (inj₁ x) = 
--  inj₁ (inj₂ (inL y , (λ {(inL y') → cong inL (eq y') ; (inR y') → ⊥-elim (x y')})))
--Varn? (Y ∪ Y₁) | inj₁ (inj₂ (y , _)) | inj₁ (inj₂ (y' , _)) = inj₂ (inL y , inR y' , (λ {()}))
--Varn? (Y ∪ Y₁) | inj₁ c | inj₂ (y , y' , ne) = inj₂ ((inR y) , ((inR y') , (λ x → ne (outR x))))
--Varn? (Y ∪ Y₁) | inj₂ (y , y' , ne) | d = inj₂ ((inL y) , ((inL y') , (λ x → ne (outL x))))
--
--
--Var? : (V : VarSet) → Dec (Var V)
--Var? ∅ = no (λ ())
--Var? V1 = yes here -- (λ ¬e → ¬e here) 
--Var? (X ∪ Y) with Var? X | Var? Y 
--Var? (X ∪ Y) | yes p1 | b = yes (inL p1) -- yes (λ {(inL x) → p1 x ; (inR y) → p2 y})
--Var? (X ∪ Y) | no ¬p | yes p = yes (inR p)
--Var? (X ∪ Y) | no ¬p | no ¬p₁ = no (λ {(inL x) → ¬p x; (inR x) → ¬p₁ x}) -- no (λ ¬e → ¬p (λ x → ¬e (inL x)))
--
--
--
--
--
----
--outS : ∀{Y}{a : Val Y}{y : Var Y} → IsIn y (S a) → IsIn y a
--outS (isS a) = a
--
--  
--surjₚ : {X : VarSet} → Val X → Set
--surjₚ {X} a = (x : Var X) → IsIn x a
--
--surj : {X Y : VarSet} → (X ⇀ Y) → Set
--surj {X} {Y} σ = (y : Var Y) → ∃ (λ x → IsIn y (σ x))
--
--
--_⊆_ : ∀{X Y Z} → Y ⇀ Z → X ⇀ Z → Set
--τ' ⊆ τ = ∃ (λ σ → τ ≡ σ >=> τ' × surj σ)
--
--≤-refl : ∀{n} → n ≤ n
--≤-refl {zero} = z≤n
--≤-refl {suc n} = s≤s ≤-refl
--
--addsuc : ∀{m n} → m + suc n ≡ suc (m + n) 
--addsuc {zero} = refl
--addsuc {suc m} = cong suc (addsuc {m})
--
--≤-add' : ∀{m p} → (o : ℕ) → m ≤ p → m ≤ o + p
--≤-add' o z≤n = z≤n
--≤-add' {suc m}{suc p} o (s≤s le) = subst (λ x → suc m ≤ x) (sym (addsuc {o})) (s≤s (≤-add' o le)) 
--
--≤-add : ∀{m n o p} → m ≤ o → n ≤ p → m + n ≤ o + p
--≤-add {o = o} z≤n le' = ≤-add' o le'
--≤-add (s≤s le) le' = s≤s (≤-add le le')
--
--≤-suc : ∀{m n} → m ≤ n → m ≤ suc n
--≤-suc z≤n = z≤n
--≤-suc (s≤s o) = s≤s (≤-suc o)
--
--<-add : ∀{a b c d} → a < b → c ≤ d → (a + c) < (b + d)
--<-add o o' = ≤-add o o' 
--
--<-add2 : ∀{a b c d} → a ≤ b → c < d → (a + c) < (b + d)
--<-add2 {a}{b}{c}{suc d} z (s≤s o) = 
--       subst (λ x → suc (a + c) ≤ x) (sym (addsuc {b}{d})) (s≤s (≤-add z o))
--       
--countEmpty : {Y Z : VarSet} → Empty Y → (τ : Y ⇀ Z) → 0 ≡ count τ 
--countEmpty {∅} e τ = refl
--countEmpty {V1} e τ = ⊥-elim (e here)
--countEmpty {Y ∪ Y₁} e τ = cong₂ _+_ (countEmpty {Y} (e ∘ inL) (τ ∘ inL)) (countEmpty {Y₁} (e ∘ inR) (τ ∘ inR))
--
--notRL : ∀{X Y}{x : Var X}{y : Var Y} → inR x ≡ inL y → ⊥
--notRL ()
--
--add0 : (m : ℕ) → m + 0 ≡ m
--add0 zero = refl
--add0 (suc m) = cong suc (add0 m)
--
--count1 : {Y Z : VarSet} → (x : Var1 Y) → (τ : Y ⇀ Z) → count τ ≡ countₚ (τ (proj₁ x))
--count1 {∅} (() , eq) τ
--count1 {V1} (x , eq) τ with eq here
--count1 {V1} (.here , eq) τ | refl = refl
--count1 {X ∪ Y₁} (inL x , eq) τ = 
--    let r = count1 {X} (x , (λ x₁ → outL (eq (inL x₁)))) (τ ∘ inL) 
--        r' = countEmpty (λ x₁ → ⊥-elim (notRL (eq (inR x₁)))) (τ ∘ inR) 
--       in trans (cong₂ _+_ r (sym r')) (add0 (countₚ (τ (inL x))))
--count1 {X ∪ X'} (inR x , eq) τ = let 
--        r = count1 (x , (λ x₁ → outR (eq (inR x₁)))) (τ ∘ inR) 
--        r' = countEmpty (λ x₁ → ⊥-elim (notRL (sym (eq (inL x₁))))) (τ ∘ inL) 
--       in cong₂ _+_ (sym r') r 
--
--countPoint : ∀{Y Z} → (a : Val Y) → surjₚ a →  (τ : Y ⇀ Z) → count τ ≤ countₚ (a >>= τ)
--countPoint {Y} (fvar x) sur τ with Varn? Y 
--countPoint (fvar x₁) sur τ | inj₁ (inj₁ x) = ⊥-elim (x x₁)
--countPoint (fvar x) sur τ | inj₁ (inj₂ (x' , eq)) with eq x 
--countPoint (fvar x') sur τ | inj₁ (inj₂ (.x' , eq)) | refl = subst (λ x → x ≤ (countₚ (τ x'))) (sym (count1 (x' , eq) τ)) ≤-refl -- count1
--countPoint (fvar x) sur τ | inj₂ (y , y' , ne) with sur y | sur y' 
--countPoint (fvar y') sur τ | inj₂ (.y' , .y' , ne) | here | here = ⊥-elim (ne refl)
--countPoint {Y} Z sur τ with Var? Y
--countPoint Z sur τ | yes x with sur x
--countPoint Z sur τ | yes x | () -- 
--countPoint Z sur τ | no ¬p = subst (λ x → x ≤ 1) (countEmpty ¬p τ) z≤n
--countPoint (S a) sur τ = ≤-suc (countPoint a (outS ∘ sur) τ)
--
--<-countPoint : ∀{Y Z} → (a : Val Y) → surjₚ a × ((y : Var Y) → a ≠ fvar y) →  (τ : Y ⇀ Z) → count τ < countₚ (a >>= τ)
--<-countPoint (fvar x) (sur , ¬a) τ = ⊥-elim (¬a x refl)
--<-countPoint {Y} Z (sur , ¬a) τ with Var? Y
--<-countPoint Z (sur , ¬a) τ | yes x with sur x
--<-countPoint Z (sur , ¬a) τ | yes x | () -- 
--<-countPoint Z (sur , ¬a) τ | no ¬p = subst (λ x → suc x ≤ 1) (countEmpty ¬p τ) (s≤s (z≤n {0}))
--<-countPoint (S a) (sur , ¬a) τ = s≤s (countPoint a (outS ∘ sur) τ)
--
--substEq : {A : Set}{x y : A} (P : (a : A) → (x ≡ a) → Set) → (eq : x ≡ y) → P x refl → P y eq
--substEq P refl p = p 
--
--countS : {X Y Z : VarSet} → (x : Var X) → {a : Val Y} → surjₚ a → 
--                (τ : (X [ x // Y ]) ⇀ Z) → count τ ≤ count ((x / a) >=> τ)
--countS {∅} () sur τ
--countS {V1} here {a} sur τ = countPoint a sur τ
--countS {X ∪ X₁} (inL x) {a} sur τ = let 
--  le = countS x sur (τ ∘ inL) 
--  le' = subst (λ x₁ → count (τ ∘ inL) ≤ count x₁) 
--                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inL) τ))) le 
--   in ≤-add le' ≤-refl 
--countS {X ∪ X₁} (inR x) {a} sur τ = let 
--  le = countS x {a} sur (τ ∘ inR) 
--  le' = subst (λ x₁ → count (τ ∘ inR) ≤ count x₁) 
--                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inR) τ))) le 
--   in ≤-add {count (τ ∘ inL)} ≤-refl le' 
--   
--AdvPoint : {Y : VarSet} → Val Y → Set
--AdvPoint {Y} a = surjₚ a × ((y : Var Y) → a ≠ fvar y)
--   
--<-count : {X Y Z : VarSet} → (x : Var X) → {a : Val Y} → AdvPoint a → 
--                (τ : (X [ x // Y ]) ⇀ Z) → count τ < count ((x / a) >=> τ)
--<-count {∅} () sur τ
--<-count {V1} here {a} sur τ = <-countPoint a sur τ
--<-count {X ∪ X₁} (inL x) {a} sur τ = let 
--  le = <-count x sur (τ ∘ inL) 
--  le' = subst (λ x₁ → count (τ ∘ inL) < count x₁) 
--                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inL) τ))) le 
--   in <-add le' ≤-refl 
--<-count {X ∪ X₁} (inR x) {a} sur τ = let 
--  le = <-count x {a} sur (τ ∘ inR) 
--  le' = subst (λ x₁ → count (τ ∘ inR) < count x₁) 
--                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inR) τ))) le 
--   in <-add2 {count (τ ∘ inL)} ≤-refl le' 
--
--countSurj : {X Y Z : VarSet} → (τ : X ⇀ Z) → (x : Var X) → {a : Val Y} → surjₚ a →
--          (τ' : X [ x // Y ] ⇀ Z) → τ ≡ (x / a) >=> τ' → count τ' ≤ count τ
--countSurj ._ x sur τ' refl = countS x sur τ'
--
--data Acc {A : Set} (_<-t_ : A → A → Set) (x : A) : Set where
--  acc : ({y : A} → (y <-t x) → Acc (_<-t_) y) →  Acc (_<-t_) x
--  
--transN : ∀{m n o} → m ≤ n → n ≤ o → m ≤ o
--transN z≤n o' = z≤n
--transN (s≤s o₁) (s≤s o') = s≤s (transN o₁ o')
--  
--acc-< : (n : ℕ) → Acc _<_ n 
--acc-< n = acc (go n) 
--  where
--    go : (n : ℕ) → {m : ℕ} → m < n → Acc _<_ m 
--    go zero {m} ()
--    go (suc n) {zero} lt = acc (λ ())
--    go (suc n) {suc m} (s≤s m<n) = acc (λ {o} o<sm → go n {o} (transN o<sm m<n))
--    
--<-func : {A : Set} → (A → A → Set) → (f : A → ℕ) → Set
--<-func {A} _<<_ f = {x y : A} → x << y → f x < f y
--
--acc-<<' : {A : Set}{_<<_ : A → A → Set}{f : A → ℕ} → <-func _<<_ f → (x : A) → Acc _<_ (f x) → Acc _<<_ x 
--acc-<<' fu x (acc g) = acc (λ {y} y<<x → acc-<<' fu y (g (fu y<<x)))
-- 
--acc-<< : {A : Set}{_<<_ : A → A → Set}{f : A → ℕ} → <-func _<<_ f → (x : A) → Acc _<<_ x 
--acc-<< {f = f} fu x = acc-<<' fu x (acc-< (f x))
 

