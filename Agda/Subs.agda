module Subs where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Helpful
open import Data.Empty
open import Function
open import Relation.Nullary 
open import Data.Nat 

postulate ext : {A B : Set}{f g : A → B} →  ((x : A) → f x ≡ g x) → f ≡ g
 
data VarSet : Set where
  ∅ : VarSet
  V1 : VarSet
  _∪_ : VarSet → VarSet → VarSet
  
data Var : VarSet → Set where
  here : Var V1
  inL : {X Y : VarSet} → (x : Var X) → Var (X ∪ Y)
  inR : {X Y : VarSet} → (x : Var Y) → Var (X ∪ Y)

  
data Val (X : VarSet) : Set where
  fvar : (x : Var X) → Val X
  Z : Val X 
  S : Val X → Val X

Empty : VarSet → Set
Empty V = ¬ (Var V)

Var? : (V : VarSet) → Dec (Var V)
Var? ∅ = no (λ ())
Var? V1 = yes here -- (λ ¬e → ¬e here) 
Var? (X ∪ Y) with Var? X | Var? Y 
Var? (X ∪ Y) | yes p1 | b = yes (inL p1) -- yes (λ {(inL x) → p1 x ; (inR y) → p2 y})
Var? (X ∪ Y) | no ¬p | yes p = yes (inR p)
Var? (X ∪ Y) | no ¬p | no ¬p₁ = no (λ {(inL x) → ¬p x; (inR x) → ¬p₁ x}) -- no (λ ¬e → ¬p (λ x → ¬e (inL x)))

_⇀_ : VarSet → VarSet → Set
_⇀_ X Y = Var X → Val Y

Inp : VarSet → Set
Inp X = Var X → Val ∅

⇀-id : ∀{X} → X ⇀ X
⇀-id x = fvar x

coll : ∀{Y} → Empty Y → Var Y → Var ∅
coll p x = ⊥-elim (p x)

_>>=_ : {X Y : VarSet} →  Val X → (X ⇀ Y) → Val Y
fvar x >>= f = f x
Z >>= f = Z
S a >>= f = S (a >>= f)

collapse : ∀{X Y} → X ⇀ Y → Empty Y → X ⇀ ∅
collapse τ p x = τ x >>= (fvar ∘ coll p)

_>=>_ : {X Y Z : VarSet} → (X ⇀ Y) → (Y ⇀ Z) → X ⇀ Z
_>=>_ f g a = f a >>= g

return : {X : VarSet} → (x : Var X) → Val X
return = fvar

>>=-left : {X Y : VarSet} → (x : Var X) → (f : (X ⇀ Y)) → return x >>= f ≡ f x
>>=-left x f = refl

>>=-right : {X : VarSet} → (a : Val X) → a >>= return ≡ a
>>=-right (fvar x) = refl
>>=-right Z = refl
>>=-right (S a) = cong S (>>=-right a) 

>>=-assoc : {X Y Z : VarSet} → (a : Val X) → (f : X ⇀ Y) → (g : Y ⇀ Z) → 
             (a >>= f) >>= g ≡ a >>= (λ a → (f a >>= g))
>>=-assoc (fvar x) f g = refl
>>=-assoc Z f g = refl
>>=-assoc (S a) f g = cong S (>>=-assoc a f g)

_[_//_] : (X : VarSet) → (x : Var X) → VarSet → VarSet
∅ [ () // Y ]
V1 [ here // Y ] = Y
(X1 ∪ X2) [ inL x // Y ] = (X1 [ x // Y ]) ∪ X2
(X1 ∪ X2) [ inR x // Y ] =  X1 ∪ (X2 [ x // Y ])

_/_ : {X Y : VarSet} → (x : Var X) → Val Y → X ⇀ (X [ x // Y ]) 
_/_ here a here = a
_/_ (inL x) a (inL y) = (x / a) y >>= (λ a → fvar (inL a)) 
_/_ (inR x) a (inL y) = fvar (inL y)
_/_ (inL x) a (inR y) = fvar (inR y)
_/_ (inR x) a (inR y) = (x / a) y >>= (fvar ∘ inR) 

embed : {X Y : VarSet} → (x : Var X) → Var Y → Var (X [ x // Y ]) 
embed here y = y
embed (inL x) y = inL (embed x y)
embed (inR x) y = inR (embed x y)

point-look : {X Y : VarSet} → (x : Var X) → (a : Val Y) → (x / a) x ≡ a >>= (fvar ∘ embed x)
point-look here a = sym (>>=-right a)
point-look (inL x) a = let 
  eq = cong (λ a' → a' >>= (fvar ∘ inL)) (point-look x a)
    in trans eq (>>=-assoc a (fvar ∘ embed x) (fvar ∘ inL))
point-look (inR x) a = let 
  eq = cong (λ a' → a' >>= (fvar ∘ inR)) (point-look x a)
    in trans eq (>>=-assoc a (fvar ∘ embed x) (fvar ∘ inR))

data MinVal : {X : VarSet} → Val X → Set where
   bindZ : MinVal {∅} Z
   bindS : MinVal {V1} (S (fvar here))
   
data LNarr {X : VarSet} (x : Var X) : {Y : VarSet} → X ⇀ Y → Set where
   narr : ∀{Y} {a : Val Y} → MinVal a → LNarr x (x / a)

--LNarr : {V : ℕ}{X : VarSet} → (x : Var X) → {Y : VarSet} → (X ⇀ Y) → Set
--LNarr x {Y}  = {!!}

_⊑ₚ_ : ∀{X Y} → Val X → Val Y → Set 
n ⊑ₚ m = ∃ (λ σ → m ≡ n >>= σ)

_⊑_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
σ ⊑ τ = ∃ (λ σ' → τ ≡ σ >=> σ')

_⊏_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
σ ⊏ τ = σ ⊑ τ × ¬ (τ ⊑ σ)

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
  
point-adv : ∀{X Y} → (x : Var X)  → (a : Val Y) → ((y : Var Y) → a ≠ fvar y)  →  ¬ ((x / a) ⊑ return)
point-adv x (fvar y) ne (σ , eq) = ⊥-elim (ne y refl)  
point-adv x Z ne (σ , eq) with subst (λ p → return x ≡ p >>= σ) (point-look x Z) (cong (λ f → f x) eq)
point-adv x Z ne (σ , eq) | ()
point-adv x (S a) ne (σ , eq) with subst (λ p → return x ≡ p >>= σ) (point-look x (S a)) (cong (λ f → f x) eq)
point-adv x (S a) ne (σ , eq) | ()

data WFSub {X : VarSet} : {Y : VarSet} → X ⇀ Y → Set where
   [] : WFSub return 
   _∷_ : ∀{Y Z} → (x : Var X) → (a : Val Y) → {σ : X [ x // Y ] ⇀ Z} → 
                               WFSub σ → WFSub ((x / a) >=> σ)
                               

countₚ : {X : VarSet} → Val X → ℕ
countₚ (fvar x) = 0 
countₚ Z = 1
countₚ (S a) = 1 + countₚ a

Var1 : VarSet → Set
Var1 Y = Σ (Var Y) (λ y → (x : Var Y) → x ≡ y)  

Var2 : VarSet → Set
Var2 Y = Σ (Var Y) (λ y → Σ (Var Y) (λ y' → y ≠ y'))

outL : ∀{Y X}{y y' : Var Y} → inL {Y = X} y ≡ inL y' → y ≡ y'
outL refl = refl

outR : ∀{Y X}{y y' : Var Y} → inR {X = X} y ≡ inR y' → y ≡ y'
outR refl = refl

Varn? : (Y : VarSet) → (Empty Y ⊎ Var1 Y) ⊎ Var2 Y
Varn? ∅ = inj₁ (inj₁ (λ ()))
Varn? V1 = inj₁ (inj₂ (here , (λ {here → refl})))
Varn? (Y ∪ Y₁) with (Varn? Y) | (Varn? Y₁) 
Varn? (Y ∪ Y₁) | inj₁ (inj₁ x) | inj₁ (inj₁ x₁) = inj₁ (inj₁ (λ {(inL y) → x y; (inR y) → x₁ y}))
Varn? (Y ∪ Y₁) | inj₁ (inj₁ x) | inj₁ (inj₂ (y , eq)) = 
      inj₁ (inj₂ (inR y , (λ {(inL y') → ⊥-elim (x y'); (inR y') → cong inR (eq y')})))
Varn? (Y ∪ Y₁) | inj₁ (inj₂ (y , eq)) | inj₁ (inj₁ x) = 
  inj₁ (inj₂ (inL y , (λ {(inL y') → cong inL (eq y') ; (inR y') → ⊥-elim (x y')})))
Varn? (Y ∪ Y₁) | inj₁ (inj₂ (y , _)) | inj₁ (inj₂ (y' , _)) = inj₂ (inL y , inR y' , (λ {()}))
Varn? (Y ∪ Y₁) | inj₁ c | inj₂ (y , y' , ne) = inj₂ ((inR y) , ((inR y') , (λ x → ne (outR x))))
Varn? (Y ∪ Y₁) | inj₂ (y , y' , ne) | d = inj₂ ((inL y) , ((inL y') , (λ x → ne (outL x))))


count : ∀{X Y} → X ⇀ Y → ℕ
count {∅} σ = 0
count {V1} σ = countₚ (σ here)
count {X ∪ X₁} σ = count (σ ∘ inL) + count (σ ∘ inR)

data IsIn {Y : VarSet} (y : Var Y) : (Val Y) → Set where
  here : IsIn y (fvar y)
  isS : {a : Val Y} → IsIn y a → IsIn y (S a)
  
outS : ∀{Y}{a : Val Y}{y : Var Y} → IsIn y (S a) → IsIn y a
outS (isS a) = a

  
surjₚ : {X : VarSet} → Val X → Set
surjₚ {X} a = (x : Var X) → IsIn x a

surj : {X Y : VarSet} → (X ⇀ Y) → Set
surj {X} {Y} σ = (y : Var Y) → ∃ (λ x → IsIn y (σ x))


_⊆_ : ∀{X Y Z} → Y ⇀ Z → X ⇀ Z → Set
τ' ⊆ τ = ∃ (λ σ → τ ≡ σ >=> τ' × surj σ)

≤-refl : ∀{n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

addsuc : ∀{m n} → m + suc n ≡ suc (m + n) 
addsuc {zero} = refl
addsuc {suc m} = cong suc (addsuc {m})

≤-add' : ∀{m p} → (o : ℕ) → m ≤ p → m ≤ o + p
≤-add' o z≤n = z≤n
≤-add' {suc m}{suc p} o (s≤s le) = subst (λ x → suc m ≤ x) (sym (addsuc {o})) (s≤s (≤-add' o le)) 

≤-add : ∀{m n o p} → m ≤ o → n ≤ p → m + n ≤ o + p
≤-add {o = o} z≤n le' = ≤-add' o le'
≤-add (s≤s le) le' = s≤s (≤-add le le')

≤-suc : ∀{m n} → m ≤ n → m ≤ suc n
≤-suc z≤n = z≤n
≤-suc (s≤s o) = s≤s (≤-suc o)

<-add : ∀{a b c d} → a < b → c ≤ d → (a + c) < (b + d)
<-add o o' = ≤-add o o' 

<-add2 : ∀{a b c d} → a ≤ b → c < d → (a + c) < (b + d)
<-add2 {a}{b}{c}{suc d} z (s≤s o) = 
       subst (λ x → suc (a + c) ≤ x) (sym (addsuc {b}{d})) (s≤s (≤-add z o))
       
countEmpty : {Y Z : VarSet} → Empty Y → (τ : Y ⇀ Z) → 0 ≡ count τ 
countEmpty {∅} e τ = refl
countEmpty {V1} e τ = ⊥-elim (e here)
countEmpty {Y ∪ Y₁} e τ = cong₂ _+_ (countEmpty {Y} (e ∘ inL) (τ ∘ inL)) (countEmpty {Y₁} (e ∘ inR) (τ ∘ inR))

notRL : ∀{X Y}{x : Var X}{y : Var Y} → inR x ≡ inL y → ⊥
notRL ()

add0 : (m : ℕ) → m + 0 ≡ m
add0 zero = refl
add0 (suc m) = cong suc (add0 m)

count1 : {Y Z : VarSet} → (x : Var1 Y) → (τ : Y ⇀ Z) → count τ ≡ countₚ (τ (proj₁ x))
count1 {∅} (() , eq) τ
count1 {V1} (x , eq) τ with eq here
count1 {V1} (.here , eq) τ | refl = refl
count1 {X ∪ Y₁} (inL x , eq) τ = 
    let r = count1 {X} (x , (λ x₁ → outL (eq (inL x₁)))) (τ ∘ inL) 
        r' = countEmpty (λ x₁ → ⊥-elim (notRL (eq (inR x₁)))) (τ ∘ inR) 
       in trans (cong₂ _+_ r (sym r')) (add0 (countₚ (τ (inL x))))
count1 {X ∪ X'} (inR x , eq) τ = let 
        r = count1 (x , (λ x₁ → outR (eq (inR x₁)))) (τ ∘ inR) 
        r' = countEmpty (λ x₁ → ⊥-elim (notRL (sym (eq (inL x₁))))) (τ ∘ inL) 
       in cong₂ _+_ (sym r') r 

countPoint : ∀{Y Z} → (a : Val Y) → surjₚ a →  (τ : Y ⇀ Z) → count τ ≤ countₚ (a >>= τ)
countPoint {Y} (fvar x) sur τ with Varn? Y 
countPoint (fvar x₁) sur τ | inj₁ (inj₁ x) = ⊥-elim (x x₁)
countPoint (fvar x) sur τ | inj₁ (inj₂ (x' , eq)) with eq x 
countPoint (fvar x') sur τ | inj₁ (inj₂ (.x' , eq)) | refl = subst (λ x → x ≤ (countₚ (τ x'))) (sym (count1 (x' , eq) τ)) ≤-refl -- count1
countPoint (fvar x) sur τ | inj₂ (y , y' , ne) with sur y | sur y' 
countPoint (fvar y') sur τ | inj₂ (.y' , .y' , ne) | here | here = ⊥-elim (ne refl)
countPoint {Y} Z sur τ with Var? Y
countPoint Z sur τ | yes x with sur x
countPoint Z sur τ | yes x | () -- 
countPoint Z sur τ | no ¬p = subst (λ x → x ≤ 1) (countEmpty ¬p τ) z≤n
countPoint (S a) sur τ = ≤-suc (countPoint a (outS ∘ sur) τ)

<-countPoint : ∀{Y Z} → (a : Val Y) → surjₚ a × ((y : Var Y) → a ≠ fvar y) →  (τ : Y ⇀ Z) → count τ < countₚ (a >>= τ)
<-countPoint (fvar x) (sur , ¬a) τ = ⊥-elim (¬a x refl)
<-countPoint {Y} Z (sur , ¬a) τ with Var? Y
<-countPoint Z (sur , ¬a) τ | yes x with sur x
<-countPoint Z (sur , ¬a) τ | yes x | () -- 
<-countPoint Z (sur , ¬a) τ | no ¬p = subst (λ x → suc x ≤ 1) (countEmpty ¬p τ) (s≤s (z≤n {0}))
<-countPoint (S a) (sur , ¬a) τ = s≤s (countPoint a (outS ∘ sur) τ)

substEq : {A : Set}{x y : A} (P : (a : A) → (x ≡ a) → Set) → (eq : x ≡ y) → P x refl → P y eq
substEq P refl p = p 

countS : {X Y Z : VarSet} → (x : Var X) → (a : Val Y) → surjₚ a → 
                (τ : (X [ x // Y ]) ⇀ Z) → count τ ≤ count ((x / a) >=> τ)
countS {∅} () a sur τ
countS {V1} here a sur τ = countPoint a sur τ
countS {X ∪ X₁} (inL x) a sur τ = let 
  le = countS x a sur (τ ∘ inL) 
  le' = subst (λ x₁ → count (τ ∘ inL) ≤ count x₁) 
                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inL) τ))) le 
   in ≤-add le' ≤-refl 
countS {X ∪ X₁} (inR x) a sur τ = let 
  le = countS x a sur (τ ∘ inR) 
  le' = subst (λ x₁ → count (τ ∘ inR) ≤ count x₁) 
                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inR) τ))) le 
   in ≤-add {count (τ ∘ inL)} ≤-refl le' 
   
<-count : {X Y Z : VarSet} → (x : Var X) → (a : Val Y) → surjₚ a × ((y : Var Y) → a ≠ fvar y) → 
                (τ : (X [ x // Y ]) ⇀ Z) → count τ < count ((x / a) >=> τ)
<-count {∅} () a sur τ
<-count {V1} here a sur τ = <-countPoint a sur τ
<-count {X ∪ X₁} (inL x) a sur τ = let 
  le = <-count x a sur (τ ∘ inL) 
  le' = subst (λ x₁ → count (τ ∘ inL) < count x₁) 
                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inL) τ))) le 
   in <-add le' ≤-refl 
<-count {X ∪ X₁} (inR x) a sur τ = let 
  le = <-count x a sur (τ ∘ inR) 
  le' = subst (λ x₁ → count (τ ∘ inR) < count x₁) 
                           (sym (ext (λ x' → >>=-assoc ((x / a) x') (fvar ∘ inR) τ))) le 
   in <-add2 {count (τ ∘ inL)} ≤-refl le' 

countSurj : {X Y Z : VarSet} → (τ : X ⇀ Z) → (x : Var X) → (a : Val Y) → surjₚ a →
          (τ' : X [ x // Y ] ⇀ Z) → τ ≡ (x / a) >=> τ' → count τ' ≤ count τ
countSurj ._ x a sur τ' refl = countS x a sur τ'

data Acc {A : Set} (_<-t_ : A → A → Set) (x : A) : Set where
  acc : ({y : A} → (y <-t x) → Acc (_<-t_) y) →  Acc (_<-t_) x
  
transN : ∀{m n o} → m ≤ n → n ≤ o → m ≤ o
transN z≤n o' = z≤n
transN (s≤s o₁) (s≤s o') = s≤s (transN o₁ o')
  
acc-< : (n : ℕ) → Acc _<_ n 
acc-< n = acc (go n) 
  where
    go : (n : ℕ) → {m : ℕ} → m < n → Acc _<_ m 
    go zero {m} ()
    go (suc n) {zero} lt = acc (λ ())
    go (suc n) {suc m} (s≤s m<n) = acc (λ {o} o<sm → go n {o} (transN o<sm m<n))
    
<-func : {A : Set} → (A → A → Set) → (f : A → ℕ) → Set
<-func {A} _<<_ f = {x y : A} → x << y → f x < f y

acc-<<' : {A : Set}{_<<_ : A → A → Set}{f : A → ℕ} → <-func _<<_ f → (x : A) → Acc _<_ (f x) → Acc _<<_ x 
acc-<<' fu x (acc g) = acc (λ {y} y<<x → acc-<<' fu y (g (fu y<<x)))
 
acc-<< : {A : Set}{_<<_ : A → A → Set}{f : A → ℕ} → <-func _<<_ f → (x : A) → Acc _<<_ x 
acc-<< {f = f} fu x = acc-<<' fu x (acc-< (f x))
  
