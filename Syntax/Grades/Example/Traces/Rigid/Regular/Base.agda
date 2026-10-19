------------------------------------------------------------------------
-- Rigid timed regular grades in whole steps: the closed languages of --
-- slots, and the literals of one-sided expressions.                  --
--                                                                    --
-- A grade is a non-empty regular language over the slot letters      --
-- (`Exact.Slots`) closed downward under the slot order. The literal  --
-- of a one-sided expression `e` is the closure of the encodings of   --
-- the exact words `e` denotes, and literals compare as their sets of --
-- exact words do:                                                    --
--                                                                    --
--   ⌜ e ⌝ ≾ ⌜ f ⌝   iff   ⟦ e ⟧ ≾ ⟦ f ⟧                               --
--                                                                    --
-- An expression is compiled to an extended regular expression over   --
-- the letters: an operation to the slots of each of its running      --
-- times, a stretch to runs of its slot of each length its end        --
-- admits.                                                            --
--                                                                    --
-- Operations are coded bijectively into `Fin n`.                     --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Regular.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List.Base using (List; []; _∷_; _++_; map; applyUpTo; replicate; allFin)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s; _≡ᵇ_)
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; ∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Intervals ℕᵀ
  using (Cut; Hi; fin; ∞; _⊑ʰ_; ⁻; ⁺; by-pt; by-side; ⊑⇒≤; ≤⇒⁻⊑⁻; ≤⇒⁺⊑⁺;
         ⁻≤; ⁺≤⁺; Interval; lo; hi; pt; side)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-trans to ⊑ᶜ-trans)
open import Syntax.Durations.Intervals.Dense ℕᵀ using (_∈ⁱ_; ⁺⋢⁻)

open Equivalence using (to; from)

-- coding is injective

code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

open RunningTimes.RunningTimes running using (rt; rt-bounded; rt-positive)
open RunningTimes ℕᵀ Op using (Bounded)

open import Syntax.Grades.Exact.Base ℕᵀ Op n code code-injective public
open import Syntax.Grades.Exact.Order ℕᵀ Op n code code-injective public
open import Syntax.Grades.Exact.Lift ℕᵀ Op n code code-injective public
open import Syntax.Grades.Exact.Expression ℕᵀ Op n code code-injective running public
open import Syntax.Grades.Exact.Slots Op n code code-injective public

import Syntax.Grades.Regular.Automaton k as A
import Syntax.Grades.Regular.Expression k as RE
open import Syntax.Grades.Regular.Closure k using (↓; ↓-wf) renaming (Below to Belowᴿ)
import Syntax.Grades.Regular.Closed as Closedᴿ
module C = Closedᴿ k tick _≤ᶠ_ ≤ᶠ-refl ≤ᶠ-trans
open C public using (Closed; lang)

------------------------------------------------------------------------
-- The ends of an interval, as numbers

-- the least length a lower end admits

lo# : Cut → ℕ
lo# (p ∣ᶜ ⁻) = p
lo# (p ∣ᶜ ⁺) = suc p

lo#-sound : ∀ c {t} → c  ⊑ᶜ (t ∣ᶜ ⁻) → lo# c ≤ t
lo#-sound (p ∣ᶜ ⁻) r = ⊑⇒≤ r
lo#-sound (p ∣ᶜ ⁺) {t} r with suc p ℕ.≤? t
... | yes s = s
... | no ¬s = ⊥-elim (⁺⋢⁻ (⊑ᶜ-trans r (≤⇒⁻⊑⁻ (ℕ.≤-pred (ℕ.≰⇒> ¬s)))))

lo#-complete : ∀ c {t} → lo# c ≤ t → c  ⊑ᶜ (t ∣ᶜ ⁻)
lo#-complete (p ∣ᶜ ⁻) s = ≤⇒⁻⊑⁻ s
lo#-complete (p ∣ᶜ ⁺) s = by-pt (ℕ.<⇒≱ s)

-- the least length an upper cut does not admit

hiS : Cut → ℕ
hiS (q ∣ᶜ ⁻) = q
hiS (q ∣ᶜ ⁺) = suc q

hiS-sound : ∀ c {t} → (t ∣ᶜ ⁺) ⊑ᶜ c → t < hiS c
hiS-sound (q ∣ᶜ ⁺) r = s≤s (⊑⇒≤ r)
hiS-sound (q ∣ᶜ ⁻) {t} r with suc t ℕ.≤? q
... | yes s = s
... | no ¬s = ⊥-elim (⁺⋢⁻ (⊑ᶜ-trans (≤⇒⁺⊑⁺ (ℕ.≤-pred (ℕ.≰⇒> ¬s))) r))

hiS-complete : ∀ c {t} → t < hiS c → (t ∣ᶜ ⁺) ⊑ᶜ c
hiS-complete (q ∣ᶜ ⁺) (s≤s s) = ≤⇒⁺⊑⁺ s
hiS-complete (q ∣ᶜ ⁻) s       = by-pt (ℕ.<⇒≱ s)

-- the upper end of a running time, a cut

hi-cut : Op → Cut
hi-cut o with hi (rt o) | rt-bounded o
... | fin c | _ = c

hi-cut-≡ : ∀ o → hi (rt o) ≡ fin (hi-cut o)
hi-cut-≡ o with hi (rt o) | rt-bounded o
... | fin c | Bounded.fin .c = refl

-- an operation takes at least a step

lo#-pos : ∀ o → 1 ≤ lo# (lo (rt o))
lo#-pos o = case (lo (rt o)) (rt-positive o)
  where
    case : ∀ c → (0 ∣ᶜ ⁺) ⊑ᶜ c → 1 ≤ lo# c
    case (p ∣ᶜ ⁻) r = lo#-sound (0 ∣ᶜ ⁺) r
    case (p ∣ᶜ ⁺) r = s≤s z≤n

------------------------------------------------------------------------
-- Extended regular expressions: the empty language, single words,
-- finite unions

∅ʳ : RE.Expr
∅ʳ = RE.Σ RE.& RE.~ RE.Σ

∅ʳ-empty : ∀ {w} → ¬ RE.⟦ ∅ʳ ⟧ w
∅ʳ-empty (p , ¬p) = ¬p p

lit : List (Fin k) → RE.Expr
lit []      = RE.ε
lit (a ∷ w) = RE.‵ a RE.· lit w

lit-sound : ∀ w {v} → RE.⟦ lit w ⟧ v → v ≡ w
lit-sound []      refl = refl
lit-sound (a ∷ w) (u , v , refl , refl , v∈) = cong (a ∷_) (lit-sound w v∈)

lit-complete : ∀ w → RE.⟦ lit w ⟧ w
lit-complete []      = refl
lit-complete (a ∷ w) = a ∷ [] , w , refl , refl , lit-complete w

-- the union of `f j` for `j < m`

⋃< : (ℕ → RE.Expr) → ℕ → RE.Expr
⋃< f zero    = ∅ʳ
⋃< f (suc m) = ⋃< f m RE.∣ f m

⋃<-sound : ∀ f m {w} → RE.⟦ ⋃< f m ⟧ w → Σ[ j ∈ ℕ ] j < m × RE.⟦ f j ⟧ w
⋃<-sound f zero    w∈ = ⊥-elim (∅ʳ-empty w∈)
⋃<-sound f (suc m) (inj₁ w∈) with ⋃<-sound f m w∈
... | j , j< , fj = j , ℕ.m≤n⇒m≤1+n j< , fj
⋃<-sound f (suc m) (inj₂ w∈) = m , ℕ.≤-refl , w∈

⋃<-complete : ∀ f m {w j} → j < m → RE.⟦ f j ⟧ w → RE.⟦ ⋃< f m ⟧ w
⋃<-complete f (suc m) {j = j} j< fj with j ℕ.≟ m
... | yes refl = inj₂ fj
... | no j≢m   = inj₁ (⋃<-complete f m (ℕ.≤∧≢⇒< (ℕ.≤-pred j<) j≢m) fj)

-- the union of `f c` over the codes

⋃ˡ : List (Fin n) → (Fin n → RE.Expr) → RE.Expr
⋃ˡ []       f = ∅ʳ
⋃ˡ (c ∷ cs) f = f c RE.∣ ⋃ˡ cs f

⋃ˡ-sound : ∀ cs f {w} → RE.⟦ ⋃ˡ cs f ⟧ w → Σ[ c ∈ Fin n ] RE.⟦ f c ⟧ w
⋃ˡ-sound []       f w∈        = ⊥-elim (∅ʳ-empty w∈)
⋃ˡ-sound (c ∷ cs) f (inj₁ w∈) = c , w∈
⋃ˡ-sound (c ∷ cs) f (inj₂ w∈) = ⋃ˡ-sound cs f w∈

⋃ˡ-complete : ∀ cs f {w c} → c ∈ˡ cs → RE.⟦ f c ⟧ w → RE.⟦ ⋃ˡ cs f ⟧ w
⋃ˡ-complete (c ∷ cs) f (here refl) w∈ = inj₁ w∈
⋃ˡ-complete (_ ∷ cs) f (there c∈)  w∈ = inj₂ (⋃ˡ-complete cs f c∈ w∈)

-- iterations of one letter

star-letter-sound : ∀ a {w} → RE.⟦ RE.‵ a RE.* ⟧ w → Σ[ t ∈ ℕ ] w ≡ replicate t a
star-letter-sound a (RE.none refl) = 0 , refl
star-letter-sound a (RE.more u v refl refl vs) with star-letter-sound a vs
... | t , refl = suc t , refl

star-letter-complete : ∀ a t → RE.⟦ RE.‵ a RE.* ⟧ (replicate t a)
star-letter-complete a zero    = RE.none refl
star-letter-complete a (suc t) = RE.more (a ∷ []) (replicate t a) refl refl (star-letter-complete a t)

replicate-+ : ∀ {A : Set} m j (a : A) → replicate (m + j) a ≡ replicate m a ++ replicate j a
replicate-+ zero    j a = refl
replicate-+ (suc m) j a = cong (a ∷_) (replicate-+ m j a)

------------------------------------------------------------------------
-- The letters of exact words

sˢ : OpSet → Fin k
sˢ S = encode (inˢ S)

opWord : Fin n → ℕ → List (Fin k)
opWord c t = map encode (applyUpTo (λ p → opˢ c (p ≡ᵇ 0) (suc p ≡ᵇ t)) t)

private
  applyUpTo-cong : ∀ {B : Set} (f g : ℕ → B) m → (∀ p → p < m → f p ≡ g p)
                 → applyUpTo f m ≡ applyUpTo g m
  applyUpTo-cong f g zero    h = refl
  applyUpTo-cong f g (suc m) h =
    cong₂ _∷_ (h 0 (s≤s z≤n))
              (applyUpTo-cong (λ p → f (suc p)) (λ p → g (suc p)) m (λ p r → h (suc p) (s≤s r)))

  applyUpTo-const : ∀ {B : Set} (b : B) m → applyUpTo (λ _ → b) m ≡ replicate m b
  applyUpTo-const b zero    = refl
  applyUpTo-const b (suc m) = cong (b ∷_) (applyUpTo-const b m)

encᶠ-[] : encᶠ [] ≡ []
encᶠ-[] = refl

encᶠ-++ : ∀ x y → encᶠ (x ++ y) ≡ encᶠ x ++ encᶠ y
encᶠ-++ x y = trans (cong (map encode) (enc-++ x y)) (map-++ encode (enc x) (enc y))

encᶠ-stretch : ∀ S τ → encᶠ (stretch S τ) ≡ replicate τ (sˢ S)
encᶠ-stretch S τ =
  trans (cong (map encode)
          (trans (cong (applyUpTo (λ p → slotOf (lab (stretch S τ) p))) (dur-stretch S τ))
          (trans (applyUpTo-cong _ (λ _ → inˢ S) τ
                    (λ p r → cong slotOf (lab-stretch S τ (ℕ.<⇒≱ r))))
                 (applyUpTo-const (inˢ S) τ))))
        (map-replicate τ)
  where
    map-replicate : ∀ m → map encode (replicate m (inˢ S)) ≡ replicate m (sˢ S)
    map-replicate zero    = refl
    map-replicate (suc m) = cong (sˢ S ∷_) (map-replicate m)

encᶠ-op : ∀ o d → encᶠ (op o d ∷ []) ≡ opWord (code o) ∣ d ∣⁺
encᶠ-op o d =
  cong (map encode)
    (trans (cong (applyUpTo (λ p → slotOf (lab (op o d ∷ []) p))) (ℕ.+-identityʳ ∣ d ∣⁺))
           (applyUpTo-cong _ _ ∣ d ∣⁺
             (λ p r → cong slotOf (lab-here {op o d} {[]} (ℕ.<⇒≱ r)))))

------------------------------------------------------------------------
-- Compiling expressions

-- the operations of a set, each at each of its running times

opsAt : Fin n → RE.Expr
opsAt c =
  ⋃< (λ j → lit (opWord c (lo# (lo (rt (name c))) + j)))
     (hiS (hi-cut (name c)) ∸ lo# (lo (rt (name c))))

guard : ∀ {P : Set} → Dec P → RE.Expr → RE.Expr
guard (yes _) e = e
guard (no _)  _ = ∅ʳ

compile : ∀ {s} → Expr s → RE.Expr
compile ε                 = RE.ε
compile (ops A)           = ⋃ˡ (allFin n) (λ c → guard (c ∈? A) (opsAt c))
compile {upper} (str S (fin c)) = ⋃< (λ t → lit (replicate t (sˢ S))) (hiS c)
compile {upper} (str S ∞)       = RE.‵ sˢ S RE.*
compile {lower} (str S c)       = lit (replicate (lo# c) (sˢ S)) RE.· (RE.‵ sˢ S RE.*)
compile (e ∣ f)           = compile e RE.∣ compile f
compile (e · f)           = compile e RE.· compile f
compile (e *)             = compile e RE.*

------------------------------------------------------------------------
-- Compiling is correct: the words of `compile e` are the encodings of
-- the exact words of `e`

private
  guard-sound : ∀ {P : Set} (d : Dec P) e {w} → RE.⟦ guard d e ⟧ w → P × RE.⟦ e ⟧ w
  guard-sound (yes p) e w∈ = p , w∈
  guard-sound (no _)  e w∈ = ⊥-elim (∅ʳ-empty w∈)

  guard-complete : ∀ {P : Set} (d : Dec P) e {w} → P → RE.⟦ e ⟧ w → RE.⟦ guard d e ⟧ w
  guard-complete (yes _) e _ w∈ = w∈
  guard-complete (no ¬p) e p _  = ⊥-elim (¬p p)

  -- the running times of an operation, as numbers

  rt-sound : ∀ o {t} → t ∈ⁱ rt o → lo# (lo (rt o)) ≤ t × t < hiS (hi-cut o)
  rt-sound o (r , r′) =
    lo#-sound (lo (rt o)) r , hiS-sound (hi-cut o) (subst (fin _ ⊑ʰ_) (hi-cut-≡ o) r′)

  rt-complete : ∀ o {t} → lo# (lo (rt o)) ≤ t → t < hiS (hi-cut o) → t ∈ⁱ rt o
  rt-complete o r r′ =
    lo#-complete (lo (rt o)) r , subst (fin _ ⊑ʰ_) (sym (hi-cut-≡ o)) (hiS-complete (hi-cut o) r′)

  -- a number below a difference, moved up

  bound : ∀ l h j → j < h ∸ l → l + j < h
  bound l h j j< with l ℕ.≤? h
  ... | yes l≤h = subst (l + j <_) (ℕ.m+[n∸m]≡n l≤h) (ℕ.+-monoʳ-< l j<)
  ... | no ¬l≤h = ⊥-elim (ℕ.n≮0 (subst (j <_) (ℕ.m≤n⇒m∸n≡0 (ℕ.<⇒≤ (ℕ.≰⇒> ¬l≤h))) j<))

  bound⁻¹ : ∀ l h t → l ≤ t → t < h → t ∸ l < h ∸ l
  bound⁻¹ l h t l≤t t<h = ℕ.∸-monoˡ-< t<h l≤t

  ops-sound : ∀ {s} A {w} → RE.⟦ compile {s} (ops A) ⟧ w → ∃ λ x → opsᴸ A x × w ≡ encᶠ x
  ops-sound A w∈ with ⋃ˡ-sound (allFin n) _ w∈
  ... | c , g with guard-sound (c ∈? A) (opsAt c) g
  ...   | c∈ , at with ⋃<-sound _ _ at
  ...     | j , j< , l =
    op o d ∷ [] ,
    (o , d , subst (_∈ A) (sym (code-name c)) c∈ , rt-complete o lo≤ t< , refl) ,
    trans (lit-sound _ l) (sym (trans (encᶠ-op o d) (cong (λ z → opWord z t) (code-name c))))
    where
      o = name c
      l₀ = lo# (lo (rt o))
      t = l₀ + j
      lo≤ : l₀ ≤ t
      lo≤ = ℕ.m≤m+n l₀ j
      t< : t < hiS (hi-cut o)
      t< = bound l₀ (hiS (hi-cut o)) j j<
      d : D⁺
      d = pos⁺ t (ℕ.<⇒≱ (ℕ.<-≤-trans (lo#-pos o) lo≤))

  ops-complete : ∀ {s} A {x} → opsᴸ A x → RE.⟦ compile {s} (ops A) ⟧ (encᶠ x)
  ops-complete A (o , d , c∈ , t∈ , refl) =
    ⋃ˡ-complete (allFin n) _ (∈-allFin (code o))
      (guard-complete (code o ∈? A) _ c∈
        (⋃<-complete _ _ (bound⁻¹ l₀ (hiS (hi-cut o′)) ∣ d ∣⁺ lo≤ t<)
          (subst (λ w → RE.⟦ lit (opWord (code o) (l₀ + (∣ d ∣⁺ ∸ l₀))) ⟧ w)
                 (sym (trans (encᶠ-op o d) (cong (opWord (code o)) (sym (ℕ.m+[n∸m]≡n lo≤)))))
                 (lit-complete _))))
    where
      o′ = name (code o)
      l₀ = lo# (lo (rt o′))
      lo≤ : l₀ ≤ ∣ d ∣⁺
      lo≤ = subst (λ z → lo# (lo (rt z)) ≤ ∣ d ∣⁺) (sym (name-code o)) (proj₁ (rt-sound o t∈))
      t< : ∣ d ∣⁺ < hiS (hi-cut o′)
      t< = subst (λ z → ∣ d ∣⁺ < hiS (hi-cut z)) (sym (name-code o)) (proj₂ (rt-sound o t∈))

  str-sound : ∀ {s} S (e : End s) {w} → RE.⟦ compile (str S e) ⟧ w → ∃ λ x → strᴸ S e x × w ≡ encᶠ x
  str-sound {upper} S (fin c) w∈ with ⋃<-sound _ (hiS c) w∈
  ... | t , t< , l = stretch S t , (t , hiS-complete c t< , refl) ,
                     trans (lit-sound _ l) (sym (encᶠ-stretch S t))
  str-sound {upper} S ∞ w∈ with star-letter-sound (sˢ S) w∈
  ... | t , refl = stretch S t , (t , _ , refl) , sym (encᶠ-stretch S t)
  str-sound {lower} S c (u , v , refl , u∈ , v∈) with star-letter-sound (sˢ S) v∈
  ... | j , refl =
    stretch S (lo# c + j) , (lo# c + j , lo#-complete c (ℕ.m≤m+n (lo# c) j) , refl) ,
    trans (cong (_++ replicate j (sˢ S)) (lit-sound _ u∈))
          (sym (trans (encᶠ-stretch S (lo# c + j)) (replicate-+ (lo# c) j (sˢ S))))

  str-complete : ∀ {s} S (e : End s) {x} → strᴸ S e x → RE.⟦ compile (str S e) ⟧ (encᶠ x)
  str-complete {upper} S (fin c) (t , a , refl) =
    ⋃<-complete _ (hiS c) (hiS-sound c a)
      (subst (λ w → RE.⟦ lit (replicate t (sˢ S)) ⟧ w) (sym (encᶠ-stretch S t)) (lit-complete _))
  str-complete {upper} S ∞ (t , _ , refl) =
    subst (λ w → RE.⟦ RE.‵ sˢ S RE.* ⟧ w) (sym (encᶠ-stretch S t)) (star-letter-complete (sˢ S) t)
  str-complete {lower} S c (t , a , refl) with ℕ.m≤n⇒∃[o]m+o≡n (lo#-sound c a)
  ... | j , refl =
    subst (λ w → RE.⟦ compile {lower} (str S c) ⟧ w)
          (sym (trans (encᶠ-stretch S (lo# c + j)) (replicate-+ (lo# c) j (sˢ S))))
          (replicate (lo# c) (sˢ S) , replicate j (sˢ S) , refl ,
           lit-complete _ , star-letter-complete (sˢ S) j)

compile-sound : ∀ {s} (e : Expr s) {w} → RE.⟦ compile e ⟧ w → ∃ λ x → ⟦ e ⟧ x × w ≡ encᶠ x
compile-sound ε       refl = [] , refl , refl
compile-sound {s} (ops A) w∈ = ops-sound {s} A w∈
compile-sound (str S e) w∈ = str-sound S e w∈
compile-sound (e ∣ f) (inj₁ w∈) with compile-sound e w∈
... | x , x∈ , eq = x , inj₁ x∈ , eq
compile-sound (e ∣ f) (inj₂ w∈) with compile-sound f w∈
... | x , x∈ , eq = x , inj₂ x∈ , eq
compile-sound (e · f) (u , v , refl , u∈ , v∈) with compile-sound e u∈ | compile-sound f v∈
... | x , x∈ , refl | y , y∈ , refl = x ++ y , (x , y , refl , x∈ , y∈) , sym (encᶠ-++ x y)
compile-sound (e *) w∈ = star w∈
  where
    star : ∀ {w} → RE.Star RE.⟦ compile e ⟧ w → ∃ λ x → ⟦ e * ⟧ x × w ≡ encᶠ x
    star (RE.none refl) = [] , stop , refl
    star (RE.more u v refl u∈ vs) with compile-sound e u∈ | star vs
    ... | x , x∈ , refl | y , y∈ , refl = x ++ y , more x∈ y∈ , sym (encᶠ-++ x y)

compile-complete : ∀ {s} (e : Expr s) {x} → ⟦ e ⟧ x → RE.⟦ compile e ⟧ (encᶠ x)
compile-complete ε         refl = refl
compile-complete {s} (ops A) x∈ = ops-complete {s} A x∈
compile-complete (str S e) x∈   = str-complete S e x∈
compile-complete (e ∣ f)   (inj₁ x∈) = inj₁ (compile-complete e x∈)
compile-complete (e ∣ f)   (inj₂ x∈) = inj₂ (compile-complete f x∈)
compile-complete (e · f)   (x , y , refl , x∈ , y∈) =
  encᶠ x , encᶠ y , encᶠ-++ x y , compile-complete e x∈ , compile-complete f y∈
compile-complete (e *)     stop = RE.none refl
compile-complete (e *)     (more {x} {y} x∈ ys) =
  RE.more (encᶠ x) (encᶠ y) (encᶠ-++ x y) (compile-complete e x∈) (compile-complete (e *) ys)

------------------------------------------------------------------------
-- Literals

open import Syntax.Grades.Regular.Grade k tick using () renaming (⊆⇒≾ to ⊆⇒≾ᴿ; ≾⇒⊆ to ≾⇒⊆ᴿ)
open import Syntax.Grades.Regular.Decide k using (nonempty?)
open import Relation.Nullary.Decidable using (True)

-- letters below the encoding of a word

Belowᶠ : List (Fin k) → List (Fin k) → Set
Belowᶠ = Belowᴿ _≤ᶠ_

private
  below-encᶠ : ∀ {x y} → Belowᶠ (encᶠ x) (encᶠ y) ⇔ Below (enc x) (enc y)
  below-encᶠ {x} {y} = mk⇔ (to′ (enc x) (enc y)) (from′ (enc x) (enc y))
    where
      to′ : ∀ xs ys → Belowᶠ (map encode xs) (map encode ys) → Below xs ys
      to′ []       []       []       = []
      to′ (s ∷ xs) (t ∷ ys) (r ∷ rs) =
        subst₂ (λ a b → T (a ≤ˢ b)) (decode-encode s) (decode-encode t) r ∷ to′ xs ys rs
      from′ : ∀ xs ys → Below xs ys → Belowᶠ (map encode xs) (map encode ys)
      from′ []       []       []       = []
      from′ (s ∷ xs) (t ∷ ys) (r ∷ rs) =
        subst₂ (λ a b → T (a ≤ˢ b)) (sym (decode-encode s)) (sym (decode-encode t)) r ∷ from′ xs ys rs

  belowᶠ-refl : ∀ w → Belowᶠ w w
  belowᶠ-refl []      = []
  belowᶠ-refl (a ∷ w) = ≤ᶠ-refl a ∷ belowᶠ-refl w

  belowᶠ-trans : ∀ {u v w} → Belowᶠ u v → Belowᶠ v w → Belowᶠ u w
  belowᶠ-trans []       []       = []
  belowᶠ-trans (r ∷ rs) (s ∷ ss) = ≤ᶠ-trans _ _ _ r s ∷ belowᶠ-trans rs ss

-- the fit order, on letters

⊑⇔belowᶠ : ∀ {x y} → x ⊑ y ⇔ Belowᶠ (encᶠ x) (encᶠ y)
⊑⇔belowᶠ {x} {y} = mk⇔ (λ r → from (below-encᶠ {x} {y}) (to (⊑⇔enc {x} {y}) r)) (λ b → from (⊑⇔enc {x} {y}) (to (below-encᶠ {x} {y}) b))

-- the table of an expression

table-of : ∀ {s} → Expr s → A.DFA
table-of e = RE.elab (compile e)

table-of-wf : ∀ {s} (e : Expr s) → A.WellFormed (table-of e)
table-of-wf e = RE.elab-wf (compile e)

∈-table-of⁺ : ∀ {s} (e : Expr s) {x} → ⟦ e ⟧ x → encᶠ x A.∈ table-of e
∈-table-of⁺ e x∈ = from (RE.elab-correct (compile e) _) (compile-complete e x∈)

∈-table-of⁻ : ∀ {s} (e : Expr s) {w} → w A.∈ table-of e → ∃ λ x → ⟦ e ⟧ x × w ≡ encᶠ x
∈-table-of⁻ e w∈ = compile-sound e (to (RE.elab-correct (compile e) _) w∈)

-- the literal of an expression, its non-emptiness found by computation

⌜_⌝ : ∀ {s} (e : Expr s)
    → {ne : True (nonempty? (↓ _≤ᶠ_ (table-of e)) (↓-wf _≤ᶠ_ {table-of e} (table-of-wf e)))} → Closed
⌜ e ⌝ {ne} = C.⌜ table-of e ⌝ {table-of-wf e} {ne}

-- the literal of an expression with a word shown

⌜_⌝′ : ∀ {s} (e : Expr s) → ∃ ⟦ e ⟧ → Closed
⌜ e ⌝′ (x , x∈) = C.⌜ table-of e ⌝′ (table-of-wf e) (encᶠ x , ∈-table-of⁺ e x∈)

-- what a literal holds: the letter words below the encoding of a word
-- of the expression

Holds : ∀ {s} → Expr s → List (Fin k) → Set
Holds e w = ∃ λ x → ⟦ e ⟧ x × Belowᶠ w (encᶠ x)

private
  holds⁻ : ∀ {s} (e : Expr s) {w} → (∃ λ v → Belowᶠ w v × v A.∈ table-of e) → Holds e w
  holds⁻ e {w} (v , wv , v∈) with ∈-table-of⁻ e v∈
  ... | x , x∈ , eq = x , x∈ , subst (Belowᶠ w) eq wv

∈-⌜⌝⁻ : ∀ {s} (e : Expr s) {ne} w → w A.∈ C.table (lang (⌜ e ⌝ {ne})) → Holds e w
∈-⌜⌝⁻ e {ne} w w∈ = holds⁻ e (C.∈-⌜⌝ (table-of e) {table-of-wf e} {ne} w w∈)

∈-⌜⌝⁺ : ∀ {s} (e : Expr s) {ne} w → Holds e w → w A.∈ C.table (lang (⌜ e ⌝ {ne}))
∈-⌜⌝⁺ e {ne} w (x , x∈ , wx) = C.∈-⌜⌝⁺ (table-of e) {table-of-wf e} {ne} w (encᶠ x) wx (∈-table-of⁺ e x∈)

∈-⌜⌝′⁻ : ∀ {s} (e : Expr s) {i} w → w A.∈ C.table (lang (⌜ e ⌝′ i)) → Holds e w
∈-⌜⌝′⁻ e {x , x∈} w w∈ =
  holds⁻ e (C.∈-⌜⌝′ (table-of e) {table-of-wf e} {encᶠ x , ∈-table-of⁺ e x∈} w w∈)

∈-⌜⌝′⁺ : ∀ {s} (e : Expr s) {i} w → Holds e w → w A.∈ C.table (lang (⌜ e ⌝′ i))
∈-⌜⌝′⁺ e {x₀ , x₀∈} w (x , x∈ , wx) =
  C.∈-⌜⌝′⁺ (table-of e) {table-of-wf e} {encᶠ x₀ , ∈-table-of⁺ e x₀∈} w (encᶠ x) wx (∈-table-of⁺ e x∈)

------------------------------------------------------------------------
-- Literals compare as their sets of exact words

-- through what they hold

holds-≾ : ∀ {s s′} (e : Expr s) (f : Expr s′) → ⟦ e ⟧ ≾ ⟦ f ⟧ → ∀ w → Holds e w → Holds f w
holds-≾ e f le w (x , x∈ , wx) with le x x∈
... | y , y∈ , xy = y , y∈ , belowᶠ-trans wx (to (⊑⇔belowᶠ {x} {y}) xy)

≾-holds : ∀ {s s′} (e : Expr s) (f : Expr s′) → (∀ w → Holds e w → Holds f w) → ⟦ e ⟧ ≾ ⟦ f ⟧
≾-holds e f h x x∈ with h (encᶠ x) (x , x∈ , belowᶠ-refl (encᶠ x))
... | y , y∈ , xy = y , y∈ , from (⊑⇔belowᶠ {x} {y}) xy

⌜⌝-≾ : ∀ {s s′} (e : Expr s) (f : Expr s′) {ne ne′}
     → C._≾_ (⌜ e ⌝ {ne}) (⌜ f ⌝ {ne′}) ⇔ ⟦ e ⟧ ≾ ⟦ f ⟧
⌜⌝-≾ e f {ne} {ne′} =
  mk⇔ (λ le → ≾-holds e f λ w h →
          ∈-⌜⌝⁻ f {ne′} w (≾⇒⊆ᴿ (lang (⌜ e ⌝ {ne})) (lang (⌜ f ⌝ {ne′})) le w (∈-⌜⌝⁺ e {ne} w h)))
      (λ le → ⊆⇒≾ᴿ (lang (⌜ e ⌝ {ne})) (lang (⌜ f ⌝ {ne′})) λ w w∈ →
          ∈-⌜⌝⁺ f {ne′} w (holds-≾ e f le w (∈-⌜⌝⁻ e {ne} w w∈)))

------------------------------------------------------------------------
-- Delays of one step, at most and at least

-- the upper bound of a step: a strict wait of at most one

wait≤1 : Closed
wait≤1 = ⌜ str {upper} Data.Fin.Subset.⊥ (fin (1 ∣ᶜ ⁺)) ⌝′ ([] , 0 , ≤⇒⁺⊑⁺ z≤n , refl)

-- the lower bound of a step: a strict wait of at least one

wait≥1 : Closed
wait≥1 = ⌜ str {lower} Data.Fin.Subset.⊥ (1 ∣ᶜ ⁻) ⌝′ (_ , 1 , ≤⇒⁻⊑⁻ ℕ.≤-refl , refl)

-- `m` steps, as the product of `m` one-step delays

steps : Closed → ℕ → Closed
steps w zero    = C.u
steps w (suc m) = w C.· steps w m

steps-zero : ∀ w → steps w 0 ≡ C.u
steps-zero w = refl

steps-plus : ∀ w {m n} → steps w (m + n) ≡ steps w m C.· steps w n
steps-plus w {zero}  {n} = sym (C.·-identityˡ (steps w n))
steps-plus w {suc m} {n} =
  trans (cong (w C.·_) (steps-plus w {m} {n})) (sym (C.·-assoc w (steps w m) (steps w n)))
