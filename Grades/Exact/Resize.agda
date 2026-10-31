-------------------------------------------------------------------------
-- Shortening and lengthening the stretches of a word.                 --
--                                                                     --
-- `Shrinks w w′`: `w′` is `w` with some stretches shortened, possibly --
-- to nothing, and its operations untouched. `Lengthens w w′`: `w′`    --
-- is `w` with some stretches lengthened. The words of an upper        --
-- expression are closed under shrinking, those of a lower expression  --
-- under lengthening: a stretch letter admits every shorter length in  --
-- the first case and every longer one in the second.                  --
-------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Resize
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; Hi; fin; ∞; _⊑_; _⊑ʰ_; ⁻; ⁺; ⊑-trans; ⊑ʰ-trans; ≤⇒⁻⊑⁻; ≤⇒⁺⊑⁺)
  renaming (_∣_ to _∣ᶜ_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective
open import Grades.Exact.Expression T Op n code code-injective running

------------------------------------------------------------------------
-- The relations

data Shrinks : Word → Word → Set where
  []  : Shrinks [] []
  op  : ∀ {o d w w′} → Shrinks w w′ → Shrinks (op o d ∷ w) (op o d ∷ w′)
  st  : ∀ {d S τ w w′} → τ ≤ᴰ ∣ d ∣⁺ → Shrinks w w′
      → Shrinks (st d S ∷ w) (stretch S τ ++ w′)

data Lengthens : Word → Word → Set where
  []  : Lengthens [] []
  op  : ∀ {o d w w′} → Lengthens w w′ → Lengthens (op o d ∷ w) (op o d ∷ w′)
  st  : ∀ {d d′ S w w′} → ∣ d ∣⁺ ≤ᴰ ∣ d′ ∣⁺ → Lengthens w w′
      → Lengthens (st d S ∷ w) (st d′ S ∷ w′)

-- a positive stretch is the stretch of its length

stretch-∣∣ : ∀ S d → stretch S ∣ d ∣⁺ ≡ st d S ∷ []
stretch-∣∣ S d = trans (stretch-pos S ∣ d ∣⁺ (∣∣⁺-pos d)) (cong (λ z → st z S ∷ []) (∣∣⁺-inj refl))

Shrinks-refl : ∀ w → Shrinks w w
Shrinks-refl []           = []
Shrinks-refl (op o d ∷ w) = op (Shrinks-refl w)
Shrinks-refl (st d S ∷ w) =
  subst (Shrinks (st d S ∷ w)) (cong (_++ w) (stretch-∣∣ S d)) (st ≤ᴰ-refl (Shrinks-refl w))

Lengthens-refl : ∀ w → Lengthens w w
Lengthens-refl []           = []
Lengthens-refl (op o d ∷ w) = op (Lengthens-refl w)
Lengthens-refl (st d S ∷ w) = st ≤ᴰ-refl (Lengthens-refl w)

-- both split along a concatenation

Shrinks-++ : ∀ x {y z} → Shrinks (x ++ y) z
           → Σ[ x′ ∈ Word ] Σ[ y′ ∈ Word ] z ≡ x′ ++ y′ × Shrinks x x′ × Shrinks y y′
Shrinks-++ []           s          = [] , _ , refl , [] , s
Shrinks-++ (op o d ∷ x) (op s) with Shrinks-++ x s
... | x′ , y′ , refl , sx , sy = op o d ∷ x′ , y′ , refl , op sx , sy
Shrinks-++ (st d S ∷ x) (st {τ = τ} r s) with Shrinks-++ x s
... | x′ , y′ , refl , sx , sy =
  stretch S τ ++ x′ , y′ , sym (++-assoc (stretch S τ) x′ y′) , st r sx , sy

Lengthens-++ : ∀ x {y z} → Lengthens (x ++ y) z
             → Σ[ x′ ∈ Word ] Σ[ y′ ∈ Word ] z ≡ x′ ++ y′ × Lengthens x x′ × Lengthens y y′
Lengthens-++ []           s          = [] , _ , refl , [] , s
Lengthens-++ (op o d ∷ x) (op s) with Lengthens-++ x s
... | x′ , y′ , refl , sx , sy = op o d ∷ x′ , y′ , refl , op sx , sy
Lengthens-++ (st d S ∷ x) (st {d′ = d′} r s) with Lengthens-++ x s
... | x′ , y′ , refl , sx , sy = st d′ S ∷ x′ , y′ , refl , st r sx , sy

------------------------------------------------------------------------
-- Closure of the languages

private
  ≮⇒≥ : ∀ {p d} → ¬ (p <ᴰ d) → d ≤ᴰ p
  ≮⇒≥ {p} {d} ¬p with d ≤ᴰ? p
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

  -- shrinking or lengthening a single stretch

  Shrinks-stretch : ∀ S τ {z} → Shrinks (stretch S τ) z → Σ[ τ′ ∈ Carrier ] τ′ ≤ᴰ τ × z ≡ stretch S τ′
  Shrinks-stretch S τ {z} s = case (0ᴰ <ᴰ? τ) s
    where
      case : (c : Dec (0ᴰ <ᴰ τ)) → Shrinks (stretch-of S τ c) z
           → Σ[ τ′ ∈ Carrier ] τ′ ≤ᴰ τ × z ≡ stretch S τ′
      case (yes p) (st {τ = τ′} r []) = τ′ , r , ++-identityʳ (stretch S τ′)
      case (no ¬p) []                 = 0ᴰ , 0ᴰ-least τ , sym (stretch-zero S 0ᴰ (λ q → <⇒≢ q refl))

  Lengthens-stretch : ∀ S τ {z} → Lengthens (stretch S τ) z → Σ[ τ′ ∈ Carrier ] τ ≤ᴰ τ′ × z ≡ stretch S τ′
  Lengthens-stretch S τ {z} s = case (0ᴰ <ᴰ? τ) s
    where
      case : (c : Dec (0ᴰ <ᴰ τ)) → Lengthens (stretch-of S τ c) z
           → Σ[ τ′ ∈ Carrier ] τ ≤ᴰ τ′ × z ≡ stretch S τ′
      case (yes p) (st {d′ = d′} r []) = ∣ d′ ∣⁺ , r , sym (stretch-∣∣ S d′)
      case (no ¬p) []                  = τ , ≤ᴰ-refl , sym (stretch-zero S τ ¬p)

  -- a smaller length lies in an upper interval, a larger in a lower one

  admits-upper : ∀ {h : Hi} {τ τ′} → τ′ ≤ᴰ τ → τ ∈ᵉ h → τ′ ∈ᵉ h
  admits-upper {fin c} r a = ⊑-trans (≤⇒⁺⊑⁺ r) a
  admits-upper {∞}     r a = a

  admits-lower : ∀ {c : Cut} {τ τ′} → τ ≤ᴰ τ′ → τ ∈ᵉ c → τ′ ∈ᵉ c
  admits-lower r a = ⊑-trans a (≤⇒⁻⊑⁻ r)

  Shrinks-ops : ∀ A {w z} → opsᴸ A w → Shrinks w z → opsᴸ A z
  Shrinks-ops A (o , d , a , r , refl) (op []) = o , d , a , r , refl

  Lengthens-ops : ∀ A {w z} → opsᴸ A w → Lengthens w z → opsᴸ A z
  Lengthens-ops A (o , d , a , r , refl) (op []) = o , d , a , r , refl

-- the words of an upper expression are closed under shrinking

Shrinks-closed : (e : Expr upper) → ∀ {w z} → ⟦ e ⟧ w → Shrinks w z → ⟦ e ⟧ z
Shrinks-closed ε         refl []  = refl
Shrinks-closed (ops A)   w∈ s     = Shrinks-ops A w∈ s
Shrinks-closed (str S h) (τ , a , refl) s with Shrinks-stretch S τ s
... | τ′ , r , refl = τ′ , admits-upper {h} r a , refl
Shrinks-closed (e ∣ f)   (inj₁ w∈) s = inj₁ (Shrinks-closed e w∈ s)
Shrinks-closed (e ∣ f)   (inj₂ w∈) s = inj₂ (Shrinks-closed f w∈ s)
Shrinks-closed (e · f)   (x , y , refl , x∈ , y∈) s with Shrinks-++ x s
... | x′ , y′ , refl , sx , sy =
  x′ , y′ , refl , Shrinks-closed e x∈ sx , Shrinks-closed f y∈ sy
Shrinks-closed (e *)     stop      [] = stop
Shrinks-closed (e *)     (more {x} x∈ y∈) s with Shrinks-++ x s
... | x′ , y′ , refl , sx , sy = more (Shrinks-closed e x∈ sx) (Shrinks-closed (e *) y∈ sy)

-- the words of a lower expression are closed under lengthening

Lengthens-closed : (e : Expr lower) → ∀ {w z} → ⟦ e ⟧ w → Lengthens w z → ⟦ e ⟧ z
Lengthens-closed ε         refl []  = refl
Lengthens-closed (ops A)   w∈ s     = Lengthens-ops A w∈ s
Lengthens-closed (str S c) (τ , a , refl) s with Lengthens-stretch S τ s
... | τ′ , r , refl = τ′ , admits-lower {c} r a , refl
Lengthens-closed (e ∣ f)   (inj₁ w∈) s = inj₁ (Lengthens-closed e w∈ s)
Lengthens-closed (e ∣ f)   (inj₂ w∈) s = inj₂ (Lengthens-closed f w∈ s)
Lengthens-closed (e · f)   (x , y , refl , x∈ , y∈) s with Lengthens-++ x s
... | x′ , y′ , refl , sx , sy =
  x′ , y′ , refl , Lengthens-closed e x∈ sx , Lengthens-closed f y∈ sy
Lengthens-closed (e *)     stop      [] = stop
Lengthens-closed (e *)     (more {x} x∈ y∈) s with Lengthens-++ x s
... | x′ , y′ , refl , sx , sy = more (Lengthens-closed e x∈ sx) (Lengthens-closed (e *) y∈ sy)
