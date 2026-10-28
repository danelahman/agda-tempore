------------------------------------------------------------------------
-- Where the items of a fit lie in time.                              --
--                                                                    --
-- An item of the lesser word and a piece of the greater that share   --
-- an instant are compatible: a stretch of the greater word admits    --
-- the item, and an operation of the greater word is the item itself, --
-- starting where it starts.                                          --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Positions
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective using (lab-stretch)
open import Grades.Exact.Letters T Op n code code-injective running

private
  variable
    a b p q : Carrier

  ≮⇒≥ : ¬ (p <ᴰ a) → a ≤ᴰ p
  ≮⇒≥ {p} {a} ¬p with a ≤ᴰ? p
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

  ≮-+ : ¬ (a +ᴰ q <ᴰ a)
  ≮-+ {a} {q} s = s (≤ᴰ-+ a q)

------------------------------------------------------------------------
-- Durations

dur-wordOf : ∀ {ps y} → WordOf ps y → dur y ≡ sumᴰ (amts ps)
dur-wordOf [] = refl
dur-wordOf (op r w) = cong (_ +ᴰ_) (dur-wordOf w)
dur-wordOf (st {S} {τ} {ps} {x} w) =
  trans (dur-++ (stretch S τ) x) (cong₂ _+ᴰ_ (dur-stretch S τ) (dur-wordOf w))

sumᴰ-++ : ∀ xs ys → sumᴰ (xs ++ ys) ≡ sumᴰ xs +ᴰ sumᴰ ys
sumᴰ-++ []       ys = sym (+ᴰ-identityˡ _)
sumᴰ-++ (x ∷ xs) ys = trans (cong (x +ᴰ_) (sumᴰ-++ xs ys)) (sym (+ᴰ-assoc x _ _))

amts-++ : ∀ xs ys → amts (xs ++ ys) ≡ amts xs ++ amts ys
amts-++ []       ys = refl
amts-++ (x ∷ xs) ys = cong (_ ∷_) (amts-++ xs ys)

------------------------------------------------------------------------
-- Labels inside an item of a word

lab-++ʳ′ : ∀ x y q → lab (x ++ y) (dur x +ᴰ q) ≡ lab y q
lab-++ʳ′ x y q = trans (lab-++ʳ x y ≮-+) (cong (lab y) (m+n∸m (dur x) q))

lab-item : ∀ xd i xr {q} → q <ᴰ len i → lab (xd ++ i ∷ xr) (dur xd +ᴰ q) ≡ labᵢ i q
lab-item xd i xr r = trans (lab-++ʳ′ xd (i ∷ xr) _) (lab-here {i} {xr} r)

-- the labels of the piece of a word from its pieces

data At (y : Word) (σ : Carrier) : Piece Carrier → Set where
  at-st : ∀ {S τ} → (∀ {q} → q <ᴰ τ → lab y (σ +ᴰ q) ≡ bud S) → At y σ (stk S , τ)
  at-op : ∀ {o} d → (∀ {q} → q <ᴰ ∣ d ∣⁺ → lab y (σ +ᴰ q) ≡ opl o q d) → At y σ (opk o , ∣ d ∣⁺)

at : ∀ psd {pm psr y} → WordOf (psd ++ pm ∷ psr) y → At y (sumᴰ (amts psd)) pm
at [] {pm} {psr} {y} (op {o} {d} {_} {x} r w) =
  at-op d (λ {q} s → trans (cong (lab (op o d ∷ x)) (+ᴰ-identityˡ q)) (lab-here {op o d} {x} s))
at [] {psr = psr} (st {S} {τ} {_} {x} w) =
  at-st (λ {q} s → trans (cong (lab (stretch S τ ++ x)) (+ᴰ-identityˡ q))
                         (trans (lab-++ˡ (stretch S τ) x (subst (q <ᴰ_) (sym (dur-stretch S τ)) s))
                                (lab-stretch S τ s)))
at (p ∷ psd) (op {o} {d} {_} {x} r w) with at psd w
... | at-st h = at-st (λ {q} s → trans (cong (lab (op o d ∷ x)) (+ᴰ-assoc ∣ d ∣⁺ _ q))
                                   (trans (lab-skip (op o d) x _) (h s)))
... | at-op e h = at-op e (λ {q} s → trans (cong (lab (op o d ∷ x)) (+ᴰ-assoc ∣ d ∣⁺ _ q))
                                       (trans (lab-skip (op o d) x _) (h s)))
at (p ∷ psd) (st {S} {τ} {_} {x} w) with at psd w
... | at-st h = at-st (λ {q} s → trans (cong (lab (stretch S τ ++ x)) (+ᴰ-assoc τ _ q)) (shift (h s)))
  where
    shift : ∀ {r ℓ} → lab x r ≡ ℓ → lab (stretch S τ ++ x) (τ +ᴰ r) ≡ ℓ
    shift {r} e = trans (cong (λ z → lab (stretch S τ ++ x) (z +ᴰ r)) (sym (dur-stretch S τ)))
                        (trans (lab-++ʳ′ (stretch S τ) x r) e)
... | at-op e h = at-op e (λ {q} s → trans (cong (lab (stretch S τ ++ x)) (+ᴰ-assoc τ _ q)) (shift (h s)))
  where
    shift : ∀ {r ℓ} → lab x r ≡ ℓ → lab (stretch S τ ++ x) (τ +ᴰ r) ≡ ℓ
    shift {r} e′ = trans (cong (λ z → lab (stretch S τ ++ x) (z +ᴰ r)) (sym (dur-stretch S τ)))
                         (trans (lab-++ʳ′ (stretch S τ) x r) e′)

------------------------------------------------------------------------
-- An item and a piece sharing an instant

compat-st : ∀ {x y} → x ⊑ y → ∀ xd i xr → x ≡ xd ++ i ∷ xr
          → ∀ {σ S τ} → At y σ (stk S , τ) → ∀ q₁ q₂ → dur xd +ᴰ q₁ ≡ σ +ᴰ q₂
          → q₁ <ᴰ len i → q₂ <ᴰ τ → σ +ᴰ q₂ <ᴰ dur y → AdmK (kind i) S
compat-st (fits _ h) xd i xr refl {σ} {S} (at-st hy) q₁ q₂ e r₁ r₂ r =
  go i (subst₂ _≤ˡ_ (trans (cong (lab (xd ++ i ∷ xr)) (sym e)) (lab-item xd i xr r₁)) (hy r₂)
                    (h (σ +ᴰ q₂) r))
  where
    go : ∀ i → labᵢ i q₁ ≤ˡ bud S → AdmK (kind i) S
    go (op o d) (opl≤bud a) = a
    go (st d S′) (bud≤bud a) = a

compat-op : ∀ {x y} → x ⊑ y → ∀ xd i xr → x ≡ xd ++ i ∷ xr
          → ∀ {σ o τ} → At y σ (opk o , τ) → ∀ q₁ q₂ → dur xd +ᴰ q₁ ≡ σ +ᴰ q₂
          → q₁ <ᴰ len i → q₂ <ᴰ τ → σ +ᴰ q₂ <ᴰ dur y
          → Σ[ d ∈ D⁺ ] i ≡ op o d × ∣ d ∣⁺ ≡ τ × dur xd ≡ σ
compat-op (fits _ h) xd i xr refl {σ} {o} (at-op d hy) q₁ q₂ e r₁ r₂ r =
  go i (subst₂ _≤ˡ_ (trans (cong (lab (xd ++ i ∷ xr)) (sym e)) (lab-item xd i xr r₁)) (hy r₂)
                    (h (σ +ᴰ q₂) r))
  where
    go : ∀ i → labᵢ i q₁ ≤ˡ opl o q₂ d → Σ[ d′ ∈ D⁺ ] i ≡ op o d′ × ∣ d′ ∣⁺ ≡ ∣ d ∣⁺ × dur xd ≡ σ
    go (op .o .d) opl≤opl = d , refl , refl , +ᴰ-cancelʳ q₁ (trans e (cong (_+ᴰ_ σ) refl))
