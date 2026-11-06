------------------------------------------------------------------------
-- Stretches split and joined, for the non-rigid translations.        --
--                                                                    --
-- A stretch of length `a + b` fits the stretch of length `a` then    --
-- the one of length `b`, with the same set, and conversely; a word   --
-- fits the stretch of its duration admitting every operation. Upper  --
-- stretches of one set add: at most `m + n` is at most `m` then at   --
-- most `n`.                                                          --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.NonRigid.Base
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Fin.Subset using () renaming (⊤ to all)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Properties using (++-assoc)
open import Relation.Nullary using (yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Hi; fin; ⁺; ⁻; ⊑⇒≤; ≤⇒⁺⊑⁺; ≤⇒⁻⊑⁻; _⊑ʰ_)
  renaming (_∣_ to _∣ᶜ_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective using (_⊑_; lab-∙; ⊑-trans; ⊑-refl)
open import Grades.Exact.Lift T Op n code code-injective
  using (_·ᴸ_; ≡ˡ⇒⊑; ⊑-all; ⊑-++)
  renaming (_≈_ to _≈ᴸ_; _≾_ to _≾ᴸ_)
open import Grades.Exact.Expression T Op n code code-injective running
  using (upper; strᴸ)

------------------------------------------------------------------------
-- Splitting and joining

stretch-0 : ∀ S → stretch S 0ᴰ ≡ []
stretch-0 S = stretch-zero S 0ᴰ (λ q → <⇒≢ q refl)

private
  ∙⊑++ : ∀ x y → x ∙ y ⊑ x ++ y
  ∙⊑++ x y = ≡ˡ⇒⊑ (trans (dur-∙ x y) (sym (dur-++ x y))) (λ p _ → lab-∙ x y p)

  ++⊑∙ : ∀ x y → x ++ y ⊑ x ∙ y
  ++⊑∙ x y = ≡ˡ⇒⊑ (trans (dur-++ x y) (sym (dur-∙ x y))) (λ p _ → sym (lab-∙ x y p))

split⊑ : ∀ S a b → stretch S (a +ᴰ b) ⊑ stretch S a ++ stretch S b
split⊑ S a b =
  subst (_⊑ stretch S a ++ stretch S b) (sym (stretch-hom S a b)) (∙⊑++ (stretch S a) (stretch S b))

join⊑ : ∀ S a b → stretch S a ++ stretch S b ⊑ stretch S (a +ᴰ b)
join⊑ S a b =
  subst (stretch S a ++ stretch S b ⊑_) (sym (stretch-hom S a b)) (++⊑∙ (stretch S a) (stretch S b))

-- a stretch of no length in front changes nothing

pad0 : ∀ {x y} S → x ⊑ y → x ⊑ stretch S 0ᴰ ++ y
pad0 {x} {y} S p = subst (λ z → x ⊑ z ++ y) (sym (stretch-0 S)) p

unpad : ∀ {x y a} S → a ≡ 0ᴰ → x ⊑ stretch S a ++ y → x ⊑ y
unpad {x} {y} S refl p = subst (λ z → x ⊑ z ++ y) (stretch-0 S) p

-- a word fits the unrestricted stretch of its duration

⊑-all′ : ∀ x {τ} → dur x ≡ τ → x ⊑ stretch all τ
⊑-all′ x refl = ⊑-all x

-- two stretches in front join into one

join-front : ∀ {x y} S a b → x ⊑ stretch S a ++ (stretch S b ++ y) → x ⊑ stretch S (a +ᴰ b) ++ y
join-front {x} {y} S a b p =
  ⊑-trans (subst (x ⊑_) (sym (++-assoc (stretch S a) (stretch S b) y)) p)
          (⊑-++ (join⊑ S a b) ⊑-refl)

split-front : ∀ {x y} S a b → x ⊑ stretch S (a +ᴰ b) ++ y → x ⊑ stretch S a ++ (stretch S b ++ y)
split-front {x} {y} S a b p =
  subst (x ⊑_) (++-assoc (stretch S a) (stretch S b) y)
        (⊑-trans p (⊑-++ (split⊑ S a b) ⊑-refl))

------------------------------------------------------------------------
-- Upper stretches of one set add

span-split : ∀ S m n → strᴸ {upper} S (fin ((m +ᴰ n) ∣ᶜ ⁺))
                         ≈ᴸ (strᴸ {upper} S (fin (m ∣ᶜ ⁺)) ·ᴸ strᴸ {upper} S (fin (n ∣ᶜ ⁺)))
span-split S m n = to , from
  where
    parts : ∀ τ → τ ≤ᴰ m +ᴰ n → Σ[ a ∈ Carrier ] Σ[ b ∈ Carrier ] a ≤ᴰ m × b ≤ᴰ n × a +ᴰ b ≡ τ
    parts τ r with τ ≤ᴰ? m
    ... | yes τm = τ , 0ᴰ , τm , 0ᴰ-least n , +ᴰ-identityʳ τ
    ... | no ¬τm = m , τ ∸ᴰ m , ≤ᴰ-refl , ∸-≤-+ r , +-∸ (<⇒≤ ¬τm)
    to : strᴸ S (fin ((m +ᴰ n) ∣ᶜ ⁺)) ≾ᴸ (strᴸ S (fin (m ∣ᶜ ⁺)) ·ᴸ strᴸ S (fin (n ∣ᶜ ⁺)))
    to x (τ , r , refl) with parts τ (⊑⇒≤ r)
    ... | a , b , am , bn , e =
      stretch S a ++ stretch S b ,
      (stretch S a , stretch S b , refl , (a , ≤⇒⁺⊑⁺ am , refl) , (b , ≤⇒⁺⊑⁺ bn , refl)) ,
      subst (λ z → stretch S z ⊑ stretch S a ++ stretch S b) e (split⊑ S a b)
    from : (strᴸ S (fin (m ∣ᶜ ⁺)) ·ᴸ strᴸ S (fin (n ∣ᶜ ⁺))) ≾ᴸ strᴸ S (fin ((m +ᴰ n) ∣ᶜ ⁺))
    from x (_ , _ , refl , (a , ra , refl) , (b , rb , refl)) =
      stretch S (a +ᴰ b) , (a +ᴰ b , ≤⇒⁺⊑⁺ (+ᴰ-mono-≤ (⊑⇒≤ ra) (⊑⇒≤ rb)) , refl) , join⊑ S a b
