------------------------------------------------------------------------
-- The hull of a run is invisible against one-sided bounds.           --
--                                                                    --
-- A run is a sequence of operations and delays. It denotes the exact --
-- words in which each operation runs for a time its running-time     --
-- interval admits and each delay is an idle wait of exactly its      --
-- length. A one-sided instance reads the run by its hull on its      --
-- side: a delay `d` becomes an idle wait of at most `d` (upper), or  --
-- of at least `d` (lower; no delay stays nothing). The run lies      --
-- within its hull, and against an expression of the same side the    --
-- two are compared alike:                                            --
--                                                                    --
--   run r ≾ ⟦ U ⟧   iff   ⟦ hullᵁ r ⟧ ≾ ⟦ U ⟧                        --
--   run r ≾ ⟦ L ⟧   iff   ⟦ hullᴸ r ⟧ ≾ ⟦ L ⟧                        --
--                                                                    --
-- The proof shortens (lengthens) the waits of the run one at a time, --
-- removing (inserting) the same time in the word it fits, which      --
-- stays among the words of the expression.                           --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Hull
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Subset using (⁅_⁆) renaming (⊥ to none)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T using (fin; ⊑⇒≤; ⁻; ⁺)
  renaming (_∣_ to _∣ᶜ_; ⊑-refl to ⊑ᶜ-refl)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective
open import Grades.Exact.Expression T Op n code code-injective running
open import Grades.Exact.Resize T Op n code code-injective running
open import Grades.Exact.Splice T Op n code code-injective running

------------------------------------------------------------------------
-- Runs

data Event : Set where
  perform : Op → Event
  delay   : Carrier → Event

Run : Set
Run = List Event

runᴸ : Run → Lang
runᴸ []              = 𝟏ᴸ
runᴸ (perform o ∷ r) = opsᴸ ⁅ code o ⁆ ·ᴸ runᴸ r
runᴸ (delay τ ∷ r)   = ιᴸ τ ·ᴸ runᴸ r

-- the hulls

hullᵁ : Run → Expr upper
hullᵁ []              = ε
hullᵁ (perform o ∷ r) = ‵ o · hullᵁ r
hullᵁ (delay τ ∷ r)   = str none (fin (τ ∣ᶜ ⁺)) · hullᵁ r

-- at least a delay; no delay is nothing

at-least : (τ : Carrier) → Dec (0ᴰ <ᴰ τ) → Expr lower
at-least τ (yes _) = str none (τ ∣ᶜ ⁻)
at-least τ (no _)  = ε

hullᴸ : Run → Expr lower
hullᴸ []              = ε
hullᴸ (perform o ∷ r) = ‵ o · hullᴸ r
hullᴸ (delay τ ∷ r)   = at-least τ (0ᴰ <ᴰ? τ) · hullᴸ r

------------------------------------------------------------------------
-- A run lies within its hulls

run⊆hullᵁ : ∀ r → runᴸ r ⊆ᴸ ⟦ hullᵁ r ⟧
run⊆hullᵁ []              w w∈ = w∈
run⊆hullᵁ (perform o ∷ r) w (x , y , e , x∈ , y∈) = x , y , e , x∈ , run⊆hullᵁ r y y∈
run⊆hullᵁ (delay τ ∷ r)   w (x , y , e , refl , y∈) =
  x , y , e , (τ , ⊑ᶜ-refl , refl) , run⊆hullᵁ r y y∈

run⊆hullᴸ : ∀ r → runᴸ r ⊆ᴸ ⟦ hullᴸ r ⟧
run⊆hullᴸ []              w w∈ = w∈
run⊆hullᴸ (perform o ∷ r) w (x , y , e , x∈ , y∈) = x , y , e , x∈ , run⊆hullᴸ r y y∈
run⊆hullᴸ (delay τ ∷ r)   w (x , y , e , refl , y∈) =
  x , y , e , wait (0ᴰ <ᴰ? τ) , run⊆hullᴸ r y y∈
  where
    wait : (c : Dec (0ᴰ <ᴰ τ)) → ⟦ at-least τ c ⟧ (idle τ)
    wait (yes _) = τ , ⊑ᶜ-refl , refl
    wait (no ¬p) = stretch-zero none τ ¬p

------------------------------------------------------------------------
-- A word of a hull is a word of the run, resized

private
  -- the stretch of no length is nothing

  stretch-≤0 : ∀ S {τ} → τ ≤ᴰ 0ᴰ → stretch S τ ≡ []
  stretch-≤0 S {τ} r = stretch-zero S τ (λ p → p r)

  shrink-stretch : ∀ S {τ τ′ w w′} → τ′ ≤ᴰ τ → Shrinks w w′
                 → Shrinks (stretch S τ ++ w) (stretch S τ′ ++ w′)
  shrink-stretch S {τ} {τ′} {w} {w′} r s = case (0ᴰ <ᴰ? τ)
    where
      case : (c : Dec (0ᴰ <ᴰ τ)) → Shrinks (stretch-of S τ c ++ w) (stretch S τ′ ++ w′)
      case (yes p) = st r s
      case (no ¬p) =
        subst (λ z → Shrinks w (z ++ w′)) (sym (stretch-≤0 S (≤ᴰ-trans r (≤ᴰ-reflexive (≮0⇒≡0 ¬p))))) s

  lengthen-stretch : ∀ S {τ τ′ w w′} → 0ᴰ <ᴰ τ → τ ≤ᴰ τ′ → Lengthens w w′
                   → Lengthens (stretch S τ ++ w) (stretch S τ′ ++ w′)
  lengthen-stretch S {τ} {τ′} p r s =
    subst₂ (λ a b → Lengthens (a ++ _) (b ++ _))
           (sym (stretch-pos S τ p)) (sym (stretch-pos S τ′ (<-≤-trans p r)))
           (st r s)

hullᵁ-shrinks : ∀ r {h} → ⟦ hullᵁ r ⟧ h → Σ[ x ∈ Word ] runᴸ r x × Shrinks x h
hullᵁ-shrinks []              refl = [] , refl , []
hullᵁ-shrinks (perform o ∷ r) (_ , y , refl , (o′ , d , a , rt , refl) , y∈)
  with hullᵁ-shrinks r y∈
... | x , x∈ , s = op o′ d ∷ x , (op o′ d ∷ [] , x , refl , (o′ , d , a , rt , refl) , x∈) , op s
hullᵁ-shrinks (delay τ ∷ r)   (_ , y , refl , (τ′ , a , refl) , y∈)
  with hullᵁ-shrinks r y∈
... | x , x∈ , s = idle τ ++ x , (idle τ , x , refl , refl , x∈) , shrink-stretch none (⊑⇒≤ a) s

hullᴸ-lengthens : ∀ r {h} → ⟦ hullᴸ r ⟧ h → Σ[ x ∈ Word ] runᴸ r x × Lengthens x h
hullᴸ-lengthens []              refl = [] , refl , []
hullᴸ-lengthens (perform o ∷ r) (_ , y , refl , (o′ , d , a , rt , refl) , y∈)
  with hullᴸ-lengthens r y∈
... | x , x∈ , s = op o′ d ∷ x , (op o′ d ∷ [] , x , refl , (o′ , d , a , rt , refl) , x∈) , op s
hullᴸ-lengthens (delay τ ∷ r) {h} (h₁ , y , refl , h₁∈ , y∈) with hullᴸ-lengthens r y∈
... | x , x∈ , s = case (0ᴰ <ᴰ? τ) h₁∈
  where
    case : (c : Dec (0ᴰ <ᴰ τ)) → ⟦ at-least τ c ⟧ h₁
         → Σ[ x′ ∈ Word ] runᴸ (delay τ ∷ r) x′ × Lengthens x′ (h₁ ++ y)
    case (yes p) (τ′ , a , refl) =
      idle τ ++ x , (idle τ , x , refl , refl , x∈) , lengthen-stretch none p (⊑⇒≤ a) s
    case (no ¬p) refl =
      x , ([] , x , refl , sym (stretch-zero none τ ¬p) , x∈) , s

------------------------------------------------------------------------
-- The hulls are invisible

-- against any set closed under shrinking, and an upper expression

hullᵁ-invisible : ∀ r (Y : Lang) → (∀ {y y′} → Y y → Shrinks y y′ → Y y′)
                → runᴸ r ≾ Y → ⟦ hullᵁ r ⟧ ≾ Y
hullᵁ-invisible r Y closed f h h∈ with hullᵁ-shrinks r h∈
... | x , x∈ , s with f x x∈
...   | y , y∈ , xy = shrink-fit Y closed [] s y∈ xy

hull-upper : ∀ r (U : Expr upper) → (runᴸ r ≾ ⟦ U ⟧ → ⟦ hullᵁ r ⟧ ≾ ⟦ U ⟧)
                                   × (⟦ hullᵁ r ⟧ ≾ ⟦ U ⟧ → runᴸ r ≾ ⟦ U ⟧)
hull-upper r U =
  hullᵁ-invisible r ⟦ U ⟧ (Shrinks-closed U) ,
  ≾-trans (⊆⇒≾ (run⊆hullᵁ r))

-- against any set closed under lengthening, and a lower expression

hullᴸ-invisible : ∀ r (Y : Lang) → (∀ {y y′} → Y y → Lengthens y y′ → Y y′)
                → runᴸ r ≾ Y → ⟦ hullᴸ r ⟧ ≾ Y
hullᴸ-invisible r Y closed f h h∈ with hullᴸ-lengthens r h∈
... | x , x∈ , s with f x x∈
...   | y , y∈ , xy = lengthen-fit Y closed [] s y∈ xy

hull-lower : ∀ r (L : Expr lower) → (runᴸ r ≾ ⟦ L ⟧ → ⟦ hullᴸ r ⟧ ≾ ⟦ L ⟧)
                                   × (⟦ hullᴸ r ⟧ ≾ ⟦ L ⟧ → runᴸ r ≾ ⟦ L ⟧)
hull-lower r L =
  hullᴸ-invisible r ⟦ L ⟧ (Lengthens-closed L) ,
  ≾-trans (⊆⇒≾ (run⊆hullᴸ r))
