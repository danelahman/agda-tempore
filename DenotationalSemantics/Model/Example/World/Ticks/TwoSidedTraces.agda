------------------------------------------------------------------------
-- A time-ticks Kripke frame for two-sided trace intervals as the      --
-- resource grades.                                                    --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only elapsed time,  --
-- so the grade's two endpoints are read through their durations, and   --
-- the world must advance into the window they span:                    --
--                                                                    --
--   w ⊑ᵗ[ [ L , U ] ] w'   iff   w + duration t ≤ w'  for every t ∈ L  --
--                           and  w' ≤ w + duration s  for some  s ∈ U  --
--                                                                    --
-- which is `Ticks.TwoSidedIntervals` with the two endpoints read off   --
-- traces instead of given outright. Both halves hold of `⊑-mono`       --
-- because `duration` is monotone for the sub-trace preorder: a smaller --
-- floor-trace advances less, and a larger cap-trace allows more.       --
--                                                                    --
-- The two quantifiers differ because the grade's two endpoints are     --
-- compared in opposite directions: weakening replaces each floor       --
-- demand by one already covered, so all of them must be met, while it  --
-- replaces some cap allowance by a larger one, so one suffices.        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.TwoSidedTraces
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.Nat using (_+_; _≤_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-mono-≤; +-identityʳ)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _×-dec_)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op c
open import Syntax.Grades.Traces.SubtraceDuration Op c using (duration-≼)

open import Syntax.Grades.Example.Traces.LowerLift.TwoSided Op _≟ₒ_ c
  using (TraceInterval; lo; hi; lower-lift-two-sided; _≾ᵗⁱ_; _·ᵗⁱ_; uᵗⁱ)

open import DenotationalSemantics.Model.World

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: advance at least a floor-trace's
-- duration, and at most a cap-trace's.

_⊑ᵗ[_]_ : ℕ → TraceInterval → ℕ → Set
w ⊑ᵗ[ i ] w' =
    True (all? (λ t → (w + duration t) ≤? w') (traces (lo i)))
  × True (any? (λ s → w' ≤? (w + duration s)) (traces (hi i)))

-- reflexivity at the unit grade: the empty trace has duration zero, so
-- the window is the singleton `[ w , w ]`

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ uᵗⁱ ] w
⊑ᵗ-refl {w} =
    fromWitness (≤-reflexive (+-identityʳ w) All.∷ All.[])
  , fromWitness (here (≤-reflexive (sym (+-identityʳ w))))

-- transitivity multiplies the grades: the two windows compose into the
-- window of the sequenced traces, whose durations are the sums

⊑ᵗ-trans : ∀ {i j w w' w''}
         → w ⊑ᵗ[ i ] w' → w' ⊑ᵗ[ j ] w'' → w ⊑ᵗ[ i ·ᵗⁱ j ] w''
⊑ᵗ-trans {i} {j} {w} {w'} {w''} (fl₁ , cp₁) (fl₂ , cp₂)
  with find (toWitness cp₁) | find (toWitness cp₂)
... | x , x∈U , w'≤w+x  | y , y∈U' , w''≤w'+y =
      fromWitness (All.tabulate lower)
    , fromWitness
        (Any.map (λ r → subst (λ z → w'' ≤ w + duration z) r upper)
                 (∈-cartesianProductWith⁺ _∙_ x∈U y∈U'))
  where
    lower : ∀ {r} → r ∈ (traces (lo i) ·ˢ traces (lo j))
          → w + duration r ≤ w''
    lower {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces (lo i)) (traces (lo j)) r∈
    ... | a , b , a∈L , b∈L' , refl =
          ≤-trans (≤-reflexive (trans (cong (w +_) (duration-∙ a b))
                                      (sym (+-assoc w (duration a) (duration b)))))
                  (≤-trans (+-mono-≤ (All.lookup (toWitness fl₁) a∈L) ≤-refl)
                           (All.lookup (toWitness fl₂) b∈L'))

    upper : w'' ≤ w + duration (x ∙ y)
    upper =
      ≤-trans (≤-trans w''≤w'+y (+-mono-≤ w'≤w+x ≤-refl))
              (≤-reflexive (trans (+-assoc w (duration x) (duration y))
                                  (cong (w +_) (sym (duration-∙ x y)))))

-- covariance: a lower floor advances less, a higher cap allows more

⊑ᵗ-mono : ∀ {i j w w'} → i ≾ᵗⁱ j → w ⊑ᵗ[ i ] w' → w ⊑ᵗ[ j ] w'
⊑ᵗ-mono {i} {j} {w} {w'} (l , h) (fl , cp) =
  fromWitness lower , fromWitness upper
  where
    lower : All (λ t → w + duration t ≤ w') (traces (lo j))
    lower = All.tabulate step
      where
        step : ∀ {t'} → t' ∈ traces (lo j) → w + duration t' ≤ w'
        step {t'} t'∈L'
          with find (toWitness (l t' (fromWitness t'∈L')))
        ... | t , t∈L , t'≼t =
              ≤-trans (+-mono-≤ ≤-refl (duration-≼ t'≼t))
                      (All.lookup (toWitness fl) t∈L)

    upper : Any (λ s → w' ≤ w + duration s) (traces (hi j))
    upper with find (toWitness cp)
    ... | s , s∈U , w'≤w+s
            with find (toWitness (h s (fromWitness s∈U)))
    ...     | s' , s'∈U' , s≼s' =
              Any.map (λ r → subst (λ z → w' ≤ w + duration z) r
                               (≤-trans w'≤w+s
                                        (+-mono-≤ ≤-refl (duration-≼ s≼s'))))
                      s'∈U'

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵗ[ i ] w') → p ≡ q
⊑ᵗ-irrelevant {i} {w} {w'} (fl , cp) (fl' , cp') =
  cong₂ _,_
    (True-irr (all? (λ t → (w + duration t) ≤? w') (traces (lo i))) fl fl')
    (True-irr (any? (λ s → w' ≤? (w + duration s)) (traces (hi i))) cp cp')

ticks : World lower-lift-two-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {i} {j} → ⊑ᵗ-trans {i} {j}
  ; ⊑-mono       = λ {i} {j} → ⊑ᵗ-mono {i} {j}
  ; ⊑-irrelevant = λ {i} → ⊑ᵗ-irrelevant {i}
  }
