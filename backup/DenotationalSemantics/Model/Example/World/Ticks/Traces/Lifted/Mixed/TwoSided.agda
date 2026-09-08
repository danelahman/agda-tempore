------------------------------------------------------------------------
-- A time-ticks Kripke frame for the mixed two-sided trace intervals   --
-- as the resource grades.                                             --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only elapsed time,  --
-- so the grade's two endpoints are read through their durations, and   --
-- the world must advance into the window they span:                    --
--                                                                    --
--   w ⊑ᵗ[ [ L , U ] ] w'   iff   w + duration t ≤ w'  for some t ∈ L   --
--                           and  w' ≤ w + duration s  for some s ∈ U   --
--                                                                    --
-- Both quantifiers are existential, which is what distinguishes this   --
-- frame from `LowerLift.TwoSided`'s, whose floor is universal, and     --
-- from `UpperLift.TwoSided`'s, whose cap is. At each endpoint a frame  --
-- is existential exactly when the grade order runs over the source     --
-- set, and the mixed column is the one that does so at both.           --
--                                                                    --
-- So a world is reached when it lies past *one* listed demand and      --
-- short of *one* listed allowance: both endpoints are read             --
-- disjunctively here, as they are in the grade. `⊑-mono` holds of      --
-- both halves because `duration` is monotone for the sub-trace         --
-- preorder: a weaker demand advances less, a larger allowance permits  --
-- more.                                                                --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Base as Base
import Syntax.Grades.Traces.Durations as Dur
import Syntax.Grades.Traces.Order as Order

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Lifted.Mixed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ)
  (O : Order.TraceOrder Op)
  (duration-≼ : {s t : Base.Trace Op}
              → Order.TraceOrder._≼_ O s t
              → Dur.Durations.duration Op c s ≤ Dur.Durations.duration Op c t)
  where

open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-mono-≤; +-identityʳ)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open Order.TraceOrder O

open import Syntax.Grades.Example.Traces.Lifted.Mixed.TwoSided Op _≟ₒ_ O
  using (MixedInterval; lo; hi; mixed-two-sided; _≾ᵐⁱ_; _·ᵐⁱ_; uᵐⁱ)

open import DenotationalSemantics.Model.World

open Durations c
open WithDecEq _≟ₒ_ using (True-irr)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: advance past some floor-trace's
-- duration, and no further than some cap-trace's.

_⊑ᵗ[_]_ : ℕ → MixedInterval → ℕ → Set
w ⊑ᵗ[ i ] w' =
    True (any? (λ t → (w + duration t) ≤? w') (traces (lo i)))
  × True (any? (λ s → w' ≤? (w + duration s)) (traces (hi i)))

-- reflexivity at the unit grade: the empty trace has duration zero, so
-- the window is the singleton `[ w , w ]`

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ uᵐⁱ ] w
⊑ᵗ-refl {w} =
    fromWitness (here (≤-reflexive (+-identityʳ w)))
  , fromWitness (here (≤-reflexive (sym (+-identityʳ w))))

-- transitivity multiplies the grades: the two windows compose into the
-- window of the sequenced traces, whose durations are the sums

⊑ᵗ-trans : ∀ {i j w w' w''}
         → w ⊑ᵗ[ i ] w' → w' ⊑ᵗ[ j ] w'' → w ⊑ᵗ[ i ·ᵐⁱ j ] w''
⊑ᵗ-trans {i} {j} {w} {w'} {w''} (fl₁ , cp₁) (fl₂ , cp₂)
  with find (toWitness fl₁) | find (toWitness fl₂)
     | find (toWitness cp₁) | find (toWitness cp₂)
... | t , t∈L , w+t≤w' | t' , t'∈L' , w'+t'≤w''
    | s , s∈U , w'≤w+s | s' , s'∈U' , w''≤w'+s' =
      fromWitness
        (Any.map (λ r → subst (λ z → w + duration z ≤ w'') r lower)
                 (∈-cartesianProductWith⁺ _∙_ t∈L t'∈L'))
    , fromWitness
        (Any.map (λ r → subst (λ z → w'' ≤ w + duration z) r upper)
                 (∈-cartesianProductWith⁺ _∙_ s∈U s'∈U'))
  where
    lower : w + duration (t ∙ t') ≤ w''
    lower =
      ≤-trans (≤-reflexive (trans (cong (w +_) (duration-∙ t t'))
                                  (sym (+-assoc w (duration t) (duration t')))))
              (≤-trans (+-mono-≤ w+t≤w' ≤-refl) w'+t'≤w'')

    upper : w'' ≤ w + duration (s ∙ s')
    upper =
      ≤-trans (≤-trans w''≤w'+s' (+-mono-≤ w'≤w+s ≤-refl))
              (≤-reflexive (trans (+-assoc w (duration s) (duration s'))
                                  (cong (w +_) (sym (duration-∙ s s')))))

-- covariance: the witnessing demand is replaced by a weaker one, which
-- is no longer, and the witnessing allowance by a larger one

⊑ᵗ-mono : ∀ {i j w w'} → i ≾ᵐⁱ j → w ⊑ᵗ[ i ] w' → w ⊑ᵗ[ j ] w'
⊑ᵗ-mono {i} {j} {w} {w'} (l , h) (fl , cp) =
  fromWitness lower , fromWitness upper
  where
    lower : Any (λ t → w + duration t ≤ w') (traces (lo j))
    lower with find (toWitness fl)
    ... | t , t∈L , w+t≤w'
            with find (toWitness (l t (fromWitness t∈L)))
    ...     | t' , t'∈L' , t'≼t =
              Any.map (λ r → subst (λ z → w + duration z ≤ w') r
                               (≤-trans (+-mono-≤ ≤-refl (duration-≼ t'≼t))
                                        w+t≤w'))
                      t'∈L'

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
    (True-irr (any? (λ t → (w + duration t) ≤? w') (traces (lo i))) fl fl')
    (True-irr (any? (λ s → w' ≤? (w + duration s)) (traces (hi i))) cp cp')

ticks : World mixed-two-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {i} {j} → ⊑ᵗ-trans {i} {j}
  ; ⊑-mono       = λ {i} {j} → ⊑ᵗ-mono {i} {j}
  ; ⊑-irrelevant = λ {i} → ⊑ᵗ-irrelevant {i}
  }
