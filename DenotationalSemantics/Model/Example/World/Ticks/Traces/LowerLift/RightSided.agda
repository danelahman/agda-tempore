------------------------------------------------------------------------
-- A time-ticks Kripke frame for the (right) one-sided sets of traces  --
-- as the resource grades.                                             --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only elapsed time,  --
-- so the cap is read through its durations and bounds how far the      --
-- world may advance:                                                   --
--                                                                    --
--   w ⊑ᵗ[ U ] w'   iff   w' ≤ w + duration s   for some trace s of U   --
--                                                                    --
-- which is the shape of the right-sided interval frame, with the       --
-- bound read off a trace of `U` instead of given outright. A cap alone --
-- never forces the world to advance, so `w ⊑ᵗ[ U ] w` always holds.    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.LowerLift.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.Nat using (_+_; _≤_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-mono-≤; +-identityʳ)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op c
open import Syntax.Grades.Traces.SubtraceDuration Op c using (duration-≼)

open import Syntax.Grades.Example.Traces.LowerLift.RightSided Op _≟ₒ_ c
  using (lower-lift-right-sided; _≾_)

open import DenotationalSemantics.Model.World

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: advance at most a cap-trace's duration.

_⊑ᵗ[_]_ : ℕ → NeTraces → ℕ → Set
w ⊑ᵗ[ U ] w' = True (any? (λ s → w' ≤? (w + duration s)) (traces U))

-- reflexivity at the unit grade: the empty trace has duration zero, so
-- the world may not advance at all

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} = fromWitness (here (≤-reflexive (sym (+-identityʳ w))))

-- transitivity multiplies the grades: the two allowances compose into
-- the allowance of the sequenced trace, whose duration is the sum

⊑ᵗ-trans : ∀ {U V w w' w''}
         → w ⊑ᵗ[ U ] w' → w' ⊑ᵗ[ V ] w'' → w ⊑ᵗ[ U · V ] w''
⊑ᵗ-trans {U} {V} {w} {w'} {w''} cp₁ cp₂
  with find (toWitness cp₁) | find (toWitness cp₂)
... | x , x∈U , w'≤w+x | y , y∈V , w''≤w'+y =
      fromWitness
        (Any.map (λ r → subst (λ z → w'' ≤ w + duration z) r upper)
                 (∈-cartesianProductWith⁺ _∙_ x∈U y∈V))
  where
    upper : w'' ≤ w + duration (x ∙ y)
    upper =
      ≤-trans (≤-trans w''≤w'+y (+-mono-≤ w'≤w+x ≤-refl))
              (≤-reflexive (trans (+-assoc w (duration x) (duration y))
                                  (cong (w +_) (sym (duration-∙ x y)))))

-- covariance: a cap that permits more allows the world to advance
-- further

⊑ᵗ-mono : ∀ {U V w w'} → U ≾ V → w ⊑ᵗ[ U ] w' → w ⊑ᵗ[ V ] w'
⊑ᵗ-mono {U} {V} {w} {w'} h cp
  with find (toWitness cp)
... | s , s∈U , w'≤w+s
        with find (toWitness (h s (fromWitness s∈U)))
...     | s' , s'∈V , s≼s' =
          fromWitness
            (Any.map (λ r → subst (λ z → w' ≤ w + duration z) r
                              (≤-trans w'≤w+s
                                       (+-mono-≤ ≤-refl (duration-≼ s≼s'))))
                     s'∈V)

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {U w w'} → (p q : w ⊑ᵗ[ U ] w') → p ≡ q
⊑ᵗ-irrelevant {U} {w} {w'} p q =
  True-irr (any? (λ s → w' ≤? (w + duration s)) (traces U)) p q

ticks : World lower-lift-right-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {U} {V} → ⊑ᵗ-trans {U} {V}
  ; ⊑-mono       = λ {U} {V} → ⊑ᵗ-mono {U} {V}
  ; ⊑-irrelevant = λ {U} → ⊑ᵗ-irrelevant {U}
  }
