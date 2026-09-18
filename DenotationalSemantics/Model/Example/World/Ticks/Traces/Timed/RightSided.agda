------------------------------------------------------------------------
-- A time-ticks Kripke frame for the trace grade of upper bounds.      --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only elapsed time, --
-- so a grade is read through the durations of the bounds it lists,    --
-- and moving between worlds may take no longer than one of them:      --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w' ≤ w + duration p   for some p ∈ P         --
--                                                                    --
-- The quantifier is existential because the grade's own order is:     --
-- `P ≾ Q` asks each bound of `P` to stay within one of `Q`, so the    --
-- witnessing bound travels, and it takes no longer at the far end     --
-- because `duration` is monotone for the allowance order.            --
--                                                                    --
-- This is the shape of a right-sided interval frame, with the bound   --
-- read off a trace of the grade rather than given outright -- and     --
-- what the tick world cannot see is which operations that trace        --
-- permits, only how long they take.                                  --
--                                                                    --
-- The grade's `unbounded` lists no bound at all, so it relates        --
-- every pair of worlds.                                               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-mono-≤; +-identityʳ)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Allowance Op costʰⁱ using (duration-≼ᵃ)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ costʰⁱ costʰⁱ-pos
  using (right-sided; Bounds; within_; unbounded; _·ᵇ_; _≾_)

open import DenotationalSemantics.Model.World

open Durations costʰⁱ
open WithDecEq _≟ₒ_ using (True-irr)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: advance no further than one of the
-- listed bounds takes; at `unbounded` there is no bound to stay within.

_⊑ᵗ[_]_ : ℕ → Bounds → ℕ → Set
w ⊑ᵗ[ (within P) ] w' = True (any? (λ p → w' ≤? (w + duration p)) (traces P))
w ⊑ᵗ[ unbounded ]      w' = ⊤

-- reflexivity at the unit grade `{ ε }`: the empty bound permits no
-- time to pass, and none has

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ (within u) ] w
⊑ᵗ-refl {w} = fromWitness (here (≤-reflexive (sym (+-identityʳ w))))

-- transitivity multiplies the grades: the two advances compose into the
-- one the sequenced bound allows, whose duration is the sum

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P ·ᵇ Q ] w''
⊑ᵗ-trans {within _} {unbounded}   p q = tt
⊑ᵗ-trans {unbounded}    {_}     p q = tt
⊑ᵗ-trans {within P} {within Q} {w} {w'} {w''} p q
  with find (toWitness p) | find (toWitness q)
... | t₁ , t₁∈P , w'≤w+t₁ | t₂ , t₂∈Q , w''≤w'+t₂ =
      fromWitness
        (Any.map (λ r → subst (λ z → w'' ≤ w + duration z) r bound)
                 (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q))
  where
    bound : w'' ≤ w + duration (t₁ ∙ t₂)
    bound =
      ≤-trans (≤-trans w''≤w'+t₂ (+-mono-≤ w'≤w+t₁ ≤-refl))
              (≤-reflexive
                (trans (+-assoc w (duration t₁) (duration t₂))
                       (cong (w +_) (sym (duration-∙ t₁ t₂)))))

-- covariance: the bound that witnessed the advance stays within one of
-- the weaker grade's, which therefore takes at least as long

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {_}      {unbounded}    rel p = tt
⊑ᵗ-mono {unbounded}    {within _} ()
⊑ᵗ-mono {within P} {within Q} {w} {w'} rel p
  with find (toWitness p)
... | t , t∈P , w'≤w+t
        with find (toWitness (rel t (fromWitness t∈P)))
...     | t' , t'∈Q , t≼t' =
          fromWitness
            (Any.map (λ r → subst (λ z → w' ≤ w + duration z) r bound) t'∈Q)
  where
    bound : w' ≤ w + duration t'
    bound = ≤-trans w'≤w+t (+-mono-≤ ≤-refl (duration-≼ᵃ t≼t'))

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {within P} {w} {w'} p q =
  True-irr (any? (λ t → w' ≤? (w + duration t)) (traces P)) p q
⊑ᵗ-irrelevant {unbounded}    tt tt = refl

ticks : World right-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
