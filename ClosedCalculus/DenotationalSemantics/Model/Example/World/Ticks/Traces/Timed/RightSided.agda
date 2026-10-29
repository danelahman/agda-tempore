------------------------------------------------------------------------
-- A time-ticks Kripke frame for the trace grade of upper bounds.     --
--                                                                    --
-- Worlds are time points of the time domain. A tick world records    --
-- only elapsed time, and a grade is read through the durations of    --
-- the bounds it lists: moving between worlds goes forward and takes  --
-- no longer than one of them.                                        --
--                                                                    --
--   w ⊑[ P ] w'   iff   w ≤ w'   and                                 --
--                       w' ≤ w + duration p   for some p ∈ P         --
--                                                                    --
-- The quantifier is existential, as in the order of the grade:       --
-- `P ≾ Q` requires each bound of `P` to stay within one of `Q`, so   --
-- the witnessing bound is transported, and it takes no longer at the --
-- far end, `duration` being monotone for the allowance order.        --
--                                                                    --
-- This is a right-sided interval frame with the bound read off a     --
-- trace of the grade; the tick world records how long the operations --
-- of that trace take, not which operations it permits.               --
--                                                                    --
-- The grade `unbounded` lists no bound and reaches every world       --
-- ahead.                                                             --
--                                                                    --
-- The relation is the bound restricted to forward moves: the unit is --
-- least, and without `w ≤ w'` the unit grade would reach the past.   --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Relation.Nullary using (¬_)

open import Grades.Durations using (Duration; TimeDomain)

module ClosedCalculus.DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.RightSided
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → Duration.Carrier D)
  (costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ Duration.0ᴰ D)) where

open import Grades.Durations.Monus T as M using (Carrier)
open M.Notation
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Grades.Traces.Durations T Op
open import Grades.Traces.Allowance T Op costʰⁱ using (duration-≼ᵃ)

open import Grades.Examples.Traces.Timed.RightSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (right-sided; Bounds; within_; unbounded; _·ᵇ_; _≾_;
         Antichain; traces; u; _∙_; _·ˢ_; n-◃⁻; ◃-∈; True-irr)

open import ClosedCalculus.DenotationalSemantics.Model.World
open import ClosedCalculus.DenotationalSemantics.Model.World.Action using (forward)

open Durations costʰⁱ

------------------------------------------------------------------------
-- The frame

-- The bound: advance no further than one of the listed bounds takes;
-- at `unbounded` there is no bound to stay within.

_⊑ᵗ[_]_ : Carrier → Bounds → Carrier → Set
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
... | t₁ , t₁∈P , w'≤w+t₁ | t₂ , t₂∈Q , w''≤w'+t₂
        with find (n-◃⁻ (traces P ·ˢ traces Q)
                        (◃-∈ (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q)))
...     | t , t∈PQ , t₁∙t₂≼t =
          fromWitness
            (Any.map (λ r → subst (λ z → w'' ≤ w + duration z) r bound) t∈PQ)
  where
    sequenced : w'' ≤ w + duration (t₁ ∙ t₂)
    sequenced =
      ≤-trans (≤-trans w''≤w'+t₂ (+-mono-≤ w'≤w+t₁ ≤-refl))
              (≤-reflexive
                (trans (+-assoc w (duration t₁) (duration t₂))
                       (cong (w +_) (sym (duration-∙ t₁ t₂)))))

    bound : w'' ≤ w + duration t
    bound = ≤-trans sequenced (+-mono-≤ ≤-refl (duration-≼ᵃ t₁∙t₂≼t))

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

-- the bound as a frame

private
  bounded : World right-sided
  bounded = record
    { W             = Carrier
    ; _⊑[_]_       = _⊑ᵗ[_]_
    ; ⊑-refl       = ⊑ᵗ-refl
    ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
    ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
    ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
    }

-- The frame: the bound, forward moves only.

ticks : World right-sided
ticks = forward bounded _≤_ ≤-refl ≤-trans ≤-irrelevant

-- the relation it states

⊑-def : ∀ {w P w'}
      → World._⊑[_]_ ticks w P w' ≡ ((w ≤ w') × (w ⊑ᵗ[ P ] w'))
⊑-def = refl
