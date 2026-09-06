------------------------------------------------------------------------
-- A time-ticks Kripke frame for the sets of traces ordered up to the   --
-- sub-trace preorder as the resource grades.                           --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only the elapsed   --
-- time, not which continuation trace produced it. The grade is a floor --
-- under what must have happened, so the world must advance by *at      --
-- least* the duration of each of `P`'s traces:                         --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w + duration t ≤ w'   for every trace t of P  --
--                                                                    --
-- which is the shape of the left-sided interval frame, with the        --
-- interval's bound read off the traces of `P` instead of given         --
-- outright.                                                           --
--                                                                    --
-- The quantifier is universal because `LowerLift.LeftSided` compares    --
-- its two sets *exchanged*: weakening a floor replaces each of its     --
-- demands by one already covered, so it is advancing past all of the   --
-- demands that carries over, not advancing past one of them.           --
--                                                                    --
-- Grade order and duration charge an operation the same execution      --
-- time `c o`, which is what makes `⊑-mono` hold: a grade that asks     --
-- for less is met by traces of no greater duration.                    --
--                                                                    --
-- The bound is decidable and the traces form a finite set, so the      --
-- accessibility is phrased in the proof-irrelevant                     --
-- `True`-of-a-decision form.                                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Base as Base
import Syntax.Grades.Traces.Durations as Dur
import Syntax.Grades.Traces.Order as Order

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Lifted.LowerLift.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ)
  (O : Order.TraceOrder Op)
  (duration-≼ : {s t : Base.Trace Op}
              → Order.TraceOrder._≼_ O s t
              → Dur.Durations.duration Op c s ≤ Dur.Durations.duration Op c t)
  where

open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-mono-≤; +-identityʳ)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open Order.TraceOrder O

open import Syntax.Grades.Example.Traces.Lifted.LowerLift.LeftSided Op _≟ₒ_ O
  using (lower-lift-left-sided; _≾_)

open import DenotationalSemantics.Model.World

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: reach the worlds at least *every* trace
-- duration of `P` ahead.
--
-- The quantifier is universal because the grade's order is
-- `LowerLift.LeftSided`'s, which compares the two sets exchanged: a
-- weaker floor's demands are each covered by one of the stronger
-- floor's, so it is by having advanced past all of them that advancing
-- past all of a weaker floor's follows. Reading the set disjunctively
-- instead would not give `⊑-mono` here.

_⊑ᵗ[_]_ : ℕ → NeTraces → ℕ → Set
w ⊑ᵗ[ P ] w' = True (all? (λ t → (w + duration t) ≤? w') (traces P))

-- reflexivity at the unit grade `{ ε }`: the empty trace has duration
-- zero, so it asks the world to advance by nothing

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} =
  fromWitness (≤-reflexive (+-identityʳ w) All.∷ All.[])

-- transitivity multiplies the grades: the two advances compose into the
-- advance asked for by each sequenced trace, whose duration is the sum

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} {w'} {w''} p q =
  fromWitness (All.tabulate step)
  where
    step : ∀ {r} → r ∈ (traces P ·ˢ traces Q) → w + duration r ≤ w''
    step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) r∈
    ... | t₁ , t₂ , t₁∈P , t₂∈Q , refl =
          ≤-trans (≤-reflexive eqU)
                  (≤-trans (+-mono-≤ (All.lookup (toWitness p) t₁∈P) ≤-refl)
                           (All.lookup (toWitness q) t₂∈Q))
      where
        eqU : w + duration (t₁ ∙ t₂) ≡ (w + duration t₁) + duration t₂
        eqU = trans (cong (w +_) (duration-∙ t₁ t₂))
                    (sym (+-assoc w (duration t₁) (duration t₂)))

-- covariance: a grade that asks for less gives a larger accessibility.
-- Each trace of `Q` has some trace of `P` above it, whose duration the
-- world has already advanced past, and durations are monotone for `_≼_`.

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {P} {Q} {w} {w'} rel p =
  fromWitness (All.tabulate step)
  where
    step : ∀ {t'} → t' ∈ traces Q → w + duration t' ≤ w'
    step {t'} t'∈Q
      with find (toWitness (rel t' (fromWitness t'∈Q)))
    ... | t , t∈P , t'≼t =
          ≤-trans (+-mono-≤ ≤-refl (duration-≼ t'≼t))
                  (All.lookup (toWitness p) t∈P)

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} {w'} p q =
  True-irr (all? (λ t → (w + duration t) ≤? w') (traces P)) p q

ticks : World lower-lift-left-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
