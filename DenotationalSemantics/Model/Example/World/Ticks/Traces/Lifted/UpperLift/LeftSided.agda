------------------------------------------------------------------------
-- A time-ticks Kripke frame for the sets of traces ordered up to the   --
-- sub-trace preorder as the resource grades.                           --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only the elapsed   --
-- time, not which continuation trace produced it. The grade is a floor --
-- under what must have happened, so the world must advance by *at      --
-- least* the duration of one of `P`'s traces:                          --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w + duration t ≤ w'   for some trace t of P   --
--                                                                    --
-- which is the shape of the left-sided interval frame, with the        --
-- interval's bound read off a trace of `P` instead of given outright.  --
--                                                                    --
-- Grade order and duration charge an operation the same execution      --
-- time `c o`, which is what makes `⊑-mono` hold: a grade that asks     --
-- for less is met by a trace of no greater duration.                   --
--                                                                    --
-- The quantifier is *existential*, where the `LowerLift.LeftSided`     --
-- frame's is universal: the two floors quantify over opposite sets, so --
-- advancing past one listed demand is what carries across here, and    --
-- past all of them there.                                             --
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

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Lifted.UpperLift.LeftSided
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
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open Order.TraceOrder O

open import Syntax.Grades.Example.Traces.Lifted.UpperLift.LeftSided Op _≟ₒ_ O
  using (upper-lift-left-sided; _≾_)

open import DenotationalSemantics.Model.World

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: reach the worlds at least a trace
-- duration of `P` ahead.

_⊑ᵗ[_]_ : ℕ → NeTraces → ℕ → Set
w ⊑ᵗ[ P ] w' = True (any? (λ t → (w + duration t) ≤? w') (traces P))

-- reflexivity at the unit grade `{ ε }`: the empty trace has duration
-- zero, so it asks the world to advance by nothing

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} = fromWitness (here (≤-reflexive (+-identityʳ w)))

-- transitivity multiplies the grades: the two advances compose into the
-- advance asked for by the sequenced trace, whose duration is the sum

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} {w'} {w''} p q
  with find (toWitness p) | find (toWitness q)
... | t₁ , t₁∈P , w+d₁≤w' | t₂ , t₂∈Q , w'+d₂≤w'' =
      fromWitness
        (Any.map
          (λ r → subst (λ z → w + duration z ≤ w'') r bound)
          (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q))
  where
    bound : w + duration (t₁ ∙ t₂) ≤ w''
    bound =
      ≤-trans (≤-reflexive eqU)
              (≤-trans (+-mono-≤ w+d₁≤w' ≤-refl) w'+d₂≤w'')
      where
        eqU : w + duration (t₁ ∙ t₂) ≡ (w + duration t₁) + duration t₂
        eqU = trans (cong (w +_) (duration-∙ t₁ t₂))
                    (sym (+-assoc w (duration t₁) (duration t₂)))

-- covariance: a grade that asks for less gives a larger accessibility.
-- The witnessing trace of `P` has some trace of `Q` inside it, whose
-- (smaller) duration is therefore also advanced past.

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {P} {Q} {w} {w'} rel p
  with find (toWitness p)
... | t , t∈P , w+dₜ≤w'
        with find (toWitness (rel t (fromWitness t∈P)))
...     | t' , t'∈Q , t'≼t =
          fromWitness
            (Any.map
              (λ r → subst (λ z → w + duration z ≤ w') r bound)
              t'∈Q)
  where
    bound : w + duration t' ≤ w'
    bound = ≤-trans (+-mono-≤ ≤-refl (duration-≼ t'≼t)) w+dₜ≤w'

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} {w'} p q =
  True-irr (any? (λ t → (w + duration t) ≤? w') (traces P)) p q

ticks : World upper-lift-left-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
