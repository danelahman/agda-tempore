------------------------------------------------------------------------
-- A time-ticks Kripke frame for the trace grade of guarantees.        --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only elapsed time, --
-- so a grade is read through the durations of the guarantees it       --
-- lists, and moving between worlds must take at least one of them:    --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w + duration p ≤ w'   for some p ∈ P         --
--                                                                    --
-- The quantifier is existential because the grade's own order is:     --
-- `P ≾ P'` asks each guarantee of `P` to be weakened by one of `P'`,  --
-- so the witnessing guarantee travels, and it takes no longer at the  --
-- far end because `duration` is monotone for the coverage order.      --
--                                                                    --
-- This is the shape of a left-sided interval frame, with the bound    --
-- read off a trace of the grade rather than given outright -- and     --
-- what the tick world cannot see is which operations that trace       --
-- demands, only how long they take.                                  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

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
open import Syntax.Grades.Traces.Coverage Op cost using (duration-≼ᶜ)

open import Syntax.Grades.Example.Traces.Timed.LeftSided
  Op _≟ₒ_ cost using (left-sided; _≾_)

open import DenotationalSemantics.Model.World

open Durations cost
open WithDecEq _≟ₒ_ using (True-irr)

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: advance at least as far as one of the
-- listed guarantees takes.

_⊑ᵗ[_]_ : ℕ → NeTraces → ℕ → Set
w ⊑ᵗ[ P ] w' = True (any? (λ p → (w + duration p) ≤? w') (traces P))

-- reflexivity at the unit grade `{ ε }`: the empty guarantee demands no
-- time to pass, and none has

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} = fromWitness (here (≤-reflexive (+-identityʳ w)))

-- transitivity multiplies the grades: the two advances compose into the
-- one the sequenced guarantee demands, whose duration is the sum

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} {w'} {w''} p q
  with find (toWitness p) | find (toWitness q)
... | t₁ , t₁∈P , w+t₁≤w' | t₂ , t₂∈Q , w'+t₂≤w'' =
      fromWitness
        (Any.map (λ r → subst (λ z → (w + duration z) ≤ w'') r bound)
                 (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q))
  where
    bound : (w + duration (t₁ ∙ t₂)) ≤ w''
    bound =
      ≤-trans (≤-reflexive
                (trans (cong (w +_) (duration-∙ t₁ t₂))
                       (sym (+-assoc w (duration t₁) (duration t₂)))))
              (≤-trans (+-mono-≤ w+t₁≤w' ≤-refl) w'+t₂≤w'')

-- covariance: the guarantee that witnessed the advance is weakened by
-- one of the weaker grade's, which therefore takes no longer

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {P} {Q} {w} {w'} rel p
  with find (toWitness p)
... | t , t∈P , w+t≤w'
        with find (toWitness (rel t (fromWitness t∈P)))
...     | t' , t'∈Q , t'≼t =
          fromWitness
            (Any.map (λ r → subst (λ z → (w + duration z) ≤ w') r bound) t'∈Q)
  where
    bound : (w + duration t') ≤ w'
    bound = ≤-trans (+-mono-≤ ≤-refl (duration-≼ᶜ t'≼t)) w+t≤w'

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} {w'} p q =
  True-irr (any? (λ t → (w + duration t) ≤? w') (traces P)) p q

ticks : World left-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
