------------------------------------------------------------------------
-- A trace-history Kripke frame for the Smyth-ordered caps.            --
--                                                                    --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A resource grade `P` reaches the histories obtained by          --
-- appending a continuation `cont` that stays within *every* allowance  --
-- the grade lists:                                                    --
--                                                                    --
--   w ⊑ʰ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                      --
--                          and   cont ≼ s   for every   s ∈ P         --
--                                                                    --
-- The quantifier is universal because `UpperLift.RightSided`'s order   --
-- runs over the *right-hand* set: weakening asks each of the new       --
-- allowances to be justified by an old one, so what carries over is    --
-- having stayed within all of them, not within one.                    --
--                                                                    --
-- That is the mirror of `LowerLift.LeftSided`'s frame, whose floor is  --
-- universal for the same reason; `LowerLift.RightSided`'s cap, whose   --
-- order runs over the left-hand set, is existential instead.           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.UpperLift.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open Order.TraceOrder O
open import Syntax.Grades.Example.Traces.Lifted.UpperLift.RightSided Op _≟ₒ_ O
  using (upper-lift-right-sided; _≾_)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation that fits inside
-- every member of the set of traces `P`.

infix 5 _⊑ʰ[_]_

record _⊑ʰ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkʰ
  field
    cont    : Trace                                          -- continuation
    within  : True (all? (λ s → cont ≼? s) (traces P))       -- within every allowance
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ʰ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation stays
-- within the sole allowance `ε`

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ u ] w
⊑ʰ-refl {w} = mkʰ ε (fromWitness {a? = all? (λ s → ε ≼? s) (traces u)}
                                 (≼-refl ε All.∷ All.[]))
                    (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two continuations;
-- monotonicity of the trace product keeps the sequenced continuation
-- inside each sequenced allowance

⊑ʰ-trans : ∀ {P Q w w' w''}
         → w ⊑ʰ[ P ] w' → w' ⊑ʰ[ Q ] w'' → w ⊑ʰ[ P · Q ] w''
⊑ʰ-trans {P} {Q} {w} (mkʰ t₁ wi₁ eq₁) (mkʰ t₂ wi₂ eq₂) =
  mkʰ (t₁ ∙ t₂)
      (fromWitness (All.tabulate step))
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    step : ∀ {r} → r ∈ (traces P ·ˢ traces Q) → (t₁ ∙ t₂) ≼ r
    step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) r∈
    ... | a , b , a∈P , b∈Q , refl =
          mono-∙ (All.lookup (toWitness wi₁) a∈P)
                 (All.lookup (toWitness wi₂) b∈Q)

-- covariance: a grade that permits more gives a larger relation. Each
-- allowance of `Q` has one of `P`'s inside it, and the continuation is
-- already within that, so transitivity of the sub-trace preorder carries
-- it across.

⊑ʰ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ʰ[ P ] w' → w ⊑ʰ[ Q ] w'
⊑ʰ-mono {P} {Q} rel (mkʰ cont wi eq) =
  mkʰ cont (fromWitness (All.tabulate step)) eq
  where
    step : ∀ {q} → q ∈ traces Q → cont ≼ q
    step {q} q∈Q
      with find (toWitness (rel q (fromWitness q∈Q)))
    ... | p , p∈P , p≼q = ≼-trans (All.lookup (toWitness wi) p∈P) p≼q

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the containment witness is an irrelevant proof

⊑ʰ-irrelevant : ∀ {P w w'} → (p q : w ⊑ʰ[ P ] w') → p ≡ q
⊑ʰ-irrelevant {P} {w} (mkʰ cont wi refl) (mkʰ cont' wi' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkʰ cont z refl)
             (True-irr (all? (λ s → cont ≼? s) (traces P)) wi wi')

------------------------------------------------------------------------
-- The frame.

histories : World upper-lift-right-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ʰ[_]_
  ; ⊑-refl        = ⊑ʰ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
