------------------------------------------------------------------------
-- A trace-history Kripke frame for the trace grade of upper bounds.   --
--                                                                    --
-- Worlds are timed traces: the history observed so far. A grade `P`   --
-- reaches the histories obtained by appending a continuation the      --
-- grade permits:                                                     --
--                                                                    --
--   w ⊑ᵇ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                     --
--                          and  cont ≼ᵃ p   for some p ∈ P           --
--                                                                    --
-- Unlike the tick frame, this one sees which operations a bound       --
-- permits and not merely how long they take, so it distinguishes      --
-- grades the tick frame identifies -- `⟨ 3 ⟩` and `⌈ write ⌉` reach   --
-- the same time points but not the same histories.                    --
--                                                                    --
-- Accessibility is just "the continuation is a run the grade admits", --
-- which is what makes the frame conditions the grade's own laws:      --
-- reflexivity is the empty run, transitivity is monotonicity of the   --
-- trace product, and covariance is transitivity of the order.         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Allowance Op cost
  using (_≼ᵃ_; ≼ᵃ-refl; ≼ᵃ-trans; mono-∙)
open import Syntax.Grades.Traces.Allowance.Decidable Op cost
  using (module DecAllowance)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ cost cost-pos using (right-sided; _≾_)

open DecAllowance _≟ₒ_ using (_≼ᵃ?_)
open WithDecEq _≟ₒ_ using (True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation that stays within one
-- of the listed bounds.

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                          -- continuation
    within  : True (any? (λ p → cont ≼ᵃ? p) (traces P))      -- within some bound
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ᵇ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation stays
-- within the empty bound

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ u ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = any? (λ p → ε ≼ᵃ? p) (traces u)} (here (≼ᵃ-refl ε)))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two
-- continuations; monotonicity of the trace product carries the bound

⊑ᵇ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵇ[ P ] w' → w' ⊑ᵇ[ Q ] w'' → w ⊑ᵇ[ P · Q ] w''
⊑ᵇ-trans {P} {Q} {w} (mkᵇ t₁ w₁ eq₁) (mkᵇ t₂ w₂ eq₂)
  with find (toWitness w₁) | find (toWitness w₂)
... | a , a∈P , t₁≼a | b , b∈Q , t₂≼b =
      mkᵇ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼ᵃ_) eq (mono-∙ t₁≼a t₂≼b))
                     (∈-cartesianProductWith⁺ _∙_ a∈P b∈Q)))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: the bound the continuation stayed within itself stays
-- within one of the weaker grade's

⊑ᵇ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵇ[ P ] w' → w ⊑ᵇ[ Q ] w'
⊑ᵇ-mono {P} {Q} rel (mkᵇ cont wit eq) =
  mkᵇ cont (fromWitness within') eq
  where
    within' : Any (λ p → cont ≼ᵃ p) (traces Q)
    within' with find (toWitness wit)
    ... | t , t∈P , cont≼t
            with find (toWitness (rel t (fromWitness t∈P)))
    ...     | t' , t'∈Q , t≼t' =
              Any.map (λ e → subst (cont ≼ᵃ_) e (≼ᵃ-trans cont≼t t≼t')) t'∈Q

-- proof irrelevance: the continuation is determined by left
-- cancellation, and the bound is an irrelevant proof

⊑ᵇ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵇ[ P ] w') → p ≡ q
⊑ᵇ-irrelevant {P} {w} (mkᵇ cont wit refl) (mkᵇ cont' wit' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkᵇ cont z refl)
             (True-irr (any? (λ p → cont ≼ᵃ? p) (traces P)) wit wit')

------------------------------------------------------------------------
-- The frame.

histories : World right-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {P} {Q} → ⊑ᵇ-trans {P} {Q}
  ; ⊑-mono        = λ {P} {Q} → ⊑ᵇ-mono {P} {Q}
  ; ⊑-irrelevant  = λ {P} → ⊑ᵇ-irrelevant {P}
  }
