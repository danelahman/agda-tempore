------------------------------------------------------------------------
-- A trace-history Kripke frame for the subset grade of upper bounds.  --
--                                                                    --
-- Worlds are timed traces: the history observed so far. A grade `Q`   --
-- reaches the histories obtained by appending a run it lists:         --
--                                                                    --
--   w ⊑ᵇ[ Q ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'  and  cont ∈ Q       --
--                                                                    --
-- Accessibility is membership outright -- there is no comparison      --
-- between the continuation and a listed run to make, equality being   --
-- the whole order. So this frame is as fine-grained as the grade is:  --
-- unlike the tick frame, it distinguishes `⌈ write ⌉` from `⟨ 3 ⟩`.   --
--                                                                    --
-- READING. The grade caps which runs may occur, and the frame says a  --
-- world is reachable exactly when the run that got there is one of    --
-- them. Covariance is then just that a listed run of a smaller grade  --
-- is a listed run of a larger one.                                    --
--                                                                    --
-- The grade's `any-run` permits every run, so it leaves the           --
-- continuation unconstrained and asks only that `w'` extend `w`.      --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subsets.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ using (∈-⊑)
open import Syntax.Grades.Example.Traces.Subsets.RightSided Op _≟ₒ_
  using (right-sided; Permits; permitting_; any-run; _·ᵖ_; _≾_)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories

-- the condition on the continuation, vacuous at `any-run`

Listed : Trace → Permits → Set
Listed cont (permitting Q) = True (cont ∈? traces Q)
Listed cont any-run       = ⊤

Listed-irr : (cont : Trace) (Q : Permits) → (p q : Listed cont Q) → p ≡ q
Listed-irr cont (permitting Q) = True-irr (cont ∈? traces Q)
Listed-irr _    any-run       tt tt = refl

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (Q : Permits) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                          -- continuation
    listed  : Listed cont Q                  -- one of the permitted runs
    extends : w ∙ cont ≡ w'                  -- `w'` extends `w`

open _⊑ᵇ[_]_

-- appending the two continuations in turn extends across both

extends-∙ : (w t₁ t₂ : Trace) {w' w'' : Trace}
          → w ∙ t₁ ≡ w' → w' ∙ t₂ ≡ w'' → w ∙ (t₁ ∙ t₂) ≡ w''
extends-∙ w t₁ t₂ eq₁ eq₂ =
  trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂)

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ (permitting u) ] w
⊑ᵇ-refl {w} =
  mkᵇ ε (fromWitness {a? = ε ∈? traces u} (here refl)) (∙-identityʳ w)

-- transitivity multiplies the grades: the two continuations sequence
-- into one the product lists

⊑ᵇ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵇ[ P ] w' → w' ⊑ᵇ[ Q ] w'' → w ⊑ᵇ[ P ·ᵖ Q ] w''
⊑ᵇ-trans {permitting _} {any-run}    {w} (mkᵇ t₁ _ eq₁) (mkᵇ t₂ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {any-run}    {_}      {w} (mkᵇ t₁ _ eq₁) (mkᵇ t₂ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {permitting P} {permitting Q} {w} (mkᵇ t₁ l₁ eq₁) (mkᵇ t₂ l₂ eq₂) =
  mkᵇ (t₁ ∙ t₂)
      (fromWitness
        (∈-cartesianProductWith⁺ _∙_ (toWitness l₁) (toWitness l₂)))
      (extends-∙ w t₁ t₂ eq₁ eq₂)

⊑ᵇ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵇ[ P ] w' → w ⊑ᵇ[ Q ] w'
⊑ᵇ-mono {_}      {any-run}    rel (mkᵇ cont _ eq) = mkᵇ cont tt eq
⊑ᵇ-mono {any-run}    {permitting _} ()
⊑ᵇ-mono {permitting P} {permitting Q} rel (mkᵇ cont l eq) =
  mkᵇ cont (fromWitness (∈-⊑ rel (toWitness l))) eq

-- proof irrelevance: the continuation is determined by left
-- cancellation, and membership is an irrelevant proof

⊑ᵇ-irrelevant : ∀ {Q w w'} → (p q : w ⊑ᵇ[ Q ] w') → p ≡ q
⊑ᵇ-irrelevant {Q} {w} (mkᵇ cont l refl) (mkᵇ cont' l' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl = cong (λ z → mkᵇ cont z refl) (Listed-irr cont Q l l')

------------------------------------------------------------------------
-- The frame.

histories : World right-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {P} {Q} → ⊑ᵇ-trans {P} {Q}
  ; ⊑-mono        = λ {P} {Q} → ⊑ᵇ-mono {P} {Q}
  ; ⊑-irrelevant  = λ {Q} → ⊑ᵇ-irrelevant {Q}
  }
