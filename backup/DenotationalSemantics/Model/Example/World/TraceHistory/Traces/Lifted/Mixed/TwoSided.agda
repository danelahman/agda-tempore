------------------------------------------------------------------------
-- A trace-history Kripke frame for the mixed two-sided trace          --
-- intervals as the resource grades.                                   --
--                                                                    --
-- Worlds are timed traces `Trace`. A resource grade `[ L , U ]` reaches --
-- the histories obtained by appending a continuation `cont` bounded on  --
-- both sides:                                                         --
--                                                                    --
--   w ⊑ᵇ[ [ L , U ] ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'              --
--                                  and  t ≼ cont   for some  t ∈ L    --
--                                  and  cont ≼ s   for some  s ∈ U    --
--                                                                    --
-- Both quantifiers are existential, where `LowerLift.TwoSided`'s frame --
-- has a universal floor and `UpperLift.TwoSided`'s a universal cap: at --
-- each endpoint the frame is existential exactly when the grade order  --
-- runs over the source set, and the mixed column is the one that does  --
-- so at both. So this frame reads the grade as the grade reads itself  --
-- -- the continuation covers one listed demand and stays within one    --
-- listed allowance -- which makes it the frame whose accessibility is  --
-- literally "the continuation is a run the grade admits".              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.Mixed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open Order.TraceOrder O

open import Syntax.Grades.Example.Traces.Lifted.Mixed.TwoSided Op _≟ₒ_ O
  using (MixedInterval; lo; hi; mixed-two-sided; _≾ᵐⁱ_; _·ᵐⁱ_; uᵐⁱ)

open WithDecEq _≟ₒ_ using (True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation that covers some
-- member of the floor and stays within some member of the cap.

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (i : MixedInterval) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                            -- continuation
    floor   : True (any? (λ t → t ≼? cont) (traces (lo i)))    -- covers some floor member
    cap     : True (any? (λ s → cont ≼? s) (traces (hi i)))    -- within some cap member
    extends : w ∙ cont ≡ w'                                    -- `w'` extends `w`

open _⊑ᵇ[_]_

-- reflexivity at the unit grade `[ { ε } , { ε } ]`: the empty
-- continuation both covers and is covered by the empty trace

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ uᵐⁱ ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = any? (λ t → t ≼? ε) (traces u)} (here (≼-refl ε)))
      (fromWitness {a? = any? (λ s → ε ≼? s) (traces u)} (here (≼-refl ε)))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two continuations;
-- monotonicity of the trace product carries both bounds across

⊑ᵇ-trans : ∀ {i j w w' w''}
         → w ⊑ᵇ[ i ] w' → w' ⊑ᵇ[ j ] w'' → w ⊑ᵇ[ i ·ᵐⁱ j ] w''
⊑ᵇ-trans {i} {j} {w} (mkᵇ t₁ fl₁ cp₁ eq₁) (mkᵇ t₂ fl₂ cp₂ eq₂)
  with find (toWitness fl₁) | find (toWitness fl₂)
     | find (toWitness cp₁) | find (toWitness cp₂)
... | a , a∈L , a≼t₁ | b , b∈L' , b≼t₂
    | x , x∈U , t₁≼x | y , y∈U' , t₂≼y =
      mkᵇ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst (_≼ (t₁ ∙ t₂)) eq (mono-∙ a≼t₁ b≼t₂))
                     (∈-cartesianProductWith⁺ _∙_ a∈L b∈L')))
          (fromWitness
            (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼_) eq (mono-∙ t₁≼x t₂≼y))
                     (∈-cartesianProductWith⁺ _∙_ x∈U y∈U')))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: both halves travel existentially -- the covered demand
-- has a weaker one in the larger grade, and the allowance stayed within
-- has a larger one

⊑ᵇ-mono : ∀ {i j w w'} → i ≾ᵐⁱ j → w ⊑ᵇ[ i ] w' → w ⊑ᵇ[ j ] w'
⊑ᵇ-mono {i} {j} (l , h) (mkᵇ cont fl cp eq) =
  mkᵇ cont (fromWitness floor') (fromWitness cap') eq
  where
    floor' : Any (λ t → t ≼ cont) (traces (lo j))
    floor' with find (toWitness fl)
    ... | t , t∈L , t≼cont
            with find (toWitness (l t (fromWitness t∈L)))
    ...     | t' , t'∈L' , t'≼t =
              Any.map (λ e → subst (_≼ cont) e (≼-trans t'≼t t≼cont)) t'∈L'

    cap' : Any (λ s → cont ≼ s) (traces (hi j))
    cap' with find (toWitness cp)
    ... | s , s∈U , cont≼s
            with find (toWitness (h s (fromWitness s∈U)))
    ...     | s' , s'∈U' , s≼s' =
              Any.map (λ e → subst (cont ≼_) e (≼-trans cont≼s s≼s')) s'∈U'

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and both bounds are irrelevant proofs

⊑ᵇ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵇ[ i ] w') → p ≡ q
⊑ᵇ-irrelevant {i} {w} (mkᵇ cont fl cp refl) (mkᵇ cont' fl' cp' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong₂ (λ z z' → mkᵇ cont z z' refl)
              (True-irr (any? (λ t → t ≼? cont) (traces (lo i))) fl fl')
              (True-irr (any? (λ s → cont ≼? s) (traces (hi i))) cp cp')

------------------------------------------------------------------------
-- The frame.

histories : World mixed-two-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ᵇ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ᵇ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ᵇ-irrelevant {ρ}
  }
