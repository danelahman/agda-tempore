------------------------------------------------------------------------
-- A trace-history Kripke frame for two-sided trace intervals as the   --
-- resource grades.                                                    --
--                                                                    --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A resource grade `[ L , U ]` reaches the histories obtained by  --
-- appending a continuation `cont` that is bounded on both sides by     --
-- the sub-trace preorder:                                             --
--                                                                    --
--   w ⊑ᵇ[ [ L , U ] ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'              --
--                                  and  t ≼ cont   for every t ∈ L    --
--                                  and  cont ≼ s   for some  s ∈ U    --
--                                                                    --
-- The two quantifiers differ because the grade compares its endpoints  --
-- in opposite directions: weakening replaces each floor demand by one  --
-- already covered, so all of them must be met, while it replaces some  --
-- cap allowance by a larger one, so one suffices. `⊑-mono` therefore   --
-- consumes one half of the order per half of the relation. This is     --
-- the trace-level counterpart of                                       --
-- `TraceHistory.TwoSidedIntervals`, whose two conditions bound         --
-- `duration cont` between `min i` and `max i`.                         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.LowerLift.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op c
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ c using (_≼ˢ_; _≽ˢ_)

open import Syntax.Grades.Example.Traces.LowerLift.TwoSided Op _≟ₒ_ c
  using (TraceInterval; lo; hi; lower-lift-two-sided; _≾ᵗⁱ_; _·ᵗⁱ_; uᵗⁱ)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `cont` that covers
-- some member of the floor and fits inside some member of the cap.

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (i : TraceInterval) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                            -- continuation
    floor   : True (all? (λ t → t ≼? cont) (traces (lo i)))    -- covers every floor member
    cap     : True (any? (λ s → cont ≼? s) (traces (hi i)))    -- fits in some cap member
    extends : w ∙ cont ≡ w'                                    -- `w'` extends `w`

open _⊑ᵇ[_]_

-- reflexivity at the unit grade `[ { ε } , { ε } ]`: the empty
-- continuation both covers and is covered by the empty trace

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ uᵗⁱ ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = all? (λ t → t ≼? ε) (traces u)}
                   (≼-refl ε All.∷ All.[]))
      (fromWitness {a? = any? (λ s → ε ≼? s) (traces u)} (here (≼-refl ε)))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two continuations;
-- monotonicity of the trace product carries both bounds across

⊑ᵇ-trans : ∀ {i j w w' w''}
         → w ⊑ᵇ[ i ] w' → w' ⊑ᵇ[ j ] w'' → w ⊑ᵇ[ i ·ᵗⁱ j ] w''
⊑ᵇ-trans {i} {j} {w} (mkᵇ t₁ fl₁ cp₁ eq₁) (mkᵇ t₂ fl₂ cp₂ eq₂)
  with find (toWitness cp₁) | find (toWitness cp₂)
... | x , x∈U , t₁≼x | y , y∈U' , t₂≼y =
      mkᵇ (t₁ ∙ t₂)
          (fromWitness (All.tabulate floor-step))
          (fromWitness
            (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼_) eq (mono-∙ t₁≼x t₂≼y))
                     (∈-cartesianProductWith⁺ _∙_ x∈U y∈U')))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    floor-step : ∀ {r} → r ∈ (traces (lo i) ·ˢ traces (lo j))
               → r ≼ (t₁ ∙ t₂)
    floor-step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces (lo i)) (traces (lo j)) r∈
    ... | a , b , a∈L , b∈L' , refl =
          mono-∙ (All.lookup (toWitness fl₁) a∈L)
                 (All.lookup (toWitness fl₂) b∈L')

-- covariance: the floor half travels along the Smyth lift on `lo`, the
-- cap half along the Hoare lift on `hi`

⊑ᵇ-mono : ∀ {i j w w'} → i ≾ᵗⁱ j → w ⊑ᵇ[ i ] w' → w ⊑ᵇ[ j ] w'
⊑ᵇ-mono {i} {j} (l , h) (mkᵇ cont fl cp eq) =
  mkᵇ cont (fromWitness floor') (fromWitness cap') eq
  where
    floor' : All (λ t → t ≼ cont) (traces (lo j))
    floor' = All.tabulate step
      where
        step : ∀ {t'} → t' ∈ traces (lo j) → t' ≼ cont
        step {t'} t'∈L'
          with find (toWitness (l t' (fromWitness t'∈L')))
        ... | t , t∈L , t'≼t = ≼-trans t'≼t (All.lookup (toWitness fl) t∈L)

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
              (True-irr (all? (λ t → t ≼? cont) (traces (lo i))) fl fl')
              (True-irr (any? (λ s → cont ≼? s) (traces (hi i))) cp cp')

------------------------------------------------------------------------
-- The frame.

histories : World lower-lift-two-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ᵇ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ᵇ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ᵇ-irrelevant {ρ}
  }
