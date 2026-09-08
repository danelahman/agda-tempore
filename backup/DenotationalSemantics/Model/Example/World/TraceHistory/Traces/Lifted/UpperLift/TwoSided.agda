------------------------------------------------------------------------
-- A trace-history Kripke frame for two-sided Smyth-lift trace          --
-- intervals as the resource grades.                                    --
--                                                                    --
-- Worlds are timed traces `Trace`. A resource grade `[ L , U ]` reaches --
-- the histories obtained by appending a continuation `cont` bounded on  --
-- both sides:                                                         --
--                                                                    --
--   w ⊑ᵇ[ [ L , U ] ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'              --
--                                  and  t ≼ cont   for some  t ∈ L    --
--                                  and  cont ≼ s   for every  s ∈ U   --
--                                                                    --
-- Exactly the mirror of `LowerLift.TwoSided`'s frame, whose floor is    --
-- universal and whose cap is existential. The quantifiers swap because  --
-- the two columns quantify over opposite sets: at each endpoint the     --
-- frame is existential when the order runs over the source set and      --
-- universal when it runs over the target, and the Smyth lift reverses   --
-- which is which.                                                     --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.UpperLift.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open Order.TraceOrder O

open import Syntax.Grades.Example.Traces.Lifted.UpperLift.TwoSided Op _≟ₒ_ O
  using (UpperInterval; lo; hi; upper-lift-two-sided; _≾ᵘⁱ_; _·ᵘⁱ_; uᵘⁱ)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation that covers some
-- member of the floor and fits inside every member of the cap.

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (i : UpperInterval) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                            -- continuation
    floor   : True (any? (λ t → t ≼? cont) (traces (lo i)))    -- covers some floor member
    cap     : True (all? (λ s → cont ≼? s) (traces (hi i)))    -- within every cap member
    extends : w ∙ cont ≡ w'                                    -- `w'` extends `w`

open _⊑ᵇ[_]_

-- reflexivity at the unit grade `[ { ε } , { ε } ]`: the empty
-- continuation both covers and is covered by the empty trace

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ uᵘⁱ ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = any? (λ t → t ≼? ε) (traces u)} (here (≼-refl ε)))
      (fromWitness {a? = all? (λ s → ε ≼? s) (traces u)}
                   (≼-refl ε All.∷ All.[]))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two continuations;
-- monotonicity of the trace product carries both bounds across

⊑ᵇ-trans : ∀ {i j w w' w''}
         → w ⊑ᵇ[ i ] w' → w' ⊑ᵇ[ j ] w'' → w ⊑ᵇ[ i ·ᵘⁱ j ] w''
⊑ᵇ-trans {i} {j} {w} (mkᵇ t₁ fl₁ cp₁ eq₁) (mkᵇ t₂ fl₂ cp₂ eq₂)
  with find (toWitness fl₁) | find (toWitness fl₂)
... | a , a∈L , a≼t₁ | b , b∈L' , b≼t₂ =
      mkᵇ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst (_≼ (t₁ ∙ t₂)) eq (mono-∙ a≼t₁ b≼t₂))
                     (∈-cartesianProductWith⁺ _∙_ a∈L b∈L')))
          (fromWitness (All.tabulate cap-step))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    cap-step : ∀ {r} → r ∈ (traces (hi i) ·ˢ traces (hi j))
             → (t₁ ∙ t₂) ≼ r
    cap-step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces (hi i)) (traces (hi j)) r∈
    ... | x , y , x∈U , y∈U' , refl =
          mono-∙ (All.lookup (toWitness cp₁) x∈U)
                 (All.lookup (toWitness cp₂) y∈U')

-- covariance: the floor half travels existentially -- the covered
-- member has a weaker one in the larger grade -- and the cap half
-- universally, each allowance of the larger grade having one of the
-- smaller inside it

⊑ᵇ-mono : ∀ {i j w w'} → i ≾ᵘⁱ j → w ⊑ᵇ[ i ] w' → w ⊑ᵇ[ j ] w'
⊑ᵇ-mono {i} {j} (l , h) (mkᵇ cont fl cp eq) =
  mkᵇ cont (fromWitness floor') (fromWitness (All.tabulate cap-step)) eq
  where
    floor' : Any (λ t → t ≼ cont) (traces (lo j))
    floor' with find (toWitness fl)
    ... | t , t∈L , t≼cont
            with find (toWitness (l t (fromWitness t∈L)))
    ...     | t' , t'∈L' , t'≼t =
              Any.map (λ e → subst (_≼ cont) e (≼-trans t'≼t t≼cont)) t'∈L'

    cap-step : ∀ {s} → s ∈ traces (hi j) → cont ≼ s
    cap-step {s} s∈U'
      with find (toWitness (h s (fromWitness s∈U')))
    ... | r , r∈U , r≼s = ≼-trans (All.lookup (toWitness cp) r∈U) r≼s

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and both bounds are irrelevant proofs

⊑ᵇ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵇ[ i ] w') → p ≡ q
⊑ᵇ-irrelevant {i} {w} (mkᵇ cont fl cp refl) (mkᵇ cont' fl' cp' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong₂ (λ z z' → mkᵇ cont z z' refl)
              (True-irr (any? (λ t → t ≼? cont) (traces (lo i))) fl fl')
              (True-irr (all? (λ s → cont ≼? s) (traces (hi i))) cp cp')

------------------------------------------------------------------------
-- The frame.

histories : World upper-lift-two-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ᵇ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ᵇ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ᵇ-irrelevant {ρ}
  }
