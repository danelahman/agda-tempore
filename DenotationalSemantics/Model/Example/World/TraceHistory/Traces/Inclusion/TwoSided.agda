------------------------------------------------------------------------
-- A trace-history Kripke frame for two-sided inclusion intervals.     --
--                                                                    --
-- Worlds are timed traces `Trace`. A resource grade `[ L , U ]` reaches --
-- the histories obtained by appending a continuation that is every run  --
-- the floor requires and one of the runs the cap permits:              --
--                                                                    --
--   w ⊑ᵇ[ [ L , U ] ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'              --
--                                  and  cont ≡ t   for every  t ∈ L   --
--                                  and  cont ≡ s   for some   s ∈ U   --
--                                                                    --
-- The two quantifiers differ for the reason they do throughout the      --
-- grid: the floor's order runs over the target set and the cap's over   --
-- the source, so the floor condition is universal and the cap's         --
-- existential. This is `LowerLift.TwoSided`'s frame with `_≼_`          --
-- replaced by `_≡_` -- which is the whole of what the `Inclusion`       --
-- column is.                                                          --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Inclusion.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op

open import Syntax.Grades.Example.Traces.Inclusion.TwoSided Op _≟ₒ_
  using (InclusionInterval; lo; hi; inclusion-two-sided;
         _≾ⁱⁱ_; _·ⁱⁱ_; uⁱⁱ)

open WithDecEq _≟ₒ_ using (_∈?_; _≟ᵀ_; True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (i : InclusionInterval) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                             -- continuation
    floor   : True (all? (λ t → cont ≟ᵀ t) (traces (lo i)))     -- is every required run
    cap     : True (any? (λ s → cont ≟ᵀ s) (traces (hi i)))     -- is some permitted run
    extends : w ∙ cont ≡ w'                                     -- `w'` extends `w`

open _⊑ᵇ[_]_

-- reflexivity at the unit grade `[ { ε } , { ε } ]`

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ uⁱⁱ ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = all? (λ t → ε ≟ᵀ t) (traces u)} (refl All.∷ All.[]))
      (fromWitness {a? = any? (λ s → ε ≟ᵀ s) (traces u)} (here refl))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two continuations

⊑ᵇ-trans : ∀ {i j w w' w''}
         → w ⊑ᵇ[ i ] w' → w' ⊑ᵇ[ j ] w'' → w ⊑ᵇ[ i ·ⁱⁱ j ] w''
⊑ᵇ-trans {i} {j} {w} (mkᵇ t₁ fl₁ cp₁ eq₁) (mkᵇ t₂ fl₂ cp₂ eq₂)
  with find (toWitness cp₁) | find (toWitness cp₂)
... | x , x∈U , t₁≡x | y , y∈U' , t₂≡y =
      mkᵇ (t₁ ∙ t₂)
          (fromWitness (All.tabulate floor-step))
          (fromWitness
            (Any.map (λ eq → trans (cong₂ _∙_ t₁≡x t₂≡y) eq)
                     (∈-cartesianProductWith⁺ _∙_ x∈U y∈U')))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    floor-step : ∀ {r} → r ∈ (traces (lo i) ·ˢ traces (lo j))
               → (t₁ ∙ t₂) ≡ r
    floor-step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces (lo i)) (traces (lo j)) r∈
    ... | a , b , a∈L , b∈L' , refl =
          cong₂ _∙_ (All.lookup (toWitness fl₁) a∈L)
                    (All.lookup (toWitness fl₂) b∈L')

-- covariance: the floor may drop requirements and the cap may gain
-- permissions, each half read through its own inclusion

⊑ᵇ-mono : ∀ {i j w w'} → i ≾ⁱⁱ j → w ⊑ᵇ[ i ] w' → w ⊑ᵇ[ j ] w'
⊑ᵇ-mono {i} {j} (l , h) (mkᵇ cont fl cp eq) =
  mkᵇ cont (fromWitness (All.tabulate floor-step)) (fromWitness cap') eq
  where
    floor-step : ∀ {q} → q ∈ traces (lo j) → cont ≡ q
    floor-step {q} q∈L'
      with find (toWitness (l q (fromWitness q∈L')))
    ... | p , p∈L , q≡p = trans (All.lookup (toWitness fl) p∈L) (sym q≡p)

    cap' : Any (λ s → cont ≡ s) (traces (hi j))
    cap' with find (toWitness cp)
    ... | s , s∈U , cont≡s
            with find (toWitness (h s (fromWitness s∈U)))
    ...     | s' , s'∈U' , s≡s' =
              Any.map (trans (trans cont≡s s≡s')) s'∈U'

-- proof irrelevance of the witnesses

⊑ᵇ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵇ[ i ] w') → p ≡ q
⊑ᵇ-irrelevant {i} {w} (mkᵇ cont fl cp refl) (mkᵇ cont' fl' cp' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong₂ (λ z z' → mkᵇ cont z z' refl)
              (True-irr (all? (λ t → cont ≟ᵀ t) (traces (lo i))) fl fl')
              (True-irr (any? (λ s → cont ≟ᵀ s) (traces (hi i))) cp cp')

------------------------------------------------------------------------
-- The frame.

histories : World inclusion-two-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ᵇ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ᵇ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ᵇ-irrelevant {ρ}
  }
