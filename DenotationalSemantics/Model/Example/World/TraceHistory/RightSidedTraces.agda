------------------------------------------------------------------------
-- A trace-history Kripke frame for the (right) one-sided sets of      --
-- traces as the resource grades.                                      --
--                                                                    --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A resource grade `U` is a cap, so it reaches the histories      --
-- obtained by appending a continuation that stays within one of its    --
-- traces:                                                              --
--                                                                    --
--   w ⊑ʳ[ U ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                      --
--                          and  cont ≼ s   for some  s ∈ U            --
--                                                                    --
-- The relation is covariant along the Hoare lift, which is the grade   --
-- order, so a cap that permits more reaches more worlds. This is the   --
-- mirror of `TraceHistory.LeftSidedTraces`, and the cap half of        --
-- `TraceHistory.TwoSidedTraces`.                                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.RightSidedTraces
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op c

open import Syntax.Grades.Example.Traces.Subtrace.RightSided Op _≟ₒ_ c
  using (subtrace-right-sided; _≾_)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `cont` that stays
-- within some member of the cap.

infix 5 _⊑ʳ[_]_

record _⊑ʳ[_]_ (w : Trace) (U : NeTraces) (w' : Trace) : Set where
  constructor mkʳ
  field
    cont    : Trace                                    -- continuation
    cap     : True (any? (λ s → cont ≼? s) (traces U)) -- stays within the cap
    extends : w ∙ cont ≡ w'                            -- `w'` extends `w`

open _⊑ʳ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation stays
-- within the empty trace

⊑ʳ-refl : ∀ {w} → w ⊑ʳ[ u ] w
⊑ʳ-refl {w} =
  mkʳ ε
      (fromWitness {a? = any? (λ s → ε ≼? s) (traces u)} (here (≼-refl ε)))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two continuations;
-- monotonicity of the trace product carries both bounds across

⊑ʳ-trans : ∀ {U V w w' w''}
         → w ⊑ʳ[ U ] w' → w' ⊑ʳ[ V ] w'' → w ⊑ʳ[ U · V ] w''
⊑ʳ-trans {U} {V} {w} (mkʳ t₁ cp₁ eq₁) (mkʳ t₂ cp₂ eq₂)
  with find (toWitness cp₁) | find (toWitness cp₂)
... | x , x∈U , t₁≼x | y , y∈V , t₂≼y =
      mkʳ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼_) eq (mono-∙ t₁≼x t₂≼y))
                     (∈-cartesianProductWith⁺ _∙_ x∈U y∈V)))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: a cap that permits more reaches more worlds

⊑ʳ-mono : ∀ {U V w w'} → U ≾ V → w ⊑ʳ[ U ] w' → w ⊑ʳ[ V ] w'
⊑ʳ-mono {U} {V} h (mkʳ cont cp eq) = mkʳ cont (fromWitness cap') eq
  where
    cap' : Any (λ s → cont ≼ s) (traces V)
    cap' with find (toWitness cp)
    ... | s , s∈U , cont≼s
            with find (toWitness (h s (fromWitness s∈U)))
    ...     | s' , s'∈V , s≼s' =
              Any.map (λ e → subst (cont ≼_) e (≼-trans cont≼s s≼s')) s'∈V

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and both bounds are irrelevant proofs

⊑ʳ-irrelevant : ∀ {U w w'} → (p q : w ⊑ʳ[ U ] w') → p ≡ q
⊑ʳ-irrelevant {U} {w} (mkʳ cont cp refl) (mkʳ cont' cp' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkʳ cont z refl)
             (True-irr (any? (λ s → cont ≼? s) (traces U)) cp cp')

------------------------------------------------------------------------
-- The frame.

histories : World subtrace-right-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ʳ[_]_
  ; ⊑-refl        = ⊑ʳ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ʳ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ʳ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ʳ-irrelevant {ρ}
  }
