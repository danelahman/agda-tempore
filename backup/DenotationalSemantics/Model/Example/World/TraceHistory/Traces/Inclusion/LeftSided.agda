------------------------------------------------------------------------
-- A trace-history Kripke frame for the inclusion-ordered floors.      --
--                                                                    --
-- Worlds are timed traces `Trace`. A resource grade `P` reaches the    --
-- histories obtained by appending a continuation that is *every* run   --
-- the grade lists:                                                    --
--                                                                    --
--   w ⊑ʰ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                      --
--                          and   cont ≡ t   for every   t ∈ P         --
--                                                                    --
-- The quantifier is universal because `Inclusion.LeftSided`'s order    --
-- runs over the right-hand set: weakening drops requirements, so what  --
-- carries across is having met all of them.                           --
--                                                                    --
-- Being an equality rather than a covering, the condition is only      --
-- inhabited when the grade's runs coincide -- a one-element floor, in  --
-- effect. That is not a defect of the frame but of what an exact       --
-- floor can ask for: `Inclusion` never consults the sub-trace preorder --
-- and so has no slack to spend on distinct alternatives. The frame     --
-- laws hold regardless, which is what this module checks.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Inclusion.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Example.Traces.Inclusion.LeftSided Op _≟ₒ_
  using (inclusion-left-sided; _≾_)

open WithDecEq _≟ₒ_ using (_∈?_; _≟ᵀ_; True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories

infix 5 _⊑ʰ[_]_

record _⊑ʰ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkʰ
  field
    cont    : Trace                                          -- continuation
    is-each : True (all? (λ t → cont ≟ᵀ t) (traces P))       -- is every listed run
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ʰ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation is the
-- sole listed run

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ u ] w
⊑ʰ-refl {w} = mkʰ ε (fromWitness {a? = all? (λ t → ε ≟ᵀ t) (traces u)}
                                 (refl All.∷ All.[]))
                    (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two continuations;
-- each sequenced run is the sequence of the two it came from

⊑ʰ-trans : ∀ {P Q w w' w''}
         → w ⊑ʰ[ P ] w' → w' ⊑ʰ[ Q ] w'' → w ⊑ʰ[ P · Q ] w''
⊑ʰ-trans {P} {Q} {w} (mkʰ t₁ e₁ eq₁) (mkʰ t₂ e₂ eq₂) =
  mkʰ (t₁ ∙ t₂)
      (fromWitness (All.tabulate step))
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    step : ∀ {r} → r ∈ (traces P ·ˢ traces Q) → (t₁ ∙ t₂) ≡ r
    step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) r∈
    ... | a , b , a∈P , b∈Q , refl =
          cong₂ _∙_ (All.lookup (toWitness e₁) a∈P)
                    (All.lookup (toWitness e₂) b∈Q)

-- covariance: a grade requiring fewer runs gives a larger relation.
-- Every run `Q` requires is one `P` requires, and the continuation is
-- already that.

⊑ʰ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ʰ[ P ] w' → w ⊑ʰ[ Q ] w'
⊑ʰ-mono {P} {Q} rel (mkʰ cont e eq) =
  mkʰ cont (fromWitness (All.tabulate step)) eq
  where
    step : ∀ {q} → q ∈ traces Q → cont ≡ q
    step {q} q∈Q
      with find (toWitness (rel q (fromWitness q∈Q)))
    ... | p , p∈P , q≡p = trans (All.lookup (toWitness e) p∈P) (sym q≡p)

-- proof irrelevance of the witnesses

⊑ʰ-irrelevant : ∀ {P w w'} → (p q : w ⊑ʰ[ P ] w') → p ≡ q
⊑ʰ-irrelevant {P} {w} (mkʰ cont e refl) (mkʰ cont' e' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkʰ cont z refl)
             (True-irr (all? (λ t → cont ≟ᵀ t) (traces P)) e e')

------------------------------------------------------------------------
-- The frame.

histories : World inclusion-left-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ʰ[_]_
  ; ⊑-refl        = ⊑ʰ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
