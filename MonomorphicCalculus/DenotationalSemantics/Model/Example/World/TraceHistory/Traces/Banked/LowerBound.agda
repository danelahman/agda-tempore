------------------------------------------------------------------------
-- A trace-history Kripke frame for the trace grade of guarantees.    --
--                                                                    --
-- Worlds are timed traces: the history observed so far. A grade `P`  --
-- reaches the histories obtained by appending a continuation that    --
-- covers one of the listed guarantees:                               --
--                                                                    --
--   w ⊑ᵇ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                     --
--                          and  p ≼ᶜ cont   for some p ∈ P           --
--                                                                    --
-- The comparison runs in the opposite direction from that of the     --
-- frame of the cap: there the continuation is bounded, here it       --
-- covers. The frame records that a continuation performed the        --
-- operations a guarantee lists, which the tick frame, recording only --
-- their duration, does not.                                          --
--                                                                    --
-- Accessibility is the reading of the grade, and the frame           --
-- conditions are laws of the order: reflexivity is the empty run,    --
-- transitivity is monotonicity of the trace product, and covariance  --
-- is transitivity of the order.                                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Banked.LowerBound
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → ℕ) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Grades.Traces.Coverage ℕᵀ Op costˡᵒ
  using (_≼ᶜ_; ≼ᶜ-refl; ≼ᶜ-trans; mono-∙)
open import Grades.Traces.Coverage.Decidable ℕᵀ Op costˡᵒ
  using (module DecCoverage)

open import Grades.Examples.Traces.Banked.LowerBound
  ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (lower-bound; _≾_; Antichain; traces; 𝟏; _·_; Trace; _∙_; _·ˢ_;
         ∙-identityʳ; ∙-assoc; ∙-cancelˡ; ε; n-◃⁻; ◃-∈; True-irr)

open DecCoverage _≟ₒ_ using (_≼ᶜ?_)

open import MonomorphicCalculus.DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation that covers one of
-- the listed guarantees.

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (P : Antichain) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                          -- continuation
    covers  : True (any? (λ p → p ≼ᶜ? cont) (traces P))      -- covers some one
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ᵇ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation covers
-- the empty guarantee

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ 𝟏 ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = any? (λ p → p ≼ᶜ? ε) (traces 𝟏)} (here (≼ᶜ-refl ε)))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two
-- continuations; monotonicity of the trace product carries the
-- guarantee

⊑ᵇ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵇ[ P ] w' → w' ⊑ᵇ[ Q ] w'' → w ⊑ᵇ[ P · Q ] w''
⊑ᵇ-trans {P} {Q} {w} (mkᵇ t₁ w₁ eq₁) (mkᵇ t₂ w₂ eq₂)
  with find (toWitness w₁) | find (toWitness w₂)
... | a , a∈P , a≼t₁ | b , b∈Q , b≼t₂
        with find (n-◃⁻ (traces P ·ˢ traces Q)
                        (◃-∈ (∈-cartesianProductWith⁺ _∙_ a∈P b∈Q)))
...     | c , c∈PQ , c≼a∙b =
          mkᵇ (t₁ ∙ t₂)
              (fromWitness
                (Any.map (λ eq → subst (_≼ᶜ (t₁ ∙ t₂)) eq
                                   (≼ᶜ-trans c≼a∙b (mono-∙ a≼t₁ b≼t₂)))
                         c∈PQ))
              (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: the guarantee the continuation covered is itself weakened
-- by one of the weaker grade's, which the continuation therefore covers
-- too

⊑ᵇ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵇ[ P ] w' → w ⊑ᵇ[ Q ] w'
⊑ᵇ-mono {P} {Q} rel (mkᵇ cont wit eq) =
  mkᵇ cont (fromWitness covers') eq
  where
    covers' : Any (λ p → p ≼ᶜ cont) (traces Q)
    covers' with find (toWitness wit)
    ... | t , t∈P , t≼cont
            with find (toWitness (rel t (fromWitness t∈P)))
    ...     | t' , t'∈Q , t'≼t =
              Any.map (λ e → subst (_≼ᶜ cont) e (≼ᶜ-trans t'≼t t≼cont)) t'∈Q

-- proof irrelevance: the continuation is determined by left
-- cancellation, and the guarantee is an irrelevant proof

⊑ᵇ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵇ[ P ] w') → p ≡ q
⊑ᵇ-irrelevant {P} {w} (mkᵇ cont wit refl) (mkᵇ cont' wit' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkᵇ cont z refl)
             (True-irr (any? (λ p → p ≼ᶜ? cont) (traces P)) wit wit')

------------------------------------------------------------------------
-- The frame.

histories : World lower-bound
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {P} {Q} → ⊑ᵇ-trans {P} {Q}
  ; ⊑-mono        = λ {P} {Q} → ⊑ᵇ-mono {P} {Q}
  ; ⊑-irrelevant  = λ {P} → ⊑ᵇ-irrelevant {P}
  }
