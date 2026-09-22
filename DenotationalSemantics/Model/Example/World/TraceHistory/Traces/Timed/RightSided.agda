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
--                                                                    --
-- The grade's `unbounded` lists no bound, so it leaves the            --
-- continuation unconstrained and asks only that `w'` extend `w`.      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Allowance Op costʰⁱ
  using (_≼ᵃ_; ≼ᵃ-refl; ≼ᵃ-trans; mono-∙)
open import Syntax.Grades.Traces.Allowance.Decidable Op costʰⁱ
  using (module DecAllowance)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (right-sided; Bounds; within_; unbounded; _·ᵇ_; _≾_;
         Trace; ε; traces; u; _∙_; _·ˢ_; ∙-assoc; ∙-identityʳ; ∙-cancelˡ;
         n-◃⁻; ◃-∈; True-irr)

open DecAllowance _≟ₒ_ using (_≼ᵃ?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation that stays within one
-- of the listed bounds.

-- the condition on the continuation, vacuous at `unbounded`

Within : Trace → Bounds → Set
Within cont (within P) = True (any? (λ p → cont ≼ᵃ? p) (traces P))
Within cont unbounded       = ⊤

Within-irr : {cont : Trace} {P : Bounds} → (p q : Within cont P) → p ≡ q
Within-irr {cont} {within P} = True-irr (any? (λ p → cont ≼ᵃ? p) (traces P))
Within-irr {_}    {unbounded}    tt tt = refl

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (P : Bounds) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                      -- continuation
    bounded : Within cont P                              -- within some bound
    extends : w ∙ cont ≡ w'                              -- `w'` extends `w`

open _⊑ᵇ[_]_

-- appending the two continuations in turn extends across both

extends-∙ : (w t₁ t₂ : Trace) {w' w'' : Trace}
          → w ∙ t₁ ≡ w' → w' ∙ t₂ ≡ w'' → w ∙ (t₁ ∙ t₂) ≡ w''
extends-∙ w t₁ t₂ eq₁ eq₂ =
  trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂)

-- reflexivity at the unit grade `{ ε }`: the empty continuation stays
-- within the empty bound

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ (within u) ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = any? (λ p → ε ≼ᵃ? p) (traces u)} (here (≼ᵃ-refl ε)))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the two
-- continuations; monotonicity of the trace product carries the bound

⊑ᵇ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵇ[ P ] w' → w' ⊑ᵇ[ Q ] w'' → w ⊑ᵇ[ P ·ᵇ Q ] w''
⊑ᵇ-trans {within _} {unbounded}    {w} (mkᵇ t₁ _ eq₁) (mkᵇ t₂ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {unbounded}    {_}      {w} (mkᵇ t₁ _ eq₁) (mkᵇ t₂ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {within P} {within Q} {w} (mkᵇ t₁ w₁ eq₁) (mkᵇ t₂ w₂ eq₂)
  with find (toWitness w₁) | find (toWitness w₂)
... | a , a∈P , t₁≼a | b , b∈Q , t₂≼b
        with find (n-◃⁻ (traces P ·ˢ traces Q)
                        (◃-∈ (∈-cartesianProductWith⁺ _∙_ a∈P b∈Q)))
...     | c , c∈PQ , a∙b≼c =
          mkᵇ (t₁ ∙ t₂)
              (fromWitness
                (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼ᵃ_) eq
                                   (≼ᵃ-trans (mono-∙ t₁≼a t₂≼b) a∙b≼c))
                         c∈PQ))
              (extends-∙ w t₁ t₂ eq₁ eq₂)

-- covariance: the bound the continuation stayed within itself stays
-- within one of the weaker grade's

⊑ᵇ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵇ[ P ] w' → w ⊑ᵇ[ Q ] w'
⊑ᵇ-mono {_}      {unbounded}    rel (mkᵇ cont _ eq) = mkᵇ cont tt eq
⊑ᵇ-mono {unbounded}    {within _} ()
⊑ᵇ-mono {within P} {within Q} rel (mkᵇ cont wit eq) =
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
... | refl = cong (λ z → mkᵇ cont z refl) (Within-irr {cont} {P} wit wit')

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
