------------------------------------------------------------------------
-- A trace-history Kripke frame for sets of traces ordered up to the   --
-- sub-trace preorder as the resource grades.                          --
--                                                                      --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A resource grade `P` reaches the histories obtained by          --
-- appending a continuation trace `cont` that does at least what some   --
-- member of the set `P` asks for:                                      --
--                                                                      --
--   w ⊑ʰ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                       --
--                          and   t ≼ cont   for some   t ∈ P           --
--                                                                      --
-- Reading `P` as a floor under what must have happened, rather than a  --
-- cap on what may, is what keeps the relation covariant along the      --
-- Smyth lift of the sub-trace preorder, which is the grade order.      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.LeftSidedTraces
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op c
open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ c
  using (left-sided-traces; _≾_)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `cont` that has some
-- member of the set of traces `P` inside it.

infix 5 _⊑ʰ[_]_

record _⊑ʰ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkʰ
  field
    cont    : Trace                                          -- continuation
    covered : True (any? (λ t → t ≼? cont) (traces P))       -- covers a member
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ʰ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation, which
-- already covers the sole member `ε` of the unit set of traces

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ u ] w
⊑ʰ-refl {w} = mkʰ ε (fromWitness {a? = any? (λ t → t ≼? ε) (traces u)} εcov)
                    (∙-identityʳ w)
  where
    εcov : Any (λ t → t ≼ ε) (traces u)
    εcov = here (≼-refl ε)

-- transitivity multiplies the grades (the language product), sequencing
-- the two continuations; monotonicity of the trace product has the
-- product of the two covered members inside the sequenced continuation

⊑ʰ-trans : ∀ {P Q w w' w''}
         → w ⊑ʰ[ P ] w' → w' ⊑ʰ[ Q ] w'' → w ⊑ʰ[ P · Q ] w''
⊑ʰ-trans {P} {Q} {w} (mkʰ t₁ cov₁ eq₁) (mkʰ t₂ cov₂ eq₂)
  with find (toWitness cov₁) | find (toWitness cov₂)
... | a , a∈P , a≼t₁ | b , b∈Q , b≼t₂ =
      mkʰ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst (_≼ (t₁ ∙ t₂)) eq (mono-∙ a≼t₁ b≼t₂))
                     (∈-cartesianProductWith⁺ _∙_ a∈P b∈Q)))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: a grade that asks for less gives a larger relation, since
-- a member sitting inside the covered one sits inside the continuation
-- too, by transitivity of the sub-trace preorder

⊑ʰ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ʰ[ P ] w' → w ⊑ʰ[ Q ] w'
⊑ʰ-mono {P} {Q} rel (mkʰ cont cov eq)
  with find (toWitness cov)
... | t , t∈P , t≼cont
        with find (toWitness (rel t (fromWitness t∈P)))
...     | t' , t'∈Q , t'≼t =
          mkʰ cont
              (fromWitness
                (Any.map (λ eq' → subst (_≼ cont) eq' (≼-trans t'≼t t≼cont))
                         t'∈Q))
              eq

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the covering witness is an irrelevant proof

⊑ʰ-irrelevant : ∀ {P w w'} → (p q : w ⊑ʰ[ P ] w') → p ≡ q
⊑ʰ-irrelevant {P} {w} (mkʰ cont cov refl) (mkʰ cont' cov' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkʰ cont z refl)
             (True-irr (any? (λ t → t ≼? cont) (traces P)) cov cov')

------------------------------------------------------------------------
-- The frame.

histories : World left-sided-traces
histories = record
  { W             = Trace
  ; _⊑[_]_       = _⊑ʰ[_]_
  ; ⊑-refl       = ⊑ʰ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
