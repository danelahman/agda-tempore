------------------------------------------------------------------------
-- A trace-history Kripke frame for sets of traces ordered up to the   --
-- sub-trace preorder as the resource grades.                          --
--                                                                      --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A resource grade `P` reaches exactly the histories obtained by  --
-- appending a continuation trace `cont` that is a sub-trace of some    --
-- member of the set `P`:                                               --
--                                                                      --
--   w ⊑ᵗ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                       --
--                          and   cont ≼ t   for some   t ∈ P           --
--                                                                      --
-- Covering the continuation by a sub-trace of a member keeps the       --
-- relation covariant along the Hoare lift of the sub-trace preorder,   --
-- which is exactly the grade order.                                    --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.SetOfTracesUpToSubtraceWithTraceHistories
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Subtrace Op
open import Syntax.Grades.SetOfTracesUpToSubtrace Op _≟ₒ_
  using (traces-up-to-subtrace; _≾_)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `cont` that is a
-- sub-trace of some member of the set of traces `P`.

infix 5 _⊑ᵗ[_]_

record _⊑ᵗ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkᵗ
  field
    cont    : Trace                                          -- continuation
    covered : True (any? (λ t → cont ≼? t) (traces P))       -- ≼ some member
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ᵗ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation, which
-- is a sub-trace of the sole member `ε` of the unit set of traces

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} = mkᵗ ε (fromWitness {a? = any? (λ t → ε ≼? t) (traces u)} εcov)
                    (∙-identityʳ w)
  where
    εcov : Any (λ t → ε ≼ t) (traces u)
    εcov = here (≼-refl ε)

-- transitivity multiplies the grades (the language product), sequencing
-- the two continuations; monotonicity of the trace product covers the
-- sequenced continuation by the product of the two covering members

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} (mkᵗ t₁ cov₁ eq₁) (mkᵗ t₂ cov₂ eq₂)
  with find (toWitness cov₁) | find (toWitness cov₂)
... | a , a∈P , t₁≼a | b , b∈Q , t₂≼b =
      mkᵗ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼_) eq (mono-∙ t₁≼a t₂≼b))
                     (∈-cartesianProductWith⁺ _∙_ a∈P b∈Q)))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: a larger set (up to sub-traces) gives a larger relation,
-- since the covering member's sub-trace is again covered, by transitivity
-- of the sub-trace preorder

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {P} {Q} rel (mkᵗ cont cov eq)
  with find (toWitness cov)
... | t , t∈P , cont≼t
        with find (toWitness (rel t (fromWitness t∈P)))
...     | t' , t'∈Q , t≼t' =
          mkᵗ cont
              (fromWitness
                (Any.map (λ eq' → subst (cont ≼_) eq' (≼-trans cont≼t t≼t'))
                         t'∈Q))
              eq

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the covering witness is an irrelevant proof

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} (mkᵗ cont cov refl) (mkᵗ cont' cov' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkᵗ cont z refl)
             (True-irr (any? (λ t → cont ≼? t) (traces P)) cov cov')

------------------------------------------------------------------------
-- The frame.

histories : World traces-up-to-subtrace
histories = record
  { W             = Trace
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
  }
