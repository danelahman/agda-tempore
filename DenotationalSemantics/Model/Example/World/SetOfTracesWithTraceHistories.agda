------------------------------------------------------------------------
-- A trace-history Kripke frame for (right-sided) sets of traces as the --
-- resource grades.                                                     --
--                                                                      --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A set-of-traces resource grade `P` reaches exactly the          --
-- histories obtained by appending a continuation trace `cont` that is  --
-- a member of the set `P`:                                             --
--                                                                      --
--   w ⊑ʰ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'   and   cont ∈ P      --
--                                                                      --
-- Multiplying grades (`_·_`, the language product) sequences the two   --
-- continuations, matching the concatenation of histories.             --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.SetOfTracesWithTraceHistories
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.SetOfTraces Op _≟ₒ_ using (right-sided-traces; _≾_)

open WithDecEq _≟ₒ_ using (_∈?_; True-irr)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `cont` that is a
-- member of the set of traces `P`.

infix 5 _⊑ʰ[_]_

record _⊑ʰ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkʰ
  field
    cont    : Trace                     -- the appended continuation
    member  : True (cont ∈? traces P)   -- it belongs to the set `P`
    extends : w ∙ cont ≡ w'             -- `w'` is `w` extended by `cont`

open _⊑ʰ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation, which
-- is the sole member of the unit set of traces

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ u ] w
⊑ʰ-refl {w} = mkʰ ε (fromWitness {a? = ε ∈? traces u} ε∈u) (∙-identityʳ w)
  where
    ε∈u : ε ∈ traces u
    ε∈u = here refl

-- transitivity multiplies the grades (the language product), sequencing
-- the two continuations; the sequenced continuation belongs to the
-- language product `P · Q`

⊑ʰ-trans : ∀ {P Q w w' w''}
         → w ⊑ʰ[ P ] w' → w' ⊑ʰ[ Q ] w'' → w ⊑ʰ[ P · Q ] w''
⊑ʰ-trans {P} {Q} {w} (mkʰ t₁ m₁ eq₁) (mkʰ t₂ m₂ eq₂) =
  mkʰ (t₁ ∙ t₂)
      (fromWitness
        (∈-cartesianProductWith⁺ _∙_ (toWitness m₁) (toWitness m₂)))
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: a larger set of traces gives a larger relation, since the
-- continuation's membership transports along the inclusion

⊑ʰ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ʰ[ P ] w' → w ⊑ʰ[ Q ] w'
⊑ʰ-mono rel (mkʰ cont m eq) = mkʰ cont (rel cont m) eq

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the membership witness is an irrelevant proof

⊑ʰ-irrelevant : ∀ {P w w'} → (p q : w ⊑ʰ[ P ] w') → p ≡ q
⊑ʰ-irrelevant {P} {w} (mkʰ cont m refl) (mkʰ cont' m' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl = cong (λ z → mkʰ cont z refl) (True-irr (cont ∈? traces P) m m')

------------------------------------------------------------------------
-- The frame.

histories : World right-sided-traces
histories = record
  { W             = Trace
  ; _⊑[_]_       = _⊑ʰ[_]_
  ; ⊑-refl       = ⊑ʰ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
