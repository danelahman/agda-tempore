------------------------------------------------------------------------
-- A trace-history Kripke frame for (right-sided) sets of traces as the --
-- resource grades.                                                     --
--                                                                      --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A set-of-traces resource grade `P` reaches exactly the          --
-- histories obtained by appending a continuation trace `cont` that is  --
-- a member of the set `P`:                                             --
--                                                                      --
--   w ⊑ᵗ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'   and   cont ∈ P      --
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

infix 5 _⊑ᵗ[_]_

record _⊑ᵗ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkᵗ
  field
    cont    : Trace                     -- the appended continuation
    member  : True (cont ∈? traces P)   -- it belongs to the set `P`
    extends : w ∙ cont ≡ w'             -- `w'` is `w` extended by `cont`

open _⊑ᵗ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation, which
-- is the sole member of the unit set of traces

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} = mkᵗ ε (fromWitness {a? = ε ∈? traces u} ε∈u) (∙-identityʳ w)
  where
    ε∈u : ε ∈ traces u
    ε∈u = here refl

-- transitivity multiplies the grades (the language product), sequencing
-- the two continuations; the sequenced continuation belongs to the
-- language product `P · Q`

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} (mkᵗ t₁ m₁ eq₁) (mkᵗ t₂ m₂ eq₂) =
  mkᵗ (t₁ ∙ t₂)
      (fromWitness
        (∈-cartesianProductWith⁺ _∙_ (toWitness m₁) (toWitness m₂)))
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: a larger set of traces gives a larger relation, since the
-- continuation's membership transports along the inclusion

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono rel (mkᵗ cont m eq) = mkᵗ cont (rel cont m) eq

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the membership witness is an irrelevant proof

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} (mkᵗ cont m refl) (mkᵗ cont' m' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl = cong (λ z → mkᵗ cont z refl) (True-irr (cont ∈? traces P) m m')

------------------------------------------------------------------------
-- The frame.

histories : World right-sided-traces
histories = record
  { W             = Trace
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ᵗ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ᵗ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ᵗ-irrelevant {ρ}
  }
