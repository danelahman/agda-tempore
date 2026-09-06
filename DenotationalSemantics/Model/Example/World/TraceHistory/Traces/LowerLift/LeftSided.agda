------------------------------------------------------------------------
-- A trace-history Kripke frame for sets of traces ordered up to the   --
-- sub-trace preorder as the resource grades.                          --
--                                                                      --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A resource grade `P` reaches the histories obtained by          --
-- appending a continuation trace `cont` that does at least what every  --
-- member of the set `P` asks for:                                      --
--                                                                      --
--   w ⊑ʰ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                       --
--                          and   t ≼ cont   for every   t ∈ P          --
--                                                                      --
-- Reading `P` as a floor under what must have happened, rather than a  --
-- cap on what may, is what keeps the relation covariant along the      --
-- grade order. The quantifier is universal because that order          --
-- (`LowerLift.LeftSided`) compares its two sets *exchanged*: weakening  --
-- a floor replaces each of its demands by one already covered, so what --
-- carries over is having covered all of them, not one of them.         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.LowerLift.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op c
open import Syntax.Grades.Example.Traces.LowerLift.LeftSided Op _≟ₒ_ c
  using (lower-lift-left-sided; _≾_)

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
    covered : True (all? (λ t → t ≼? cont) (traces P))       -- covers every member
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ʰ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation, which
-- already covers the sole member `ε` of the unit set of traces

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ u ] w
⊑ʰ-refl {w} = mkʰ ε (fromWitness {a? = all? (λ t → t ≼? ε) (traces u)}
                                 (≼-refl ε All.∷ All.[]))
                    (∙-identityʳ w)

-- transitivity multiplies the grades (the language product), sequencing
-- the two continuations; monotonicity of the trace product has each
-- sequenced member inside the sequenced continuation

⊑ʰ-trans : ∀ {P Q w w' w''}
         → w ⊑ʰ[ P ] w' → w' ⊑ʰ[ Q ] w'' → w ⊑ʰ[ P · Q ] w''
⊑ʰ-trans {P} {Q} {w} (mkʰ t₁ cov₁ eq₁) (mkʰ t₂ cov₂ eq₂) =
  mkʰ (t₁ ∙ t₂)
      (fromWitness (All.tabulate step))
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    step : ∀ {r} → r ∈ (traces P ·ˢ traces Q) → r ≼ (t₁ ∙ t₂)
    step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) r∈
    ... | a , b , a∈P , b∈Q , refl =
          mono-∙ (All.lookup (toWitness cov₁) a∈P)
                 (All.lookup (toWitness cov₂) b∈Q)

-- covariance: a grade that asks for less gives a larger relation. Each
-- member of `Q` sits inside one of `P`'s, which the continuation
-- already covers, so transitivity of the sub-trace preorder carries it.

⊑ʰ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ʰ[ P ] w' → w ⊑ʰ[ Q ] w'
⊑ʰ-mono {P} {Q} rel (mkʰ cont cov eq) =
  mkʰ cont (fromWitness (All.tabulate step)) eq
  where
    step : ∀ {t'} → t' ∈ traces Q → t' ≼ cont
    step {t'} t'∈Q
      with find (toWitness (rel t' (fromWitness t'∈Q)))
    ... | t , t∈P , t'≼t =
          ≼-trans t'≼t (All.lookup (toWitness cov) t∈P)

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the covering witness is an irrelevant proof

⊑ʰ-irrelevant : ∀ {P w w'} → (p q : w ⊑ʰ[ P ] w') → p ≡ q
⊑ʰ-irrelevant {P} {w} (mkʰ cont cov refl) (mkʰ cont' cov' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong (λ z → mkʰ cont z refl)
             (True-irr (all? (λ t → t ≼? cont) (traces P)) cov cov')

------------------------------------------------------------------------
-- The frame.

histories : World lower-lift-left-sided
histories = record
  { W             = Trace
  ; _⊑[_]_       = _⊑ʰ[_]_
  ; ⊑-refl       = ⊑ʰ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
