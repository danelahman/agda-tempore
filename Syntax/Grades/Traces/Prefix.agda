------------------------------------------------------------------------
-- The prefix order on timed traces, and why it carries no grade.      --
--                                                                     --
-- The orders the trace grades are built from match one trace against   --
-- another as a *subsequence*: the events named must occur in order,     --
-- but others may occur in between. That is what lets a demand for       --
-- `read · ⟨ 2 ⟩ · send` be met by a run that also stores on the way,    --
-- and what lets a bound permit a run that skips what it offers.         --
--                                                                     --
-- The obvious strengthening is to ask for a *prefix*: the events must   --
-- happen from the start, with nothing skipped.                         --
--                                                                     --
--   s ⊑ᵖ t   iff   t ≡ s ∙ r   for some continuation r                --
--                                                                     --
-- This module defines that relation, proves it is a preorder, and then --
-- shows why it cannot be the comparison underlying a `Grade`: the      --
-- language product is not monotone for it on the left, which is        --
-- exactly the `·-monoˡ-≾` field. `Separation` exhibits the failure as  --
-- a checked term.                                                     --
--                                                                     --
-- The obstruction is not special to prefixes. Any order asking the     --
-- demanded events to be *contiguous* in the run fails the same way,    --
-- because sequencing two gap-free demands leaves a gap between them:   --
-- for the infix order, `a` is an infix of `a` and `a` of `b · a`, yet  --
-- `a · a` is no infix of `a · b · a`. Contiguity is simply not stable  --
-- under the language product, and monotonicity for that product is     --
-- what the grade construction needs.                                  --
--                                                                     --
-- So an order's tolerance of unmatched operations in the middle is not --
-- a looseness that could be tightened away; it is what makes the trace --
-- grades monoid-graded at all.                                        --
------------------------------------------------------------------------

open import Relation.Nullary using (¬_)

open import Util.Equality

module Syntax.Grades.Traces.Prefix (Op : Set) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)

open import Syntax.Grades.Traces.Base Op

------------------------------------------------------------------------
-- The relation

infix 4 _⊑ᵖ_

_⊑ᵖ_ : Trace → Trace → Set
s ⊑ᵖ t = Σ[ r ∈ Trace ] (s ∙ r ≡ t)

------------------------------------------------------------------------
-- It is a preorder

⊑ᵖ-refl : (s : Trace) → s ⊑ᵖ s
⊑ᵖ-refl s = ε , ∙-identityʳ s

⊑ᵖ-trans : {s t u : Trace} → s ⊑ᵖ t → t ⊑ᵖ u → s ⊑ᵖ u
⊑ᵖ-trans {s} (r , p) (r' , q) =
  r ∙ r' , trans (sym (∙-assoc s r r')) (trans (cong (_∙ r') p) q)

-- and the empty trace is below everything, as it is for `_≼_`

ε-⊑ᵖ : (t : Trace) → ε ⊑ᵖ t
ε-⊑ᵖ t = t , ∙-identityˡ t

------------------------------------------------------------------------
-- Left multiplication is fine
--
-- Extending both sides by a common *prefix* preserves the relation:
-- the continuation is untouched. It is the other side that fails.

⊑ᵖ-monoʳ : {s s' : Trace} → (u : Trace) → s ⊑ᵖ s' → (u ∙ s) ⊑ᵖ (u ∙ s')
⊑ᵖ-monoʳ {s} u (r , p) = r , trans (∙-assoc u s r) (cong (u ∙_) p)

------------------------------------------------------------------------
-- Right multiplication is not
--
-- Extending both sides by a common *suffix* does not preserve the
-- relation, because the suffix lands after the part that differs. Two
-- distinct operations are enough to see it, with the empty demand on
-- the left: `ε` is a prefix of `a`, yet appending `b` to both gives
-- `b` against `a ∙ b`, and the very first event already disagrees.

module Separation (a b : Op) (a≢b : ¬ (a ≡ b)) where

  -- the heads of two equal operation traces agree

  op-head : {o o' : Op} {s s' : Trace}
          → operation o s ≡ operation o' s' → o ≡ o'
  op-head refl = refl

  -- `ε` is a prefix of `⌈ a ⌉`

  ε-before-a : ε ⊑ᵖ ⌈ a ⌉
  ε-before-a = ε-⊑ᵖ ⌈ a ⌉

  -- but `⌈ b ⌉` is not a prefix of `⌈ a ⌉ ∙ ⌈ b ⌉`

  b-not-before-ab : ¬ (⌈ b ⌉ ⊑ᵖ (⌈ a ⌉ ∙ ⌈ b ⌉))
  b-not-before-ab (r , p) = a≢b (sym (op-head {b} {a} {r} {⌈ b ⌉} p))

  -- so the language product is not monotone on the left, which is
  -- precisely the `·-monoˡ-≾` field of `Grade`. No grade can be built
  -- over the prefix order by the construction the trace grades use.

  ¬-monoˡ : ¬ ({s s' : Trace} → (t : Trace) → s ⊑ᵖ s' → (s ∙ t) ⊑ᵖ (s' ∙ t))
  ¬-monoˡ mono = b-not-before-ab (mono {ε} {⌈ a ⌉} ⌈ b ⌉ ε-before-a)
