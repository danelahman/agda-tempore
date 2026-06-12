------------------------------------------------------------------------------
-- Example grade system of (non-empty) sets of timed traces over all        --
-- operations as effect grades and sets of timed traces over a sub-alphabet --
-- of operation names (picked out by a predicate) as resource grades.       --
------------------------------------------------------------------------------

open import Data.Bool
open import Data.List
open import Data.Unit using (tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.GradeSystem.TracesToRestrictedTraces (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

module _ (OpPred : Op → Bool) where

  -- the restriction of traces to the sub-alphabet picked out by `OpPred`

  open import Syntax.Grades.Traces.Restriction Op _≟ₒ_ OpPred

  -- the (non-empty) sets of timed traces over all operations provide the
  -- effect grades, those over the `OpPred`-operations the resource grades

  open import Syntax.Grades.SetOfTraces Op  _≟ₒ_  using () renaming (right-sided-traces to traces-E)
  open import Syntax.Grades.SetOfTraces Op' _≟ₒ'_ using () renaming (right-sided-traces to traces-R)

  open import Syntax.Grades.Traces.Base

  -- a set of traces is sent to the set of its restrictions to the
  -- sub-alphabet; monotonicity and the homomorphism laws follow from the
  -- corresponding facts about `restrict-traces`

  traces→subset-traces : traces-E →ᵍ traces-R
  traces→subset-traces = record
    { map          = λ P → neTraces (restrict-traces (traces P)) (restrict-nonempty (nonempty P))
    ; map-monotone = λ I≾J → restrict-⊑ I≾J
    ; map-u        = refl
    ; map-·        = λ {P} {Q} → ne-ext Op' (restrict-·ˢ (traces P) (traces Q))
    ; map-of-nat   = λ {n} → cong (λ z → neTraces (z ∷ []) tt) (restrict-⟨⟩ n)
    }

  tracesToRestrictedTracesGradeSystem : GradeSystem
  tracesToRestrictedTracesGradeSystem = record
    { RGrade = traces-R
    ; EGrade = traces-E
    ; ∣_∣ᵉ   = traces→subset-traces
    }
