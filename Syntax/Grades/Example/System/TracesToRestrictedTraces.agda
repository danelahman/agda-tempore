------------------------------------------------------------------------
-- A grade system in which the resource grades observe less than the   --
-- effect grades do.                                                   --
--                                                                     --
-- Effect grades are (non-empty) sets of timed traces over all          --
-- operations; resource grades are sets of timed traces over the        --
-- sub-alphabet a predicate picks out. The projection restricts each    --
-- trace, keeping the delays and the admitted operations and dropping   --
-- the rest -- so a resource grade records only the part of a           --
-- computation's behaviour that is being accounted for.                 --
------------------------------------------------------------------------

open import Data.Bool
open import Data.List
open import Data.Unit using (tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.Example.System.TracesToRestrictedTraces (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

module _ (OpPred : Op → Bool) where

  -- the restriction of traces to the sub-alphabet picked out by `OpPred`

  open import Syntax.Grades.Traces.Restriction Op _≟ₒ_ OpPred

  -- the (non-empty) sets of timed traces over all operations provide the
  -- effect grades, those over the `OpPred`-operations the resource grades

  open import Syntax.Grades.Example.TraceSet.Inclusion Op  _≟ₒ_
    using () renaming (traces-by-inclusion to traces-E)
  open import Syntax.Grades.Example.TraceSet.Inclusion Op' _≟ₒ'_
    using () renaming (traces-by-inclusion to traces-R)

  open import Syntax.Grades.Traces.Sets

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
