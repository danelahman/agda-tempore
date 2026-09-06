------------------------------------------------------------------------
-- Grade systems in which the resource grades read the same sets of    --
-- traces against a cost model.                                        --
--                                                                     --
-- The effect grades record *what* a computation may do -- sets of      --
-- timed traces compared by inclusion. The resource grades read the      --
-- same sets against the operations' prescribed execution times: a run   --
-- discharges a demand when it does at least what the demand asks for,   --
-- with an operation performed charged the time it takes. A demand for   --
-- an operation is thereby discharged by time spent as well as by the    --
-- operation itself, while a demand for elapsed time is still not        --
-- discharged by having spent it on anything else.                       --
--                                                                     --
-- Two systems are built here: one reinterpreting an effect grade as a  --
-- resource grade at a fixed cost model, and one relating the           --
-- cost-aware grades at two different cost models.                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Data.List.Relation.Unary.Any as Any using (Any)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.Example.System.TracesToCostAwareTraces (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

------------------------------------------------------------------------
-- Reinterpreting an effect grade as a resource grade
--
-- The construction is parameterised by an assignment of a predetermined
-- execution time to each operation symbol.

module _ (opTime : Op → ℕ) where

  open import Syntax.Grades.Traces.Sets Op
  open import Syntax.Grades.Traces.Subtrace Op opTime using (_≼_; ≼-refl)

  -- the sets of timed traces ordered by inclusion provide the effect
  -- grades, the same sets ordered up to the cost-aware sub-trace
  -- preorder the resource grades

  open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
    using (traces-by-inclusion) renaming (_≾_ to _≾ˢ_)
  open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ opTime
    using (left-sided-traces) renaming (_≾_ to _≾ᶜ_)

  -- a trace of the smaller set is a member of the larger one, and is
  -- covered by itself there, so inclusion is contained in the sub-trace
  -- lift

  ⊆⇒≼ : {P Q : NeTraces} → P ≾ˢ Q → P ≾ᶜ Q
  ⊆⇒≼ {P} {Q} rel t m =
    fromWitness
      (Any.map (λ eq → subst (_≼ t) eq (≼-refl t)) (toWitness (rel t m)))

  -- the two grades share their carrier and their monoid structure, so
  -- the reinterpretation is the identity on sets of traces

  traces→cost-aware-traces : traces-by-inclusion →ᵍ left-sided-traces
  traces→cost-aware-traces = record
    { map          = λ P → P
    ; map-monotone = λ {P} {Q} → ⊆⇒≼ {P} {Q}
    ; map-u        = refl
    ; map-·        = refl
    ; map-of-nat   = refl
    }

  tracesToCostAwareTracesGradeSystem : GradeSystem
  tracesToCostAwareTracesGradeSystem = record
    { RGrade = left-sided-traces
    ; EGrade = traces-by-inclusion
    ; ∣_∣ᵉ   = traces→cost-aware-traces
    }

------------------------------------------------------------------------
-- Reinterpreting one cost model as another
--
-- The cost-aware grades form a family indexed by the execution times.
-- Dearer operations bank more time when they elapse unmatched, so the
-- order widens as the cost rises and the identity on sets of traces is
-- a grade morphism from the grade at the cheaper cost to the dearer.

module _ (c c' : Op → ℕ) (c≤c' : (o : Op) → c o ≤ c' o) where

  open import Syntax.Grades.Traces.Sets Op
  open import Syntax.Grades.Traces.SubtraceCost Op c c' c≤c'
    using (≼-cost-mono₀)

  open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ c'
    using () renaming (left-sided-traces to traces-slow; _≾_ to _≾ˢˡᵒʷ_)
  open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ c
    using () renaming (left-sided-traces to traces-fast; _≾_ to _≾ᶠᵃˢᵗ_)

  ≾-cost-mono : {P Q : NeTraces} → P ≾ᶠᵃˢᵗ Q → P ≾ˢˡᵒʷ Q
  ≾-cost-mono {P} {Q} rel t m =
    fromWitness (Any.map ≼-cost-mono₀ (toWitness (rel t m)))

  fast-traces→slow-traces : traces-fast →ᵍ traces-slow
  fast-traces→slow-traces = record
    { map          = λ P → P
    ; map-monotone = λ {P} {Q} → ≾-cost-mono {P} {Q}
    ; map-u        = refl
    ; map-·        = refl
    ; map-of-nat   = refl
    }

  costAwareTracesGradeSystem : GradeSystem
  costAwareTracesGradeSystem = record
    { RGrade = traces-slow
    ; EGrade = traces-fast
    ; ∣_∣ᵉ   = fast-traces→slow-traces
    }
