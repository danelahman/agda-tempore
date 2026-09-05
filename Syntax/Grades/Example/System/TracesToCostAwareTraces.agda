------------------------------------------------------------------------
-- Grade systems in which the resource grades read the same sets of    --
-- traces against a cost model.                                        --
--                                                                     --
-- The effect grades record *what* a computation may do -- sets of      --
-- timed traces compared by inclusion. The resource grades read the     --
-- same sets against the operations' prescribed execution times: a      --
-- trace lies below another when it fits inside the schedule the other  --
-- describes, with an operation performed charged the time it takes.    --
-- Time spent is thereby accounted for by operations as well as by      --
-- delays, while a schedule that calls for an operation is still not    --
-- met by time spent on anything else.                                  --
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
    using (right-sided-traces) renaming (_≾_ to _≾ˢ_)
  open import Syntax.Grades.Example.TraceSet.UpToSubtrace Op _≟ₒ_ opTime
    using (traces-up-to-subtrace) renaming (_≾_ to _≾ᶜ_)

  -- a trace of the smaller set is a member of the larger one, and covers
  -- itself there, so inclusion is contained in the sub-trace lift

  ⊆⇒≼ : {P Q : NeTraces} → P ≾ˢ Q → P ≾ᶜ Q
  ⊆⇒≼ {P} {Q} rel s m =
    fromWitness
      (Any.map (λ eq → subst (s ≼_) eq (≼-refl s)) (toWitness (rel s m)))

  -- the two grades share their carrier and their monoid structure, so
  -- the reinterpretation is the identity on sets of traces

  traces→cost-aware-traces : right-sided-traces →ᵍ traces-up-to-subtrace
  traces→cost-aware-traces = record
    { map          = λ P → P
    ; map-monotone = λ {P} {Q} → ⊆⇒≼ {P} {Q}
    ; map-u        = refl
    ; map-·        = refl
    ; map-of-nat   = refl
    }

  tracesToCostAwareTracesGradeSystem : GradeSystem
  tracesToCostAwareTracesGradeSystem = record
    { RGrade = traces-up-to-subtrace
    ; EGrade = right-sided-traces
    ; ∣_∣ᵉ   = traces→cost-aware-traces
    }

------------------------------------------------------------------------
-- Reinterpreting one cost model as another
--
-- The cost-aware grades form a family indexed by the execution times.
-- Cheaper operations are easier to fit inside a schedule, so the order
-- widens as the cost falls and the identity on sets of traces is a
-- grade morphism from the grade at the slower cost to the faster one.

module _ (c c' : Op → ℕ) (c≤c' : (o : Op) → c o ≤ c' o) where

  open import Syntax.Grades.Traces.Sets Op
  open import Syntax.Grades.Traces.SubtraceCost Op c c' c≤c'
    using (≼-cost-anti₀)

  open import Syntax.Grades.Example.TraceSet.UpToSubtrace Op _≟ₒ_ c'
    using () renaming (traces-up-to-subtrace to traces-slow; _≾_ to _≾ˢˡᵒʷ_)
  open import Syntax.Grades.Example.TraceSet.UpToSubtrace Op _≟ₒ_ c
    using () renaming (traces-up-to-subtrace to traces-fast; _≾_ to _≾ᶠᵃˢᵗ_)

  ≾-cost-anti : {P Q : NeTraces} → P ≾ˢˡᵒʷ Q → P ≾ᶠᵃˢᵗ Q
  ≾-cost-anti {P} {Q} rel s m =
    fromWitness (Any.map ≼-cost-anti₀ (toWitness (rel s m)))

  slow-traces→fast-traces : traces-slow →ᵍ traces-fast
  slow-traces→fast-traces = record
    { map          = λ P → P
    ; map-monotone = λ {P} {Q} → ≾-cost-anti {P} {Q}
    ; map-u        = refl
    ; map-·        = refl
    ; map-of-nat   = refl
    }

  costAwareTracesGradeSystem : GradeSystem
  costAwareTracesGradeSystem = record
    { RGrade = traces-fast
    ; EGrade = traces-slow
    ; ∣_∣ᵉ   = slow-traces→fast-traces
    }
