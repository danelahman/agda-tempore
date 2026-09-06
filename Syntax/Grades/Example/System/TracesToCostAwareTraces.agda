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
  open import Syntax.Grades.Traces.Subtrace Op opTime
    using (_≼_; ≼-refl; module DecSubtrace)

  open WithDecEq _≟ₒ_ using (_≟ᵀ_; liftˢ-mono)
  open DecSubtrace _≟ₒ_ using (_≼?_)

  -- both grades read their sets as a *floor*, so both compare them with
  -- the two sets exchanged; they differ only in how a listed run is
  -- matched. The effect grade asks to have had it exactly, the resource
  -- grade only to have covered it, at the operations' execution times.

  open import Syntax.Grades.Example.Traces.Inclusion.LeftSided Op _≟ₒ_
    using (inclusion-left-sided) renaming (_≾_ to _≾ˢ_)
  open import Syntax.Grades.Example.Traces.Subtrace.LeftSided Op _≟ₒ_ opTime
    using (subtrace-left-sided) renaming (_≾_ to _≾ᶜ_)

  -- a run covers itself, so being a member is a special case of being
  -- covered. Both orders are `liftˢ` on the same two sets in the same
  -- order -- at `_≡_` and at `_≼_` -- so this is exactly the lift's
  -- monotonicity in the relation compared.

  ⊆⇒≼ : {P Q : NeTraces} → P ≾ˢ Q → P ≾ᶜ Q
  ⊆⇒≼ {P} {Q} =
    liftˢ-mono _≟ᵀ_ _≼?_ (λ {s} eq → subst (s ≼_) eq (≼-refl s))

  -- the two grades share their carrier and their monoid structure, so
  -- the reinterpretation is the identity on sets of traces

  traces→cost-aware-traces : inclusion-left-sided →ᵍ subtrace-left-sided
  traces→cost-aware-traces = record
    { map          = λ P → P
    ; map-monotone = λ {P} {Q} → ⊆⇒≼ {P} {Q}
    ; map-u        = refl
    ; map-·        = refl
    ; map-of-nat   = refl
    }

  tracesToCostAwareTracesGradeSystem : GradeSystem
  tracesToCostAwareTracesGradeSystem = record
    { RGrade = subtrace-left-sided
    ; EGrade = inclusion-left-sided
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

  open import Syntax.Grades.Traces.Subtrace Op c
    using () renaming (module DecSubtrace to DecFast)
  open import Syntax.Grades.Traces.Subtrace Op c'
    using () renaming (module DecSubtrace to DecSlow)

  open DecFast _≟ₒ_ using () renaming (_≼?_ to _≼ᶠᵃˢᵗ?_)
  open DecSlow _≟ₒ_ using () renaming (_≼?_ to _≼ˢˡᵒʷ?_)

  open WithDecEq _≟ₒ_ using (liftˢ-mono)

  open import Syntax.Grades.Example.Traces.Subtrace.LeftSided Op _≟ₒ_ c'
    using () renaming (subtrace-left-sided to traces-slow; _≾_ to _≾ˢˡᵒʷ_)
  open import Syntax.Grades.Example.Traces.Subtrace.LeftSided Op _≟ₒ_ c
    using () renaming (subtrace-left-sided to traces-fast; _≾_ to _≾ᶠᵃˢᵗ_)

  -- both orders are `liftˢ` at the sub-trace preorder on the same two
  -- sets, one per cost model, so widening the preorder widens the order

  ≾-cost-mono : {P Q : NeTraces} → P ≾ᶠᵃˢᵗ Q → P ≾ˢˡᵒʷ Q
  ≾-cost-mono {P} {Q} = liftˢ-mono _≼ᶠᵃˢᵗ?_ _≼ˢˡᵒʷ?_ ≼-cost-mono₀

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
