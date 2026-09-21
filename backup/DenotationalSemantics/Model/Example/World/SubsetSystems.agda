------------------------------------------------------------------------
-- The two subset grade systems have models.                           --
--                                                                    --
-- Their resource grades are the intervals with a formal greatest       --
-- grade, so it is the frames of those that make the presheaf model      --
-- available here: the category of worlds, the graded modalities and     --
-- their adjunction ask for a grade system and a frame over its          --
-- resource grades, and for nothing else.                                --
--                                                                    --
-- The left-sided system gets a tick frame only, as the plain left-sided --
-- intervals do -- a history frame for them is the two-sided one at an     --
-- infinite upper endpoint.                                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.SubsetSystems
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (costˡᵒ costʰⁱ : Op → ℕ)
  (cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o) where

open import Syntax.Grades using (GradeSystem)

open import Syntax.Grades.Example.System.Traces.Subsets.LeftSided Op _≟ₒ_ costˡᵒ
  using (subsetsToLeftSidedIntervalsGradeSystem)
open import Syntax.Grades.Example.System.Traces.Subsets.TwoSided
  Op _≟ₒ_ costˡᵒ costʰⁱ cost-≤
  using (subsetsToIntervalsGradeSystem)

open import DenotationalSemantics.Model.World

import DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSidedWithTop
  as LeftSidedTicks
import DenotationalSemantics.Model.Example.World.Ticks.Time.TwoSidedWithInfinityAndTop
  as TwoSidedTicks
import DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinityAndTop
  Op costˡᵒ as TwoSidedHistories

import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction as Adjunction
import DenotationalSemantics.Model.Example.PSh.Modality.Eternal as Eternal

------------------------------------------------------------------------
-- The frames, at the systems' own resource grades

left-sided-ticks
  : World (GradeSystem.RGrade subsetsToLeftSidedIntervalsGradeSystem)
left-sided-ticks = LeftSidedTicks.ticks

two-sided-ticks
  : World (GradeSystem.RGrade subsetsToIntervalsGradeSystem)
two-sided-ticks = TwoSidedTicks.ticks

two-sided-histories
  : World (GradeSystem.RGrade subsetsToIntervalsGradeSystem)
two-sided-histories = TwoSidedHistories.histories

------------------------------------------------------------------------
-- The presheaf model over each frame

module LeftSidedOnTicks =
  Adjunction subsetsToLeftSidedIntervalsGradeSystem left-sided-ticks
module LeftSidedEternal =
  Eternal subsetsToLeftSidedIntervalsGradeSystem left-sided-ticks

module TwoSidedOnTicks =
  Adjunction subsetsToIntervalsGradeSystem two-sided-ticks
module TwoSidedEternalOnTicks =
  Eternal subsetsToIntervalsGradeSystem two-sided-ticks

module TwoSidedOnHistories =
  Adjunction subsetsToIntervalsGradeSystem two-sided-histories
module TwoSidedEternalOnHistories =
  Eternal subsetsToIntervalsGradeSystem two-sided-histories
