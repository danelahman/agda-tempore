------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                  --
--                                                                    --
-- A grade records the runs a computation may have. The families      --
-- differ in the comparison between a run and a listed trace:         --
--                                                                    --
--   Timed.*    the two cost-sensitive orders on traces. Going up the --
--              allowance order, an operation becomes a delay that    --
--              covers it; going up the coverage order, a run may do  --
--              more than is demanded.                                --
--                                                                    --
--   Subsets.*  equality: a run is a listed trace or it is not, and   --
--              the lift is subset inclusion.                         --
--                                                                    --
-- `Timed.*` has a floor, a cap and their pairing:                    --
--                                                                    --
--   Timed.LeftSided   a lower bound on what happened, reduced to     --
--                     the antichain of its weakest guarantees        --
--   Timed.RightSided  an upper bound, reduced to the antichain of    --
--                     its most permissive bounds                     --
--   Timed.TwoSided    both at once, with a coherence field           --
--                                                                    --
-- `Subsets.*` has the cap, `Subsets.RightSided`.                     --
--                                                                    --
-- `Regular.*` has the cap at inclusion, over regular sets of runs    --
-- represented by canonical minimal automata.                         --
--                                                                    --
-- Every endpoint is read *disjunctively*, one listed trace carrying  --
-- the grade: grades weaken by gaining members, and the union of two  --
-- grades is their join.                                              --
--                                                                    --
-- The `Timed.*` grades are `Traces.Lifted.*` instantiated at a trace --
-- order; the `Subsets.*` grade is built directly on the order `_⊑_`  --
-- of `Sets`, the discrete order not being a `TraceOrder` (it lacks   --
-- `≼-nil`).                                                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces where

------------------------------------------------------------------------
-- The constructions, over an arbitrary order (or pair of orders)

import Syntax.Grades.Example.Traces.Lifted.LeftSided
import Syntax.Grades.Example.Traces.Lifted.RightSided
import Syntax.Grades.Example.Traces.Lifted.TwoSided

-- grade morphisms between them along a map of traces between two time
-- domains

import Syntax.Grades.Example.Traces.Lifted.Morphism

------------------------------------------------------------------------
-- At the cost-sensitive orders
--
-- The floor takes the coverage order, in which time never covers an
-- operation, and the cap the allowance order, in which a listed delay
-- is a budget that pays for operations.

import Syntax.Grades.Example.Traces.Timed.LeftSided
import Syntax.Grades.Example.Traces.Timed.RightSided
import Syntax.Grades.Example.Traces.Timed.TwoSided

-- along a morphism of time domains, and whole steps read in dense time

import Syntax.Grades.Example.Traces.Timed.Morphism
import Syntax.Grades.Example.Traces.Timed.Dense

------------------------------------------------------------------------
-- At the subset order
--
-- The comparison is equality, and the cap is subset inclusion `X ⊆ Q`:
-- every run a computation may have is one of the listed traces.

import Syntax.Grades.Example.Traces.Subsets.Base
import Syntax.Grades.Example.Traces.Subsets.RightSided

------------------------------------------------------------------------
-- Regular sets
--
-- A grade is a non-empty regular set of runs, represented by the
-- canonical minimal automaton of its encoding over `Op ⊎ tick`; the
-- finite sets of `Subsets.RightSided` embed in it, but no grade
-- morphism exists.

import Syntax.Grades.Example.Traces.Regular.RightSided
import Syntax.Grades.Example.Traces.Regular.Subsets

------------------------------------------------------------------------
-- Rigid timed regular grades
--
-- A grade is a non-empty regular language of whole-step slots closed
-- downward under the slot order, the order on exact words
-- (`Grades.Exact`) read slot by slot. Literals are one-sided
-- expressions over interval letters; upper bounds, lower bounds, and
-- their pairs.

import Syntax.Grades.Example.Traces.Rigid.Regular.Base
import Syntax.Grades.Example.Traces.Rigid.Regular.RightSided
import Syntax.Grades.Example.Traces.Rigid.Regular.LeftSided
import Syntax.Grades.Example.Traces.Rigid.Regular.TwoSided

------------------------------------------------------------------------
-- Rigid timed finite-expression grades
--
-- Preordered grades over the non-negative rationals: finite one-sided
-- expressions over interval letters with open or closed ends, compared
-- by the runs they denote and decided by the pouring reader
-- (`Grades.Exact.Finite`); upper bounds, lower bounds, and their pairs.

import Syntax.Grades.Example.Traces.Rigid.Finite.Base
import Syntax.Grades.Example.Traces.Rigid.Finite.RightSided
import Syntax.Grades.Example.Traces.Rigid.Finite.LeftSided
import Syntax.Grades.Example.Traces.Rigid.Finite.TwoSided
