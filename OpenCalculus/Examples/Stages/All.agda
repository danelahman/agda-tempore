------------------------------------------------------------------------
-- Single solver stages on hand-written constraints, each answer checked
-- by `refl`: splitting, disjunction pruning, absorption by the top,
-- multiset comparison of products, chained closed orderings, cycle
-- collapse, and lowering at each shape of cycle (`Canon`, `Simplify`,
-- `Entail`, `Localise`, `Values`).
------------------------------------------------------------------------

module OpenCalculus.Examples.Stages.All where

import OpenCalculus.Examples.Stages
