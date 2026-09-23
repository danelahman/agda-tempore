--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: `handlers_nested.tpe`.   --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (write)
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup
open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.InClause using (h-in-clause)

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.HandlersNested where

open LanguageSpec spec
open Operations Ops

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- `handlers_nested.tpe`, with `write` for both operations: the outer
-- clause runs an inner handler whose clause idles and resumes

nested : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ _
nested = h-in-clause

ex-nested : Verdict nested
ex-nested = ok Unit (econst (op-grade write)) refl ≤!
