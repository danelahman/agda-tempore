--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: a value kept across the  --
-- resumption.                                                                --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Kept where

open LanguageSpec spec
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

open M.Keeping (keepAfter τ τₑ τᵣ ans)

ex-h-keep : Verdict h-keep
ex-h-keep = ok Bool (econst (op-grade read)) refl ≤!
