--------------------------------------------------------------------------------
-- Completeness checks at timed traces: a value kept across the resumption.   --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec; uᵇ-least)

open import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Kept where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops using (op-grade)

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

open M.Keeping (keepNow uᵇ-least uᵇ-least ans)

ex-h-keep : Verdict h-keep
ex-h-keep = ok Bool (econst (op-grade read)) refl ≤!
