--------------------------------------------------------------------------------
-- Completeness checks at timed traces: a handler returning a box, or the     --
-- handled answer, for forwarding and resuming families.                      --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec; uᵇ-least; module TC)
open TC using (reading)

open import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Boxed where

open LanguageSpec spec
open GradeSystemInterface Grades using (⊤ᵣ)
open Operations Ops using (op-grade)

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ rconst ⊤ᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!

module BoxedR where

  open M.Boxing (resumeNow uᵇ-least uᵇ-least ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ rconst ⊤ᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!
