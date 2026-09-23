--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: a handler returning a    --
-- box, or the handled answer, for forwarding and resuming families.          --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Boxed where

open LanguageSpec spec
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!

module BoxedR where

  open M.Boxing (resumeAfter τ τₑ τᵣ ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!
