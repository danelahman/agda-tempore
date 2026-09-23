--------------------------------------------------------------------------------
-- Completeness checks at deadlines: a handler returning a box, or the        --
-- handled answer, for forwarding and both resuming families.                 --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; uᵈ-min)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Boxed where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ rconst ⊤ᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

module BoxedR where

  open M.Boxing (resumeNow uᵈ-min uᵈ-min ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ rconst ⊤ᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

module BoxedR₁ where

  open M.Boxing (resumeAfter τ τₑ τᵣ ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ rconst ⊤ᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!
