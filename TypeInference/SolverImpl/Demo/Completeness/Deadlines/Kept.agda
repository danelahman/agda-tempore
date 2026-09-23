--------------------------------------------------------------------------------
-- Completeness checks at deadlines: a value kept across the resumption, by   --
-- clauses resuming at once and after a tick.                                 --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; uᵈ-min)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Kept where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

module Now   = M.Keeping (keepNow uᵈ-min uᵈ-min ans)
module After = M.Keeping (keepAfter τ τₑ τᵣ ans)

ex-h-keep : Verdict Now.h-keep
ex-h-keep = ok Bool (econst (of-natᵉ 1)) refl ≤!

ex-h-keep-after : Verdict After.h-keep
ex-h-keep-after = ok Bool (econst (of-natᵉ 1)) refl ≤!
