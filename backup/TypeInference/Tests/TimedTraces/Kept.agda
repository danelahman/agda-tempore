--------------------------------------------------------------------------------
-- Tests at timed traces: a value kept across the resumption.                 --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec; uᵇ-least)

open import TypeInference.Tests.TimedTraces.Setup

module TypeInference.Tests.TimedTraces.Kept where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops using (op-grade)

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

open M.Keeping (keepNow uᵇ-least uᵇ-least ans)

ex-h-keep : Outcome h-keep
ex-h-keep = ok (scope 14 0 22 , Bool ‼ econst (op-grade read) ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
