--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: a value kept across the                --
-- resumption.                                                                --
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
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Kept where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

open M.Keeping (keepAfter τ τₑ τᵣ ans)

ex-h-keep : Outcome h-keep
ex-h-keep = ok (scope 14 0 25 , Bool ‼ econst (of-natᵉ 1) ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
