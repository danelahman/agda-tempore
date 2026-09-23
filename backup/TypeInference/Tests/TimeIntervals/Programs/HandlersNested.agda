--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: `handlers_nested.tpe`.                 --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (write)
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.Tests.TimeIntervals.Setup
open import TypeInference.Tests.TimeIntervals.InClause using (h-in-clause)

module TypeInference.Tests.TimeIntervals.Programs.HandlersNested where

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

ex-nested : Outcome nested
ex-nested = ok (scope 20 0 24 , Unit ‼ econst (op-grade write) ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
