--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: a handler returning a                  --
-- box, or the handled answer, for forwarding and resuming families.          --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Fin using (#_)
open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Boxed where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Outcome h-box
  ex-h-box = ok (scope 11 9 13 , ([ rvar (# 6) ] Unit) ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-ans : Outcome h-ans
  ex-h-ans = ok (scope 12 0 13 , Base reading ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module BoxedR where

  open M.Boxing (resumeAfter τ τₑ τᵣ ans)

  ex-h-box : Outcome h-box
  ex-h-box = ok (scope 11 9 13 , ([ rvar (# 6) ] Unit) ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-ans : Outcome h-ans
  ex-h-ans = ok (scope 12 0 13 , Base reading ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
