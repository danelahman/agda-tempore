--------------------------------------------------------------------------------
-- Tests at timed traces: a handler returning a box, or the                   --
-- handled answer, for forwarding and resuming families.                      --
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

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec; uᵇ-least; module TC)
open TC using (reading)

open import TypeInference.Tests.TimedTraces.Setup

module TypeInference.Tests.TimedTraces.Boxed where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops using (op-grade)

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Outcome h-box
  ex-h-box = ok (scope 11 9 13 ,
                 ([ rvar (# 6) ] Unit) ‼ econst (op-grade read) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-ans : Outcome h-ans
  ex-h-ans = ok (scope 12 0 13 , Base reading ‼ econst (op-grade read) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module BoxedR where

  open M.Boxing (resumeNow uᵇ-least uᵇ-least ans)

  ex-h-box : Outcome h-box
  ex-h-box = ok (scope 11 9 10 ,
                 ([ rvar (# 6) ] Unit) ‼ econst (op-grade read) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-ans : Outcome h-ans
  ex-h-ans = ok (scope 12 0 10 , Base reading ‼ econst (op-grade read) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
