--------------------------------------------------------------------------------
-- Tests at deadlines: a handler returning a box, or the                      --
-- handled answer, for forwarding and both resuming families.                 --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Fin using (#_)
open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; uᵈ-min)

open import TypeInference.Tests.Deadlines.Setup

module TypeInference.Tests.Deadlines.Boxed where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Outcome h-box
  ex-h-box = ok (scope 11 9 13 , [ rvar (# 6) ] Unit ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-ans : Outcome h-ans
  ex-h-ans = ok (scope 12 0 13 , Base reading ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module BoxedR where

  open M.Boxing (resumeNow uᵈ-min uᵈ-min ans)

  ex-h-box : Outcome h-box
  ex-h-box = ok (scope 11 9 10 , [ rvar (# 6) ] Unit ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-ans : Outcome h-ans
  ex-h-ans = ok (scope 12 0 10 , Base reading ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module BoxedR₁ where

  open M.Boxing (resumeAfter τ τₑ τᵣ ans)

  ex-h-box : Outcome h-box
  ex-h-box = ok (scope 11 9 13 , [ rvar (# 6) ] Unit ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-ans : Outcome h-ans
  ex-h-ans = ok (scope 12 0 13 , Base reading ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
