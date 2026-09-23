--------------------------------------------------------------------------------
-- Tests at deadlines: a value kept across the resumption, by                 --
-- clauses resuming at once and after a tick.                                 --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; uᵈ-min)

open import TypeInference.Tests.Deadlines.Setup

module TypeInference.Tests.Deadlines.Kept where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

module Now   = M.Keeping (keepNow uᵈ-min uᵈ-min ans)
module After = M.Keeping (keepAfter τ τₑ τᵣ ans)

ex-h-keep : Outcome Now.h-keep
ex-h-keep = ok (scope 14 0 22 , Bool ‼ econst (of-natᵉ 1) ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-h-keep-after : Outcome After.h-keep
ex-h-keep-after = ok (scope 14 0 25 , Bool ‼ econst (of-natᵉ 1) ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
