--------------------------------------------------------------------------------
-- Completeness checks at deadlines: a handler inside another, for each pair  --
-- of forwarding, resuming and discarding families.                           --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Nested where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

ex-fwd-in-fwd : Verdict (Nesting.nest forward forward)
ex-fwd-in-fwd = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-fwd-in-res : Verdict (Nesting.nest forward resume)
ex-fwd-in-res = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-fwd-in-drop : Verdict (Nesting.nest forward drop)
ex-fwd-in-drop = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-res-in-fwd : Verdict (Nesting.nest resume forward)
ex-res-in-fwd = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-res-in-res : Verdict (Nesting.nest resume resume)
ex-res-in-res = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-res-in-drop : Verdict (Nesting.nest resume drop)
ex-res-in-drop = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-drop-in-fwd : Verdict (Nesting.nest drop forward)
ex-drop-in-fwd = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-drop-in-res : Verdict (Nesting.nest drop resume)
ex-drop-in-res = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-drop-in-drop : Verdict (Nesting.nest drop drop)
ex-drop-in-drop = ok Unit (econst (of-natᵉ 1)) refl ≤!
