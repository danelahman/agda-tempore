--------------------------------------------------------------------------------
-- Completeness checks at deadlines: pairs without a handler.                 --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Pairs where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

ex-p-λ : Verdict p-λ
ex-p-λ = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

ex-p-I : Verdict p-I
ex-p-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-p-S : Verdict p-S
ex-p-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-D : Verdict p-D
ex-p-D = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-B : Verdict p-B
ex-p-B = ok ([ ûᵣ ] Base reading) (econst (of-natᵉ 1)) refl ≤!

ex-p-U : Verdict p-U
ex-p-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-λ-I : Verdict λ-I
ex-λ-I = ok (Bool ⇒ Unit ‼ econst (of-natᵉ 1)) ûₑ refl ≤!

ex-λ-S : Verdict λ-S
ex-λ-S = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-λ-D : Verdict λ-D
ex-λ-D = ok Bool (econst (of-natᵉ 1)) refl ≤!

ex-s-I : Verdict s-I
ex-s-I = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-s-D : Verdict s-D
ex-s-D = ok Bool (econst (of-natᵉ 3)) refl ≤!

ex-i-D : Verdict i-D
ex-i-D = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-b-λ : Verdict b-λ
ex-b-λ = ok (Unit ⇒ [ ûᵣ ] Unit ‼ ûₑ) ûₑ refl ≤!

ex-b-g : Verdict b-g
ex-b-g = ok ([ rconst ⊤ᵣ ] Unit) ûₑ refl ≤!

ex-u-λ : Verdict u-λ
ex-u-λ = ok Unit ûₑ refl ≤!

ex-b-I : Verdict b-I
ex-b-I = ok ([ rconst ⊤ᵣ ] Unit) ûₑ refl ≤!

ex-u-I : Verdict u-I
ex-u-I = ok Unit ûₑ refl ≤!

ex-b-S : Verdict b-S
ex-b-S = ok Unit ûₑ refl ≤!

ex-b-D : Verdict b-D
ex-b-D = ok ([ rconst ⊤ᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

ex-u-D : Verdict u-D
ex-u-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-b-U : Verdict b-U
ex-b-U = ok Unit ûₑ refl ≤!
