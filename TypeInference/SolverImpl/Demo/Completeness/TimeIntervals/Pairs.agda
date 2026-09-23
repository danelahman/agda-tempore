--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: pairs without a handler. --
--------------------------------------------------------------------------------

open import Data.Nat using (z≤n; s≤s)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Pairs where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

ex-p-λ : Verdict p-λ
ex-p-λ = ok (Base reading) (econst (op-grade read)) refl ≤!

ex-p-I : Verdict p-I
ex-p-I = ok Unit (econst [ 0 , ↑ 1 , z≤n ]) refl ≤!

ex-p-S : Verdict p-S
ex-p-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-D : Verdict p-D
ex-p-D = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-B : Verdict p-B
ex-p-B = ok ([ ûᵣ ] Base reading) (econst (op-grade read)) refl ≤!

ex-p-U : Verdict p-U
ex-p-U = ok Unit (econst (op-grade read)) refl ≤!

ex-λ-I : Verdict λ-I
ex-λ-I = ok (Bool ⇒ Unit ‼ econst [ 0 , ↑ 1 , z≤n ]) ûₑ refl ≤!

ex-λ-S : Verdict λ-S
ex-λ-S = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-λ-D : Verdict λ-D
ex-λ-D = ok Bool (econst (of-natᵉ 1)) refl ≤!

ex-s-I : Verdict s-I
ex-s-I = ok Unit (econst [ 1 , ↑ 2 , s≤s z≤n ]) refl ≤!

ex-s-D : Verdict s-D
ex-s-D = ok Bool (econst (of-natᵉ 3)) refl ≤!

ex-i-D : Verdict i-D
ex-i-D = ok Unit (econst [ 1 , ↑ 2 , s≤s z≤n ]) refl ≤!

ex-b-λ : Verdict b-λ
ex-b-λ = ok (Unit ⇒ [ ûᵣ ] Unit ‼ ûₑ) ûₑ refl ≤!

ex-b-g : Verdict b-g
ex-b-g = ok ([ ûᵣ ] Unit) ûₑ refl ≤!

ex-u-λ : Verdict u-λ
ex-u-λ = ok Unit ûₑ refl ≤!

ex-b-I : Verdict b-I
ex-b-I = ok ([ ûᵣ ] Unit) ûₑ refl ≤!

ex-u-I : Verdict u-I
ex-u-I = ok Unit ûₑ refl ≤!

ex-b-S : Verdict b-S
ex-b-S = ok Unit ûₑ refl ≤!

ex-b-D : Verdict b-D
ex-b-D = ok ([ ûᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

ex-u-D : Verdict u-D
ex-u-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-b-U : Verdict b-U
ex-b-U = ok Unit ûₑ refl ≤!
