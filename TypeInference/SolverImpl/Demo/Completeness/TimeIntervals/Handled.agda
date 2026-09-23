--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: pairs with a handler.    --
--                                                                            --
-- Each clause family handling each construct, a forwarding clause opening a  --
-- box, and a family chosen per operation.                                    --
--------------------------------------------------------------------------------

open import Data.Nat using (z≤n)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Handled where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

-- no discarding clause is derivable: the unit is below no operation's
-- window

module Hf = Handling forward
module Hr = Handling resume

module Forwarding where

  open Hf

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst [ 0 , ↑ 1 , z≤n ]) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (op-grade read)) refl ≤!

  ex-fwd-U : Verdict fwd-U
  ex-fwd-U = ok Unit (econst (op-grade read)) refl ≤!

module Resuming where

  open Hr

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst [ 0 , ↑ 1 , z≤n ]) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (op-grade read)) refl ≤!

module Chosen where

  open M.Handling (choose forward resume)

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!
