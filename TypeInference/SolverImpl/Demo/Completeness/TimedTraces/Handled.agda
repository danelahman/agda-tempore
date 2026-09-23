--------------------------------------------------------------------------------
-- Completeness checks at timed traces: pairs with a handler.                 --
--                                                                            --
-- Each clause family handling each construct, a forwarding clause opening a  --
-- box, and a family chosen per operation.                                    --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec)

open import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Handled where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops using (op-grade)

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

module Hf = Handling forward
module Hr = Handling resume
module Hd = Handling drop

module Forwarding where

  open Hf

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (op-grade read ·ₑ op-grade read)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (op-grade read)) refl ≤!

module Resuming where

  open Hr

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (op-grade read ·ₑ op-grade read)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (op-grade read)) refl ≤!

module Discarding where

  open Hd

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (op-grade read ·ₑ op-grade read)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (op-grade read)) refl ≤!

ex-fwd-U : Verdict fwd-U
ex-fwd-U = ok Unit (econst (op-grade read)) refl ≤!

module Chosen where

  open M.Handling (choose forward drop)

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!
