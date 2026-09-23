--------------------------------------------------------------------------------
-- Completeness checks at deadlines: pairs with a handler.                    --
--                                                                            --
-- Each clause family handling each construct, a forwarding clause opening a  --
-- box, and a family chosen per operation.                                    --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Handled where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

module Hf = Handling forward
module Hr = Handling resume
module Hr₁ = Handling resume₁
module Hd = Handling drop

module Forwarding where

  open Hf

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module Resuming where

  open Hr

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module ResumingAfter where

  open Hr₁

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module Discarding where

  open Hd

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-fwd-U : Verdict fwd-U
ex-fwd-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module Chosen where

  open M.Handling (choose forward drop)

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!
