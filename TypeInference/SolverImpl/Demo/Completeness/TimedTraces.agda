--------------------------------------------------------------------------------
-- Completeness checks at timed traces.                                       --
--                                                                            --
-- Inference checked against open derivations of pairs of constructs at       --
-- `Demo.TimedTraces`' grades: finite sets of timed runs, read as             --
-- allowances, over an identity grade system; both units least.               --
--                                                                            --
--       P      Hf     Hr     Hd     B      U      λ      I      S      D     --
--   P   ok     ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hf         ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hr                ok     ok     ok     ok     ok     ok     ok/ref ok    --
--   Hd                       ok     ok     ok     ok     ok     ok     ok    --
--   B                               worse  ok     ok     ok     ok     ok    --
--   U                                      ·      ok     ok     ok     ok    --
--   λ                                             ·      ok     ok     ok    --
--   I                                                    ·      ok     ok    --
--   S                                                           ·      ok    --
--   D                                                                  ·     --
--                                                                            --
-- P perform; Hf, Hr, Hd handle with a forwarding, resuming or discarding     --
-- clause family; B box; U unbox; λ lam and application; I if; S              --
-- sequencing; D delay. `ok` inferred, at least as good as declared;          --
-- `ref` refused; `worse` inferred, worse than declared; `—` not              --
-- derivable; `·` no entry.                                                   --
--                                                                            --
-- Hr × S is refused where a value bound before the resumption is used        --
-- after it (`Kept`). B × B is `b-g`, a box whose grade nothing bounds.       --
--------------------------------------------------------------------------------

open import Data.Maybe using (just)
open import Data.Fin using (#_)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; ⌈_⌉; ⟨_⟩; _∙_)
open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
  using (within_; ⟅_⟆; ⟅_∣_⟆)

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec; ops₃; uᵇ-least; module TC)
open TC using (reading)

import TypeInference.SolverImpl.Demo.Completeness.Generic

module TypeInference.SolverImpl.Demo.Completeness.TimedTraces where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops using (op-grade; param; arity)

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

------------------------------------------------------------------------
-- Setup
--
-- Both units are least, so both options are taken; `read` takes `⋆`.

module M = TypeInference.SolverImpl.Demo.Completeness.Generic
             spec ops₃ (just uᵇ-least) (just uᵇ-least) read ⋆

open M

-- an answer of each operation's arity type

ans : (op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ
ans read  = const reading 0
ans write = ⋆
ans send  = ⋆

-- clause families: resuming at once, and discarding

resume : Clauses
resume = resumeNow uᵇ-least uᵇ-least ans

drop : Clauses
drop = discard uᵇ-least

module Hf = Handling forward
module Hr = Handling resume
module Hd = Handling drop

------------------------------------------------------------------------
-- Pairs without a handler

ex-p-λ : Verdict p-λ
ex-p-λ = ok (Base reading) (econst (op-grade read)) refl ≤!

ex-p-I : Verdict p-I
ex-p-I = ok Unit (econst (op-grade read)) refl ≤!

ex-p-S : Verdict p-S
ex-p-S = ok Unit (econst (op-grade read ·ₑ op-grade read)) refl ≤!

ex-p-D : Verdict p-D
ex-p-D = ok Unit (econst (of-natᵉ 1 ·ₑ op-grade read)) refl ≤!

ex-p-B : Verdict p-B
ex-p-B = ok ([ ûᵣ ] Base reading) (econst (op-grade read)) refl ≤!

ex-p-U : Verdict p-U
ex-p-U = ok Unit (econst (op-grade read)) refl ≤!

ex-λ-I : Verdict λ-I
ex-λ-I = ok (Bool ⇒ Unit ‼ econst (of-natᵉ 1)) ûₑ refl ≤!

ex-λ-S : Verdict λ-S
ex-λ-S = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-λ-D : Verdict λ-D
ex-λ-D = ok Bool (econst (of-natᵉ 1)) refl ≤!

ex-s-I : Verdict s-I
ex-s-I = ok Unit (econst (of-natᵉ 1 ·ₑ op-grade read)) refl ≤!

ex-s-D : Verdict s-D
ex-s-D = ok Bool (econst (of-natᵉ 1 ·ₑ of-natᵉ 2)) refl ≤!

ex-i-D : Verdict i-D
ex-i-D = ok Unit (econst (of-natᵉ 1 ⊔ₑ of-natᵉ 2)) refl ≤!

ex-b-λ : Verdict b-λ
ex-b-λ = ok (Unit ⇒ [ ûᵣ ] Unit ‼ ûₑ) ûₑ refl ≤!

ex-b-g : Verdict b-g
ex-b-g = worse ([ ûᵣ ] Unit) ûₑ refl ≰!

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

------------------------------------------------------------------------
-- Pairs with a handler

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

module Kept where

  open M.Keeping (keepNow uᵇ-least uᵇ-least ans)

  ex-h-keep : Verdict h-keep
  ex-h-keep = refused refl

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!

module BoxedR where

  open M.Boxing (resumeNow uᵇ-least uᵇ-least ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!

module Chosen where

  open M.Handling (choose forward drop)

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

module Nested where

  ex-fwd-in-fwd : Verdict (Nesting.nest forward forward)
  ex-fwd-in-fwd = ok Unit (econst (op-grade read)) refl ≤!

  ex-fwd-in-res : Verdict (Nesting.nest forward resume)
  ex-fwd-in-res = ok Unit (econst (op-grade read)) refl ≤!

  ex-fwd-in-drop : Verdict (Nesting.nest forward drop)
  ex-fwd-in-drop = ok Unit (econst (op-grade read)) refl ≤!

  ex-res-in-fwd : Verdict (Nesting.nest resume forward)
  ex-res-in-fwd = ok Unit (econst (op-grade read)) refl ≤!

  ex-res-in-res : Verdict (Nesting.nest resume resume)
  ex-res-in-res = ok Unit (econst (op-grade read)) refl ≤!

  ex-res-in-drop : Verdict (Nesting.nest resume drop)
  ex-res-in-drop = ok Unit (econst (op-grade read)) refl ≤!

  ex-drop-in-fwd : Verdict (Nesting.nest drop forward)
  ex-drop-in-fwd = ok Unit (econst (op-grade read)) refl ≤!

  ex-drop-in-res : Verdict (Nesting.nest drop resume)
  ex-drop-in-res = ok Unit (econst (op-grade read)) refl ≤!

  ex-drop-in-drop : Verdict (Nesting.nest drop drop)
  ex-drop-in-drop = ok Unit (econst (op-grade read)) refl ≤!

------------------------------------------------------------------------
-- What these grades see

-- B × P × U: a permit naming a reading and then a store, opened once
-- both are done

permit : R
permit = within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆

logged : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ _
logged = box (rconst permit) true
           (perform read ⋆
             (perform write (v Hd)
               (unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd)))))

ex-logged : Verdict logged
ex-logged = ok Bool (econst (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)) refl ≤!
