--------------------------------------------------------------------------------
-- Completeness checks at deadlines: the setup.                               --
--                                                                            --
-- `Generic` at `Demo.TimeIntervals`' deadlines, an answer of each operation, --
-- and the clause families the entries share.                                 --
--------------------------------------------------------------------------------

open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; opsᵈ₃; uᵈ-min)

import TypeInference.SolverImpl.Demo.Completeness.Generic

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup where

open LanguageSpec specᵈ
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades   specᵈ
open import TypeInference.OpenSyntax.Types    specᵈ
open import TypeInference.OpenSyntax.Contexts specᵈ
open import TypeInference.OpenSyntax.Hyps     specᵈ
open import TypeInference.OpenSyntax.Language specᵈ

------------------------------------------------------------------------
-- Setup
--
-- Both units are least, so both options are taken; `read` takes `⋆`.

module M = TypeInference.SolverImpl.Demo.Completeness.Generic
             specᵈ opsᵈ₃ (just uᵈ-min) (just uᵈ-min) read ⋆

open M

-- an answer of each operation's arity type

ans : (op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ
ans read  = const reading 0
ans write = ⋆
ans send  = ⋆

-- a resuming clause may idle a tick: it fits every operation's deadline

τ : Op → ℕ
τ _ = 1

τₑ : (op : Op) → of-natᵉ (τ op) ≾ₑ op-grade op
τₑ read  = ≾ₑ! (of-natᵉ 1) (op-grade read)
τₑ write = ≾ₑ! (of-natᵉ 1) (op-grade write)
τₑ send  = ≾ₑ! (of-natᵉ 1) (op-grade send)

τᵣ : (op : Op) → of-natʳ (τ op) ≾ᵣ mapᵉ (op-grade op)
τᵣ read  = ≾ᵣ! (of-natʳ 1) (mapᵉ (op-grade read))
τᵣ write = ≾ᵣ! (of-natʳ 1) (mapᵉ (op-grade write))
τᵣ send  = ≾ᵣ! (of-natʳ 1) (mapᵉ (op-grade send))

-- clause families: resuming at once, resuming after a tick, and
-- discarding

resume : Clauses
resume = resumeNow uᵈ-min uᵈ-min ans

resume₁ : Clauses
resume₁ = resumeAfter τ τₑ τᵣ ans

drop : Clauses
drop = discard uᵈ-min

-- a constant effect of `k` ticks

d : ℕ → ∀ {Θ} → EExp Θ
d k = econst (of-natᵉ k)
