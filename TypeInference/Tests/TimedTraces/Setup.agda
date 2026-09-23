--------------------------------------------------------------------------------
-- Tests at timed traces: the setup.                                          --
--                                                                            --
-- `Generic` at `Demo.TimedTraces`' grades, an answer of each operation, and  --
-- the clause families the tests share.                                       --
--------------------------------------------------------------------------------

open import Data.Maybe using (just)

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (Op; read; write; send)

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec; ops₃; uᵇ-least; module TC)
open TC using (reading)

import TypeInference.Tests.Generic

module TypeInference.Tests.TimedTraces.Setup where

open LanguageSpec spec
open Operations Ops using (arity)

open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

------------------------------------------------------------------------
-- Setup
--
-- Both units are least, so both options are taken; `read` takes `⋆`.

module M = TypeInference.Tests.Generic
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
