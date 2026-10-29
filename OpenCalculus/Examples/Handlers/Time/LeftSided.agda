-------------------------------------------------------------------
-- Handlers at left-sided intervals                              --
--                                                               --
-- Every scheme is the one written in `Handlers`.                --
-- `resume-twice` is typed, the unit being the top; `discard` is --
-- refuted. Two handlers whose clause delays and drops its       --
-- continuation, alone and nested in another clause, are refuted --
-- by retry at a candidate the grade supplies: the condition     --
-- holds at the unit, which is the top, and fails at later ones. --
-------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (suc)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Time-LeftSided)

module OpenCalculus.Examples.Handlers.Time.LeftSided where

open Time-LeftSided using (spec; hints; enum)

open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Inference.Principality spec using (Typable; untypable)
open import OpenCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import OpenCalculus.Examples.Handlers spec hints enum
open import OpenCalculus.Syntax.Scopes using (_+e; ∅ˢ)
open import OpenCalculus.Syntax.Raw spec
open import OpenCalculus.Examples.Variables using (v₀; v₁; v₂)
open import Grades.Examples.Worked.Operations using (Op; send)

relay-reported : schemeOf (infer [] relay) ≡ just expected-relay
relay-reported = refl

relay-boxed-reported : schemeOf (infer [] relay-boxed) ≡ just expected-relay-boxed
relay-boxed-reported = refl

-- A handler as a value: bound by `let`, taken as an argument, and
-- passed to a function

bound-reported : schemeOf (infer [] bound) ≡ just expected-bound
bound-reported = refl

run-reported : schemeOf (infer [] run) ≡ just expected-run-commuted
run-reported = refl

run-forward-reported : schemeOf (infer [] run-forward) ≡ just expected-run-forward
run-forward-reported = refl

-- The unit is the top, so the continuation may be spent twice and
-- nothing goes stale

resume-twice-reported : schemeOf (infer [] resume-twice) ≡ just expected-resume-twice
resume-twice-reported = refl

resume-twice-derivable : Typable [] resume-twice
resume-twice-derivable = resume-twice-typable _

-- Returning at once is not below `op-grade read`: `no-discarding` in
-- `ClosedCalculus/Examples/Typing/Time/LeftSided.agda`

discard-untypable-verdict : infer [] discard ≡ untypable
discard-untypable-verdict = refl

discard-not-typable : ¬ Typable [] discard
discard-not-typable = infer-untypable [] discard discard-untypable-verdict
------------------------------------------------------------------
-- A clause that delays the 4 ticks of `send` and drops its
-- continuation:
--
--   late-discard m = handle m () with handler {op p k ↦ delay 4; return ()}
--
-- The clause's grade `4` must be below `op · j` for every
-- continuation grade `j`: at `send`, `j` is the unit, which is the
-- top. The condition is deferred, and retry refutes it at `j = 1`, a
-- candidate of the constants `4` and `op` (`left-sided-witnesses`).

late-discard : RawC ∅ˢ 0
late-discard =
  return (lam (handle (v₀ · ⋆) `with handler (return ⋆) (λ _ → delay 4 (return ⋆))))

late-discard-verdict : infer [] late-discard ≡ untypable
late-discard-verdict = refl

-- The same clause nested, as in the prototype's
-- `examples/handlers/nested_reject.tpe`: an outer clause performs its
-- operation, handles a `send` with the clause above, and resumes.

nested-reject : RawC ∅ˢ 0
nested-reject = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) outer))
  where
    inner : ∀ {Θ n} → RawC Θ n
    inner = handle (perform send ⋆ (return ⋆)) `with handler (return ⋆) (λ _ → delay 4 (return ⋆))

    outer : Op → RawC (∅ˢ +e) (suc (suc (suc 0)))
    outer op = perform op v₁ (inner ⨟ unbox (var (fsuc (fsuc fzero))) (v₀ · v₂))

nested-reject-verdict : infer [] nested-reject ≡ untypable
nested-reject-verdict = refl
