-------------------------------------------------------------------
-- Handlers at left-sided intervals                              --
--                                                               --
-- The shared schemes; `resume-twice` typed, `discard` refuted.  --
-- A clause that delays and drops its continuation, alone and    --
-- nested, is refuted by retry at a candidate after the unit.    --
-------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (suc)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-LeftSided)

module PolymorphicCalculus.Examples.Handlers.Time.LeftSided where

open Time-LeftSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Handlers spec hints enum
open import PolymorphicCalculus.Syntax.Scopes using (_+e; ∅ˢ)
open import PolymorphicCalculus.Syntax.Raw spec
open import PolymorphicCalculus.Examples.Variables using (v₀; v₁; v₂)
open import Grades.Examples.Worked.Operations        using (Op; send)

relay-reported : schemeOf (infer [] relay) ≡ just expected-relay
relay-reported = refl

relay-boxed-reported : schemeOf (infer [] relay-boxed) ≡ just expected-relay-boxed
relay-boxed-reported = refl

-- Handlers as values

bound-reported : schemeOf (infer [] bound) ≡ just expected-bound
bound-reported = refl

run-reported : schemeOf (infer [] run) ≡ just expected-run-commuted
run-reported = refl

run-forward-reported : schemeOf (infer [] run-forward) ≡ just expected-run-forward
run-forward-reported = refl

-- The unit is the top: spending `j` twice costs nothing

resume-twice-reported : schemeOf (infer [] resume-twice) ≡ just expected-resume-twice
resume-twice-reported = refl

resume-twice-derivable : Typable [] resume-twice
resume-twice-derivable = resume-twice-typable _

-- Returning at once is not below `op-grade read`

discard-untypable-verdict : infer [] discard ≡ untypable
discard-untypable-verdict = refl

discard-not-typable : ¬ Typable [] discard
discard-not-typable = infer-untypable [] discard discard-untypable-verdict
------------------------------------------------------------------
-- A clause that delays and drops its continuation
--
--   late-discard m = handle m () with handler {op p k ↦ delay 4; return ()}
--
-- `4 ≾ op · j` holds at `j = u` but retry refutes it at the candidate
-- `j = 1` (`left-sided-witnesses`).

late-discard : RawC ∅ˢ 0
late-discard =
  return (lam (handle (v₀ · ⋆) `with handler (return ⋆) (λ _ → delay 4 (return ⋆))))

late-discard-verdict : infer [] late-discard ≡ untypable
late-discard-verdict = refl

-- The same clause nested in an outer clause, which then resumes

nested-reject : RawC ∅ˢ 0
nested-reject = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) outer))
  where
    inner : ∀ {Θ n} → RawC Θ n
    inner = handle (perform send ⋆ (return ⋆)) `with handler (return ⋆) (λ _ → delay 4 (return ⋆))

    outer : Op → RawC (∅ˢ +e) (suc (suc (suc 0)))
    outer op = perform op v₁ (inner ⨟ unbox (var (fsuc (fsuc fzero))) (v₀ · v₂))

nested-reject-verdict : infer [] nested-reject ≡ untypable
nested-reject-verdict = refl
