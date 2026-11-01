------------------------------------------------------------------------
-- Boxes at timed traces, allowance order                             --
--                                                                    --
-- A box is a permit, claimable while the elapsed run stays within    --
-- it; operations cost `costʰⁱ` (read 1, write 3, send 6). No         --
-- non-eternal variable survives a tick, so `stale-call`,             --
-- `boxed-call` and `nesting` are refuted, and late claims are        --
-- refused.                                                           --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)
open import Grades.Base
open import Language.Spec

open import Util.Equality

open import Grades.Examples.Worked.Operations using (read; write; send)

open import PolymorphicCalculus.Examples.Specs using (module Traces-Timed-RightSided)

module PolymorphicCalculus.Examples.Boxes.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; hints; enum)
open LanguageSpec spec using (Grades)
open GradeSystemInterface Grades using (𝟏ᵣ; ⊤ᵣ)

open import PolymorphicCalculus.Syntax.Grades   spec using (rconst; ∣_∣̂ᵉ; _·̂ᵣ_; _·̂ₑ_)
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Boxes spec hints enum ℕᴰ-stepped
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- 1. A function argument used after a tick fails `⟨ 1 ⟩ ≾ 𝟏ᵣ`, boxed
-- or not

stale-call-verdict : infer [] stale-call ≡ untypable
stale-call-verdict = refl

stale-call-not-typable : ¬ Typable [] stale-call
stale-call-not-typable = infer-untypable [] stale-call stale-call-verdict

boxed-call-verdict : infer [] boxed-call ≡ untypable
boxed-call-verdict = refl

boxed-call-not-typable : ¬ Typable [] boxed-call
boxed-call-not-typable = infer-untypable [] boxed-call boxed-call-verdict

handed-box-call-reported : schemeOf (infer [] handed-box-call) ≡ just expected-handed-box-call
handed-box-call-reported = refl

-- a boxed argument is used after a tick: it has to be eternal

boxing-an-argument-reported :
  schemeOf (infer [] boxing-an-argument) ≡ just expected-boxing-an-eternal
boxing-an-argument-reported = refl

------------------------------------------------------------------
-- 2. A permit of three: claimable after two or three ticks, not four

claim-early-reported : schemeOf (infer [] (claim-after 2)) ≡ just (expected-claim-after 2)
claim-early-reported = refl

claim-early-derivable : Typable [] (claim-after 2)
claim-early-derivable = claim-after-typable 2 _

claim-on-time-reported : schemeOf (infer [] (claim-after 3)) ≡ just (expected-claim-after 3)
claim-on-time-reported = refl

-- the late claim fails its premise `⟨ 4 ⟩ ≾ ⟨ 3 ⟩`

claim-late-verdict : infer [] (claim-after 4) ≡ untypable
claim-late-verdict = refl

claim-late-not-typable : ¬ Typable [] (claim-after 4)
claim-late-not-typable = infer-untypable [] (claim-after 4) claim-late-verdict

------------------------------------------------------------------
-- 3. Inferred grades: a budget of at least two ticks

inferred-grade-reported : schemeOf (infer [] inferred-grade) ≡ just expected-inferred-grade
inferred-grade-reported = refl

kept-and-claimed-reported :
  schemeOf (infer [] kept-and-claimed) ≡ just expected-kept-and-claimed
kept-and-claimed-reported = refl

------------------------------------------------------------------
-- 4. A box escaping through `return`: typed on time, refuted late

escaping-reported : schemeOf (infer [] (escaping-after 2)) ≡ just (expected-escaping 2)
escaping-reported = refl

escaping-late-verdict : infer [] (escaping-after 4) ≡ untypable
escaping-late-verdict = refl

escaping-late-not-typable : ¬ Typable [] (escaping-after 4)
escaping-late-not-typable = infer-untypable [] (escaping-after 4) escaping-late-verdict

------------------------------------------------------------------
-- 5. Both branches: the join is the larger budget, three ticks

branches-reported : schemeOf (infer [] branches) ≡ just expected-branches
branches-reported = refl

------------------------------------------------------------------
-- 6. A budget of two pays for a reading (1), not a store (3) or a
-- transmission (6)

read-licenses-reported : schemeOf (infer [] (op-licensed read)) ≡ just (expected-op-licensed read)
read-licenses-reported = refl

read-licenses-derivable : Typable [] (op-licensed read)
read-licenses-derivable = op-licensed-typable read _

write-overruns-verdict : infer [] (op-licensed write) ≡ untypable
write-overruns-verdict = refl

write-overruns-not-typable : ¬ Typable [] (op-licensed write)
write-overruns-not-typable = infer-untypable [] (op-licensed write) write-overruns-verdict

send-overruns-verdict : infer [] (op-licensed send) ≡ untypable
send-overruns-verdict = refl

send-overruns-not-typable : ¬ Typable [] (op-licensed send)
send-overruns-not-typable = infer-untypable [] (op-licensed send) send-overruns-verdict

------------------------------------------------------------------
-- 7. Nested boxes: typed; built in place, the inner box goes stale
-- under the outer box's modality

nested-reported : schemeOf (infer [] nested) ≡ just expected-nested
nested-reported = refl

nesting-verdict : infer [] nesting ≡ untypable
nesting-verdict = refl

nesting-not-typable : ¬ Typable [] nesting
nesting-not-typable = infer-untypable [] nesting nesting-verdict

------------------------------------------------------------------
-- 8. Inside a clause `⊤ᵣ = unbounded` has elapsed: only an unbounded
-- permit is open

claimed-at-𝟏-verdict : infer [] (claimed-in-clause (rconst 𝟏ᵣ)) ≡ untypable
claimed-at-𝟏-verdict = refl

claimed-at-𝟏-not-typable : ¬ Typable [] (claimed-in-clause (rconst 𝟏ᵣ))
claimed-at-𝟏-not-typable = infer-untypable [] (claimed-in-clause (rconst 𝟏ᵣ)) claimed-at-𝟏-verdict

claimed-at-1-verdict : infer [] (claimed-in-clause ⌜ 1 ⌝ʳ) ≡ untypable
claimed-at-1-verdict = refl

claimed-at-1-not-typable : ¬ Typable [] (claimed-in-clause ⌜ 1 ⌝ʳ)
claimed-at-1-not-typable = infer-untypable [] (claimed-in-clause ⌜ 1 ⌝ʳ) claimed-at-1-verdict

claimed-at-⊤-reported :
  schemeOf (infer [] (claimed-in-clause (rconst ⊤ᵣ))) ≡ just expected-claimed-in-clause
claimed-at-⊤-reported = refl

handed-to-clause-reported : schemeOf (infer [] handed-to-clause) ≡ just expected-handed-to-clause
handed-to-clause-reported = refl

------------------------------------------------------------------
-- 9. An annotated box; a permit of three re-annotated as one of two
-- is claimable after two ticks, not three

annotated-claim-reported :
  schemeOf (infer [] annotated-claim) ≡ just expected-annotated-claim
annotated-claim-reported = refl

relabelled-on-time-reported :
  schemeOf (infer [] (relabelled 2 2)) ≡ just (expected-relabelled 2)
relabelled-on-time-reported = refl

relabelled-on-time-derivable : Typable [] (relabelled 2 2)
relabelled-on-time-derivable = relabelled-typable 2 2 _ _

relabelled-late-verdict : infer [] (relabelled 2 3) ≡ untypable
relabelled-late-verdict = refl

relabelled-late-not-typable : ¬ Typable [] (relabelled 2 3)
relabelled-late-not-typable = infer-untypable [] (relabelled 2 3) relabelled-late-verdict
