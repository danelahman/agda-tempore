--------------------------------------------------------------------
-- Boxes at timed traces, coverage order                          --
--                                                                --
-- A box is a demand, claimable once the run that elapsed covers  --
-- it; `n` ticks are covered by idling or by operations at        --
-- `costˡᵒ` (read 1, write 2, send 4). Every run covers the unit, --
-- so nothing goes stale. As at the left-sided intervals, an      --
-- early claim is refused and there is no late one.               --
--------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)
open import Grades.Base
open import Language.Spec

open import Util.Equality

open import Grades.Examples.Worked.Operations using (read; write; send)

open import PolymorphicCalculus.Examples.Specs using (module Traces-Timed-LeftSided)

module PolymorphicCalculus.Examples.Boxes.Traces.Timed.LeftSided where

open Traces-Timed-LeftSided using (spec; hints; enum)
open LanguageSpec spec using (Grades)
open GradeSystemInterface Grades using (uᵣ; ⊤ᵣ)

open import PolymorphicCalculus.Syntax.Grades   spec using (rconst)
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Boxes spec hints enum ℕᴰ-stepped

------------------------------------------------------------------
-- 1. Surviving time: nothing goes stale, so a function argument
-- may be called after a tick, boxed or not

stale-call-reported : schemeOf (infer [] stale-call) ≡ just expected-stale-call
stale-call-reported = refl

stale-call-derivable : Typable [] stale-call
stale-call-derivable = stale-call-typable _

boxed-call-reported : schemeOf (infer [] boxed-call) ≡ just expected-stale-call
boxed-call-reported = refl

boxed-call-derivable : Typable [] boxed-call
boxed-call-derivable = boxed-call-typable _

handed-box-call-reported : schemeOf (infer [] handed-box-call) ≡ just expected-handed-box-call
handed-box-call-reported = refl

-- the var-rule disjunction holds on its grade

boxing-an-argument-reported :
  schemeOf (infer [] boxing-an-argument) ≡ just expected-boxing-anything
boxing-an-argument-reported = refl

------------------------------------------------------------------
-- 2. A promise of three: claimable after three and after four
-- ticks, not after two

-- the early claim fails its premise `⟨ 2 ⟩ ≾ ⟨ 3 ⟩`

claim-early-verdict : infer [] (claim-after 2) ≡ untypable
claim-early-verdict = refl

claim-early-not-typable : ¬ Typable [] (claim-after 2)
claim-early-not-typable = infer-untypable [] (claim-after 2) claim-early-verdict

claim-on-time-reported : schemeOf (infer [] (claim-after 3)) ≡ just (expected-claim-after 3)
claim-on-time-reported = refl

claim-late-reported : schemeOf (infer [] (claim-after 4)) ≡ just (expected-claim-after 4)
claim-late-reported = refl

claim-late-derivable : Typable [] (claim-after 4)
claim-late-derivable = claim-after-typable 4 _

------------------------------------------------------------------
-- 3. Inferred grades: a demand covered by two ticks

inferred-grade-reported : schemeOf (infer [] inferred-grade) ≡ just expected-inferred-grade
inferred-grade-reported = refl

kept-and-claimed-reported :
  schemeOf (infer [] kept-and-claimed) ≡ just expected-kept-and-claimed
kept-and-claimed-reported = refl

------------------------------------------------------------------
-- 4. A box escaping through `return`: claimed on time; claimed
-- early, it is refuted by the ordering its two bounds entail

escaping-reported : schemeOf (infer [] (escaping-after 2)) ≡ just (expected-escaping 2)
escaping-reported = refl

escaping-early-verdict : infer [] (escaping-after 1) ≡ untypable
escaping-early-verdict = refl

escaping-early-not-typable : ¬ Typable [] (escaping-after 1)
escaping-early-not-typable = infer-untypable [] (escaping-after 1) escaping-early-verdict

------------------------------------------------------------------
-- 5. Both branches: the join is the smaller demand, one tick

branches-reported : schemeOf (infer [] branches) ≡ just expected-branches
branches-reported = refl

------------------------------------------------------------------
-- 6. A demand for two ticks is covered by a store, at 2, or a
-- transmission, at 4, not by a reading, at 1

read-too-early-verdict : infer [] (op-licensed read) ≡ untypable
read-too-early-verdict = refl

read-too-early-not-typable : ¬ Typable [] (op-licensed read)
read-too-early-not-typable = infer-untypable [] (op-licensed read) read-too-early-verdict

write-licenses-reported : schemeOf (infer [] (op-licensed write)) ≡ just (expected-op-licensed write)
write-licenses-reported = refl

write-licenses-derivable : Typable [] (op-licensed write)
write-licenses-derivable = op-licensed-typable write _

send-licenses-reported : schemeOf (infer [] (op-licensed send)) ≡ just (expected-op-licensed send)
send-licenses-reported = refl

send-licenses-derivable : Typable [] (op-licensed send)
send-licenses-derivable = op-licensed-typable send _

------------------------------------------------------------------
-- 7. Nested boxes, passed in or built in place

nested-reported : schemeOf (infer [] nested) ≡ just expected-nested
nested-reported = refl

nesting-reported : schemeOf (infer [] nesting) ≡ just expected-nesting
nesting-reported = refl

nesting-derivable : Typable [] nesting
nesting-derivable = nesting-typable _

------------------------------------------------------------------
-- 8. Inside a clause `⊤ᵣ` has elapsed, the unit: a box demanding
-- nothing may be claimed there, one demanding a tick may not

claimed-at-u-reported :
  schemeOf (infer [] (claimed-in-clause (rconst uᵣ))) ≡ just expected-claimed-in-clause
claimed-at-u-reported = refl

claimed-at-u-derivable : Typable [] (claimed-in-clause (rconst uᵣ))
claimed-at-u-derivable = claimed-in-clause-typable uᵣ _

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
-- 9. An annotated box: claimed at the annotation's grade; a promise
-- of three re-annotated as a promise of four is claimable after four
-- ticks, not after three

annotated-claim-reported :
  schemeOf (infer [] annotated-claim) ≡ just expected-annotated-claim
annotated-claim-reported = refl

relabelled-on-time-reported :
  schemeOf (infer [] (relabelled 4 4)) ≡ just (expected-relabelled 4)
relabelled-on-time-reported = refl

relabelled-on-time-derivable : Typable [] (relabelled 4 4)
relabelled-on-time-derivable = relabelled-typable 4 4 _ _

relabelled-early-verdict : infer [] (relabelled 4 3) ≡ untypable
relabelled-early-verdict = refl

relabelled-early-not-typable : ¬ Typable [] (relabelled 4 3)
relabelled-early-not-typable = infer-untypable [] (relabelled 4 3) relabelled-early-verdict
