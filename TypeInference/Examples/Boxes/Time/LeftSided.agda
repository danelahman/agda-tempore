------------------------------------------------------------------
-- Boxes at left-sided intervals                                  --
--                                                                --
-- "At least `n` ticks": a box is a promise, claimable once the   --
-- elapsed time is at least its grade, and `var`'s bound          --
-- `ρ ≾ uᵣ` holds at every grade, so nothing goes stale. An early --
-- claim is refused; there is no late one.                        --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations using (read; write; send)

open import TypeInference.Examples.Specs using (module Time-LeftSided)

module TypeInference.Examples.Boxes.Time.LeftSided where

open Time-LeftSided using (spec; enum)
open LanguageSpec spec using (Grades)
open GradeSystemInterface Grades using (uᵣ; ⊤ᵣ)

open import TypeInference.OpenSyntax.Grades   spec using (rconst)
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Boxes spec enum

------------------------------------------------------------------
-- 1. Surviving time: nothing goes stale, so a function argument
-- may be called after a tick, boxed or not

stale-call-reported : report (infer [] stale-call) ≡ just expected-stale-call
stale-call-reported = refl

stale-call-derivable : Typable [] stale-call
stale-call-derivable = stale-call-typable _

boxed-call-reported : report (infer [] boxed-call) ≡ just expected-stale-call
boxed-call-reported = refl

boxed-call-derivable : Typable [] boxed-call
boxed-call-derivable = boxed-call-typable _

handed-box-call-reported : report (infer [] handed-box-call) ≡ just expected-handed-box-call
handed-box-call-reported = refl

-- the var-rule disjunction holds on its grade

boxing-an-argument-reported :
  report (infer [] boxing-an-argument) ≡ just expected-boxing-anything
boxing-an-argument-reported = refl

------------------------------------------------------------------
-- 2. A promise of three: claimable after three and after four
-- ticks, not after two

-- the early claim is reported with the false premise
-- `[ 2 ,+∞⟩ ≾ [ 3 ,+∞⟩`

claim-early-reported : report (infer [] (claim-after 2)) ≡ just (expected-claim-refused 2)
claim-early-reported = refl

claim-early-not-typable : ¬ Typable [] (claim-after 2)
claim-early-not-typable = refuted-by-scheme (claim-after 2) refl

claim-on-time-reported : report (infer [] (claim-after 3)) ≡ just (expected-claim-after 3)
claim-on-time-reported = refl

claim-late-reported : report (infer [] (claim-after 4)) ≡ just (expected-claim-after 4)
claim-late-reported = refl

claim-late-derivable : Typable [] (claim-after 4)
claim-late-derivable = claim-after-typable 4 _

------------------------------------------------------------------
-- 3. Inferred grades: a promise due within two ticks

inferred-grade-reported : report (infer [] inferred-grade) ≡ just expected-inferred-grade
inferred-grade-reported = refl

kept-and-claimed-reported :
  report (infer [] kept-and-claimed) ≡ just expected-kept-and-claimed
kept-and-claimed-reported = refl

------------------------------------------------------------------
-- 4. A box escaping through `return`

escaping-reported : report (infer [] escaping) ≡ just expected-escaping
escaping-reported = refl

------------------------------------------------------------------
-- 5. Both branches: the join is the smaller floor, one tick

branches-reported : report (infer [] branches) ≡ just expected-branches
branches-reported = refl

------------------------------------------------------------------
-- 6. A promise of two is due after a store, `[ 2 ,+∞⟩`, or a
-- transmission, `[ 4 ,+∞⟩`, not after a reading, `[ 1 ,+∞⟩`:
-- `claim-after-sampling-fails` of `Worked/Typing/Time/LeftSided.agda`

read-too-early-reported : report (infer [] (op-licensed read)) ≡ just (expected-op-refused read)
read-too-early-reported = refl

read-too-early-not-typable : ¬ Typable [] (op-licensed read)
read-too-early-not-typable = refuted-by-scheme (op-licensed read) refl

write-licenses-reported : report (infer [] (op-licensed write)) ≡ just (expected-op-licensed write)
write-licenses-reported = refl

write-licenses-derivable : Typable [] (op-licensed write)
write-licenses-derivable = op-licensed-typable write _

send-licenses-reported : report (infer [] (op-licensed send)) ≡ just (expected-op-licensed send)
send-licenses-reported = refl

send-licenses-derivable : Typable [] (op-licensed send)
send-licenses-derivable = op-licensed-typable send _

------------------------------------------------------------------
-- 7. Nested boxes, passed in or built in place

nested-reported : report (infer [] nested) ≡ just expected-nested
nested-reported = refl

nesting-reported : report (infer [] nesting) ≡ just expected-nesting
nesting-reported = refl

nesting-derivable : Typable [] nesting
nesting-derivable = nesting-typable _

------------------------------------------------------------------
-- 8. Inside a clause `⊤ᵣ = [ 0 ,+∞⟩` has elapsed, the unit: a box
-- due at once may be claimed there, one due in a tick may not

claimed-at-u-reported :
  report (infer [] (claimed-in-clause (rconst uᵣ))) ≡ just expected-claimed-in-clause
claimed-at-u-reported = refl

claimed-at-u-derivable : Typable [] (claimed-in-clause (rconst uᵣ))
claimed-at-u-derivable = claimed-in-clause-typable uᵣ _

claimed-at-1-verdict : infer [] (claimed-in-clause ⌜ 1 ⌝ʳ) ≡ untypable
claimed-at-1-verdict = refl

claimed-at-1-not-typable : ¬ Typable [] (claimed-in-clause ⌜ 1 ⌝ʳ)
claimed-at-1-not-typable = infer-untypable [] (claimed-in-clause ⌜ 1 ⌝ʳ) claimed-at-1-verdict

claimed-at-⊤-reported :
  report (infer [] (claimed-in-clause (rconst ⊤ᵣ))) ≡ just expected-claimed-in-clause
claimed-at-⊤-reported = refl

handed-to-clause-reported : report (infer [] handed-to-clause) ≡ just expected-handed-to-clause
handed-to-clause-reported = refl
