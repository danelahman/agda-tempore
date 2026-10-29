------------------------------------------------------------------
-- Boxes at right-sided intervals                               --
--                                                              --
-- "At most `n` ticks": a box is a lease, claimable while the   --
-- elapsed time is at most its grade, and `var`'s bound         --
-- `ρ ≾ uᵣ` holds only at `[0, 0 ]`, so no non-eternal variable --
-- survives a tick. A late claim is refused; there is no early  --
-- one.                                                         --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)
open import Grades.Base
open import Language.Spec

open import Util.Equality

open import Grades.Examples.Worked.Operations using (read; write; send)

open import OpenCalculus.Examples.Specs using (module Time-RightSided)

module OpenCalculus.Examples.Boxes.Time.RightSided where

open Time-RightSided using (spec; hints; enum)
open LanguageSpec spec using (Grades)
open GradeSystemInterface Grades using (uᵣ; ⊤ᵣ)

open import OpenCalculus.Syntax.Grades   spec using (rconst; ∣_∣̂ᵉ; _·̂ᵣ_; _·̂ₑ_)
open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Inference.Principality spec using (Typable; untypable)
open import OpenCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import OpenCalculus.Examples.Boxes spec hints enum ℕᴰ-stepped
open import OpenCalculus.Examples.Variables

------------------------------------------------------------------
-- 1. Boxing to survive time
--
-- A function argument used after a tick fails `var`'s bound
-- `[0, 1 ] ≾ [0, 0 ]`, boxed or not (`reading-stale-after-idling`
-- in `ClosedCalculus/Examples/Typing/Time/RightSided.agda`, at two ticks).

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
-- 2. A lease of three: claimable after two and after three ticks,
-- not after four

claim-early-reported : schemeOf (infer [] (claim-after 2)) ≡ just (expected-claim-after 2)
claim-early-reported = refl

claim-early-derivable : Typable [] (claim-after 2)
claim-early-derivable = claim-after-typable 2 _

claim-on-time-reported : schemeOf (infer [] (claim-after 3)) ≡ just (expected-claim-after 3)
claim-on-time-reported = refl

-- the late claim fails its premise `[0, 4 ] ≾ [0, 3 ]`

claim-late-verdict : infer [] (claim-after 4) ≡ untypable
claim-late-verdict = refl

claim-late-not-typable : ¬ Typable [] (claim-after 4)
claim-late-not-typable = infer-untypable [] (claim-after 4) claim-late-verdict

------------------------------------------------------------------
-- 3. Inferred grades: a lease of at least two ticks

inferred-grade-reported : schemeOf (infer [] inferred-grade) ≡ just expected-inferred-grade
inferred-grade-reported = refl

kept-and-claimed-reported :
  schemeOf (infer [] kept-and-claimed) ≡ just expected-kept-and-claimed
kept-and-claimed-reported = refl

------------------------------------------------------------------
-- 4. A box escaping through `return`: claimed on time; claimed
-- late, it is refuted by the ordering its two bounds entail

escaping-reported : schemeOf (infer [] (escaping-after 2)) ≡ just (expected-escaping 2)
escaping-reported = refl

escaping-late-verdict : infer [] (escaping-after 4) ≡ untypable
escaping-late-verdict = refl

escaping-late-not-typable : ¬ Typable [] (escaping-after 4)
escaping-late-not-typable = infer-untypable [] (escaping-after 4) escaping-late-verdict

------------------------------------------------------------------
-- 5. Both branches: the join is the larger bound, three ticks

branches-reported : schemeOf (infer [] branches) ≡ just expected-branches
branches-reported = refl

------------------------------------------------------------------
-- 6. A lease of two covers a reading, `[0, 1 ]`; a store, `[0, 3 ]`,
-- and a transmission, `[0, 6 ]`, overrun it

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
-- under the outer box's lock

nested-reported : schemeOf (infer [] nested) ≡ just expected-nested
nested-reported = refl

nesting-verdict : infer [] nesting ≡ untypable
nesting-verdict = refl

nesting-not-typable : ¬ Typable [] nesting
nesting-not-typable = infer-untypable [] nesting nesting-verdict

------------------------------------------------------------------
-- 8. Inside a clause `⊤ᵣ = [0, ∞ ]` has elapsed: only a lease of
-- `[0, ∞ ]` is still open. At the unit the premise is
-- `reading-stale-at-⊤` of `ClosedCalculus/Examples/Typing/Time/RightSided.agda`.

claimed-at-u-verdict : infer [] (claimed-in-clause (rconst uᵣ)) ≡ untypable
claimed-at-u-verdict = refl

claimed-at-u-not-typable : ¬ Typable [] (claimed-in-clause (rconst uᵣ))
claimed-at-u-not-typable = infer-untypable [] (claimed-in-clause (rconst uᵣ)) claimed-at-u-verdict

claimed-at-1-verdict : infer [] (claimed-in-clause ⌜ 1 ⌝ʳ) ≡ untypable
claimed-at-1-verdict = refl

claimed-at-1-not-typable : ¬ Typable [] (claimed-in-clause ⌜ 1 ⌝ʳ)
claimed-at-1-not-typable = infer-untypable [] (claimed-in-clause ⌜ 1 ⌝ʳ) claimed-at-1-verdict

claimed-at-⊤-reported :
  schemeOf (infer [] (claimed-in-clause (rconst ⊤ᵣ))) ≡ just expected-claimed-in-clause
claimed-at-⊤-reported = refl

handed-to-clause-reported : schemeOf (infer [] handed-to-clause) ≡ just expected-handed-to-clause
handed-to-clause-reported = refl
