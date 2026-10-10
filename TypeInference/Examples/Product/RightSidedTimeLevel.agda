--------------------------------------------------------------------
-- Inference at right-sided time paired with a security level     --
--                                                                --
-- `([0, n ] , ℓ)`: at most `n` ticks, touching nothing above     --
-- `ℓ`. The sensor node's operations are graded by the time they  --
-- may take at worst: `read` 1 and `write` 3 at `Low`, `send` 6   --
-- at `High` (`Specs`). The unit is least and `_·_` commutes.     --
--                                                                --
-- A box at `([0, 8 ] , Low)` is a session token: claimable while --
-- at most eight ticks have passed and nothing above `Low` has    --
-- been touched since it was boxed. A claim is refused for being  --
-- late or for being tainted; there is no early one.              --
--------------------------------------------------------------------

open import Data.Maybe.Base using (just)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import TypeInference.Scopes using (∅ˢ)

open import Syntax.Durations.Nat using (ℕᴰ-stepped)
open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.RightSided using ([0,_]; ↑_)
open import Syntax.Grades.Example.SecurityLevel using (Low; High)
open import Syntax.Grades.Example.Worked.Operations using (read; write; send)

open import TypeInference.Examples.Specs using (module Product-RightSidedTimeLevel)

module TypeInference.Examples.Product.RightSidedTimeLevel where

open Product-RightSidedTimeLevel using (spec; enum)
open LanguageSpec spec using (Grades; Ops)
open GradeSystemInterface Grades using (_·ₑ_; _⊔ₑ_)
open Operations Ops using (op-grade)

open import TypeInference.OpenSyntax.Grades   spec using (RExp; rconst)
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Product spec enum ℕᴰ-stepped

-- the token

token : RExp ∅ˢ
token = rconst ([0, ↑ 8 ] , Low)

------------------------------------------------------------------
-- 1. Claimed early and on time; late is refused, `[0, 9 ]` not
-- being below `[0, 8 ]`

early-reported : schemeOf (infer [] (embargoed token 2)) ≡ just (expected-embargoed 2)
early-reported = refl

early-derivable : Typable [] (embargoed token 2)
early-derivable = embargoed-typable _ 2 _

on-time-reported : schemeOf (infer [] (embargoed token 8)) ≡ just (expected-embargoed 8)
on-time-reported = refl

late-verdict : infer [] (embargoed token 9) ≡ untypable
late-verdict = refl

late-not-typable : ¬ Typable [] (embargoed token 9)
late-not-typable = infer-untypable [] (embargoed token 9) late-verdict

------------------------------------------------------------------
-- 2. After a store and three ticks, `([0, 6 ] , Low)`, the claim is
-- in time and clean; right after a transmission, `([0, 6 ] , High)`,
-- it is in time and tainted

stored : op-grade write ·ₑ ([0, ↑ 3 ] , Low) ≡ ([0, ↑ 6 ] , Low)
stored = refl

stored-reported :
  schemeOf (infer [] (transmitted token write 3)) ≡ just (expected-transmitted write 3)
stored-reported = refl

stored-derivable : Typable [] (transmitted token write 3)
stored-derivable = transmitted-typable _ write 3 _

sent : op-grade send ·ₑ ([0, ↑ 0 ] , Low) ≡ ([0, ↑ 6 ] , High)
sent = refl

sent-verdict : infer [] (transmitted token send 0) ≡ untypable
sent-verdict = refl

sent-not-typable : ¬ Typable [] (transmitted token send 0)
sent-not-typable = infer-untypable [] (transmitted token send 0) sent-verdict

------------------------------------------------------------------
-- 3. Reading, then storing or transmitting: the join is the longer
-- time and the higher level

joined : op-grade read ·ₑ (op-grade write ⊔ₑ op-grade send) ≡ ([0, ↑ 7 ] , High)
joined = refl

joined-claim-reported :
  schemeOf (infer [] (joined-claim read write send)) ≡ just (expected-joined-claim read write send)
joined-claim-reported = refl

------------------------------------------------------------------
-- 4. Publishing after a transmission: the token must outlast `f` and
-- `([0, 6 ] , High)`

publish-reported : schemeOf (infer [] (publish send)) ≡ just (expected-publish send)
publish-reported = refl

------------------------------------------------------------------
-- 5. A reading goes stale after any operation: a store takes time,
-- `[0, 3 ] ≾ [0, 0 ]` failing, and a transmission time and `High`

twice-write-verdict : infer [] (twice write) ≡ untypable
twice-write-verdict = refl

twice-write-not-typable : ¬ Typable [] (twice write)
twice-write-not-typable = infer-untypable [] (twice write) twice-write-verdict

twice-send-verdict : infer [] (twice send) ≡ untypable
twice-send-verdict = refl

twice-send-not-typable : ¬ Typable [] (twice send)
twice-send-not-typable = infer-untypable [] (twice send) twice-send-verdict
