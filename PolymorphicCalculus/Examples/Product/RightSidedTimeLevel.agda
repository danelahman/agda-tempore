--------------------------------------------------------------------
-- Inference at right-sided time paired with a security level     --
--                                                                --
-- `([0, n ] , ℓ)`: at most `n` ticks, touching nothing above     --
-- `ℓ`; `read` 1 and `write` 3 at `Low`, `send` 6 at `High`. A    --
-- box at `([0, 8 ] , Low)` is a session token, refused when      --
-- late or tainted.                                               --
--------------------------------------------------------------------

open import Data.Maybe.Base using (just)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes using (∅ˢ)

open import Grades.Durations.Nat using (ℕᴰ-stepped)
open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Grades.Examples.Time.RightSided using ([0,_]; ↑_)
open import Grades.Examples.SecurityLevel using (Low; High)
open import Grades.Examples.Worked.Operations using (read; write; send)

open import PolymorphicCalculus.Examples.Specs using (module Product-RightSidedTimeLevel)

module PolymorphicCalculus.Examples.Product.RightSidedTimeLevel where

open Product-RightSidedTimeLevel using (spec; hints; enum)
open LanguageSpec spec using (Grades; Ops)
open GradeSystemInterface Grades using (_·ₑ_; _⊔ₑ_)
open Operations Ops using (op-grade)

open import PolymorphicCalculus.Syntax.Grades   spec using (RExp; rconst)
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Product spec hints enum ℕᴰ-stepped

-- the token

token : RExp ∅ˢ
token = rconst ([0, ↑ 8 ] , Low)

------------------------------------------------------------------
-- 1. Claimed early and on time; refused late

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
-- 2. Clean after a store and three ticks, `([0, 6 ] , Low)`; tainted
-- after a transmission, `([0, 6 ] , High)`

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
-- 4. The token must outlast `f` and `([0, 6 ] , High)`

publish-reported : schemeOf (infer [] (publish send)) ≡ just (expected-publish send)
publish-reported = refl

------------------------------------------------------------------
-- 5. A reading goes stale after any operation

twice-write-verdict : infer [] (twice write) ≡ untypable
twice-write-verdict = refl

twice-write-not-typable : ¬ Typable [] (twice write)
twice-write-not-typable = infer-untypable [] (twice write) twice-write-verdict

twice-send-verdict : infer [] (twice send) ≡ untypable
twice-send-verdict = refl

twice-send-not-typable : ¬ Typable [] (twice send)
twice-send-not-typable = infer-untypable [] (twice send) twice-send-verdict
