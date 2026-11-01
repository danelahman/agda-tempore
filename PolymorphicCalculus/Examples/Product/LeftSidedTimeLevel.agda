------------------------------------------------------------------------
-- Inference at left-sided time paired with a security level          --
--                                                                    --
-- `([ n ,+∞⟩ , ℓ)` is at least `n` ticks, touching nothing above     --
-- `ℓ`; `read` takes 1 and `write` 2 at `Low`, `send` 4 at `High`. A  --
-- box at `([ 5 ,+∞⟩ , Low)` is an embargoed report: claimed on time  --
-- and late, and after a store; refused early, or after a             --
-- transmission. A reading survives a store, not a transmission.      --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes using (∅ˢ)

open import Grades.Durations.Nat using (ℕᴰ-stepped)
open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Grades.Examples.Time.LeftSided using ([_,+∞⟩)
open import Grades.Examples.SecurityLevel using (Low; High)
open import Grades.Examples.Worked.Operations using (read; write; send)

open import PolymorphicCalculus.Examples.Specs using (module Product-LeftSidedTimeLevel)

module PolymorphicCalculus.Examples.Product.LeftSidedTimeLevel where

open Product-LeftSidedTimeLevel using (spec; hints; enum)
open LanguageSpec spec using (Grades; Ops)
open GradeSystemInterface Grades using (_·ₑ_; _⊔ₑ_)
open Operations Ops using (op-grade)

open import PolymorphicCalculus.Syntax.Grades   spec using (RExp; rconst)
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Product spec hints enum ℕᴰ-stepped

-- the report's box

embargo : RExp ∅ˢ
embargo = rconst ([ 5 ,+∞⟩ , Low)

------------------------------------------------------------------
-- 1. Claimed on time and late; refused early

on-time-reported : schemeOf (infer [] (embargoed embargo 5)) ≡ just (expected-embargoed 5)
on-time-reported = refl

late-reported : schemeOf (infer [] (embargoed embargo 7)) ≡ just (expected-embargoed 7)
late-reported = refl

late-derivable : Typable [] (embargoed embargo 7)
late-derivable = embargoed-typable _ 7 _

early-verdict : infer [] (embargoed embargo 4) ≡ untypable
early-verdict = refl

early-not-typable : ¬ Typable [] (embargoed embargo 4)
early-not-typable = infer-untypable [] (embargoed embargo 4) early-verdict

------------------------------------------------------------------
-- 2. Clean after a store and three ticks, `([ 5 ,+∞⟩ , Low)`; tainted
-- after a transmission, `([ 7 ,+∞⟩ , High)`, whatever the delay

stored : op-grade write ·ₑ ([ 3 ,+∞⟩ , Low) ≡ ([ 5 ,+∞⟩ , Low)
stored = refl

stored-reported :
  schemeOf (infer [] (transmitted embargo write 3)) ≡ just (expected-transmitted write 3)
stored-reported = refl

stored-derivable : Typable [] (transmitted embargo write 3)
stored-derivable = transmitted-typable _ write 3 _

sent : op-grade send ·ₑ ([ 3 ,+∞⟩ , Low) ≡ ([ 7 ,+∞⟩ , High)
sent = refl

sent-verdict : infer [] (transmitted embargo send 3) ≡ untypable
sent-verdict = refl

sent-not-typable : ¬ Typable [] (transmitted embargo send 3)
sent-not-typable = infer-untypable [] (transmitted embargo send 3) sent-verdict

------------------------------------------------------------------
-- 3. Reading, then storing or transmitting: the join, three ticks and
-- `High`

joined : op-grade read ·ₑ (op-grade write ⊔ₑ op-grade send) ≡ ([ 3 ,+∞⟩ , High)
joined = refl

joined-claim-reported :
  schemeOf (infer [] (joined-claim read write send)) ≡ just (expected-joined-claim read write send)
joined-claim-reported = refl

------------------------------------------------------------------
-- 4. The report must outlast `f` and `([ 4 ,+∞⟩ , High)`

publish-reported : schemeOf (infer [] (publish send)) ≡ just (expected-publish send)
publish-reported = refl

------------------------------------------------------------------
-- 5. A reading survives a store, not a transmission

twice-write-reported : schemeOf (infer [] (twice write)) ≡ just (expected-twice write)
twice-write-reported = refl

twice-write-derivable : Typable [] (twice write)
twice-write-derivable = twice-typable write _

twice-send-verdict : infer [] (twice send) ≡ untypable
twice-send-verdict = refl

twice-send-not-typable : ¬ Typable [] (twice send)
twice-send-not-typable = infer-untypable [] (twice send) twice-send-verdict
