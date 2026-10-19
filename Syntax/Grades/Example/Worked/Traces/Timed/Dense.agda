------------------------------------------------------------------------
-- Worked instances of the timed trace grades in dense time.          --
--                                                                    --
-- The sensor node of `Worked.Operations` once more, now with running --
-- times in units of dense time, each an interval with open or closed --
-- ends:                                                              --
--                                                                    --
--   read   [1/2, 1]     between half a unit and one                  --
--   write  ]1/4, 3/2]   more than a quarter, at most one and a half  --
--   send   [1, 2]                                                    --
--                                                                    --
-- An allowance charges an operation the upper end of its running    --
-- time (`RunningTimes.costʰⁱ`), and delays are rational. The whole-  --
-- step grade reads in dense time along the inclusion of durations    --
-- (`Timed.Dense`). Every ordering is established by the decision     --
-- procedure of the grade.                                            --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Timed.Dense where

open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Properties using (<⇒≢)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Syntax.Grades using (GradeMorphism)
open import Syntax.Durations.Nat using (ℕᵀ)
open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᵀ)
open import Syntax.Grades.Example.Time.Dense.TwoSided
  using (Interval; [_,_]; ]_,_]; ↑_; _/_; #_; nonZero; fin; _⊑ʰ?_; 0⁺; hi)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; read; write; send)
import Syntax.Grades.Example.Worked.Operations as Steps

------------------------------------------------------------------------
-- Running times

open import Syntax.Grades.Traces.RunningTimes ℚ≥0ᵀ Op
  using (RunningTimes; Bounded)
  renaming (fin to bounded)

rt : Op → Interval
rt read  = [ 1 / 2 , ↑ # 1 ]
rt write = ] 1 / 4 , ↑ 3 / 2 ]
rt send  = [ # 1 , ↑ # 2 ]

running-times : RunningTimes
running-times = record
  { rt            = rt
  ; rt-bounded    = λ { read → bounded _ ; write → bounded _ ; send → bounded _ }
  ; rt-takes-time = λ { read  → toWitnessFalse {a? = hi (rt read)  ⊑ʰ? fin 0⁺} _
                      ; write → toWitnessFalse {a? = hi (rt write) ⊑ʰ? fin 0⁺} _
                      ; send  → toWitnessFalse {a? = hi (rt send)  ⊑ʰ? fin 0⁺} _ }
  }

open RunningTimes running-times using (costˡᵒ; costʰⁱ; costʰⁱ-pos)

-- the costs are the closed hull: an open end still bounds the time

write-costs : (costˡᵒ write ≡ 1 / 4) × (costʰⁱ write ≡ 3 / 2)
write-costs = refl , refl

------------------------------------------------------------------------
-- The grade of upper bounds in dense time

open import Syntax.Grades.Traces.Sets ℚ≥0ᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (Trace; ⌈_⌉; ⟨_⟩; _∙_)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  ℚ≥0ᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (Bounds; within_; _≾_; _≾?_; Antichain; acSet)

⟅_⟆ : Trace → Antichain
⟅ t ⟆ = acSet (t ∷ []) tt

holds : {P Q : Bounds} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : Bounds} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

-- a reading and an idle half unit fit a budget of one and a half after
-- the reading

idle-after-reading :
  within ⟅ ⌈ read ⌉ ∙ ⟨ 1 / 2 ⟩ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 / 2 ⟩ ⟆
idle-after-reading = holds

-- a write is charged its upper end, one and a half units, open lower
-- end or not

storing-fits :
  within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 3 / 2 ⟩ ⟆
storing-fits = holds

storing-overruns :
  ¬ (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆ ≾ within ⟅ ⌈ read ⌉ ∙ ⟨ 5 / 4 ⟩ ⟆)
storing-overruns = fails

-- two half-unit delays are one delay of a unit

halves : ⟨ 1 / 2 ⟩ ∙ ⟨ 1 / 2 ⟩ ≡ ⟨ # 1 ⟩
halves = refl

------------------------------------------------------------------------
-- Whole steps, read in dense time

open import Syntax.Grades.Example.Traces.Timed.Dense
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans using (module Right)

private
  module W = Right Steps.costʰⁱ (λ o e → <⇒≢ (Steps.costʰⁱ-pos o) (sym e))

-- the duty-cycle bound of `Worked.Traces.Timed.RightSided`, six ticks
-- after a reading, is six units after a reading

duty-cycle :
  GradeMorphism.map W.right-sided→ (W.R₁.within W.R₁.acSet (Steps.⌈ read ⌉ Steps.∙ Steps.⟨ 6 ⟩ ∷ []) tt)
  ≡ W.R₂.within (W.R₂.acSet (⌈ read ⌉ ∙ ⟨ # 6 ⟩ ∷ []) tt)
duty-cycle = refl
