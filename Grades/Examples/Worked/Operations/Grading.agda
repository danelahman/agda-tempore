------------------------------------------------------------------------
-- The operations of the sensor node, graded at example grades.       --
--                                                                    --
-- Each submodule gives `opTime`, the effect grade of each operation  --
-- at one grade, as the typing examples                               --
-- (`ClosedCalculus.Examples.Typing`) and the inference examples      --
-- (`OpenCalculus.Examples.Specs`) use it.                            --
------------------------------------------------------------------------

module Grades.Examples.Worked.Operations.Grading where

open import Data.Product using (_×_; _,_)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; fast; ⌈_⌉)
open import Grades.Examples.Worked.Operations.Footprint using (touches)

------------------------------------------------------------------------
-- Right-sided time: the time an operation may take at worst

module Time-RightSided where

  open import Grades.Examples.Time.RightSided using (𝕀ᵣ; ↑_; [0,_])

  opTime : Op → 𝕀ᵣ
  opTime read  = [0, ↑ 1 ]
  opTime write = [0, ↑ 3 ]
  opTime send  = [0, ↑ 6 ]

------------------------------------------------------------------------
-- Left-sided time: the time an operation is guaranteed to take

module Time-LeftSided where

  open import Grades.Examples.Time.LeftSided using (𝕀; [_,+∞⟩)

  opTime : Op → 𝕀
  opTime read  = [ 1 ,+∞⟩
  opTime write = [ 2 ,+∞⟩
  opTime send  = [ 4 ,+∞⟩

------------------------------------------------------------------------
-- Two-sided time: the window an operation's execution time falls in

module Time-TwoSided where

  open import Grades.Examples.Time.TwoSidedWithInfinity
    using (Interval∞; ↑_; [_,_])

  opTime : Op → Interval∞
  opTime read  = [ 1 , ↑ 1 ]
  opTime write = [ 2 , ↑ 3 ]
  opTime send  = [ 4 , ↑ 6 ]

------------------------------------------------------------------------
-- Dense right-sided time: the measured worst case

module Time-Dense-RightSided where

  open import Grades.Examples.Time.Dense.RightSided using (𝕀ᵣ; ↑_; _/_; [0,_])

  opTime : Op → 𝕀ᵣ
  opTime read  = [0, ↑ (1 / 2) ]
  opTime write = [0, ↑ (5 / 2) ]
  opTime send  = [0, ↑ (11 / 2) ]

------------------------------------------------------------------------
-- Right-sided timed traces: the run that performs an operation

module Traces-Timed-RightSided where

  open import Grades.Examples.Worked.Traces.Timed.RightSided
    using (Bounds; within_; Antichain; ⟅_⟆)

  opTime₀ : Op → Antichain
  opTime₀ o = ⟅ ⌈ o ⌉ ⟆

  opTime : Op → Bounds
  opTime o = within (opTime₀ o)

------------------------------------------------------------------------
-- Left-sided timed traces: the run that performs an operation

module Traces-Timed-LeftSided where

  open import Grades.Examples.Worked.Traces.Timed.LeftSided
    using (Antichain; ⟅_⟆)

  opTime : Op → Antichain
  opTime o = ⟅ ⌈ o ⌉ ⟆

------------------------------------------------------------------------
-- Left-sided time with a security level: guaranteed time and the
-- level touched

module Product-LeftSidedTimeLevel where

  open import Grades.Examples.Time.LeftSided using (𝕀; [_,+∞⟩)
  open import Grades.Examples.SecurityLevel using (LowHigh)

  opTime : Op → 𝕀 × LowHigh
  opTime o = ([ fast o ,+∞⟩ , touches o)
