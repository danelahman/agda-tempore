------------------------------------------------------------------------
-- The operations of the sensor node, graded at example grades.       --
--                                                                    --
-- Each submodule gives `opTime`, the effect grade of each operation  --
-- at one grade, for the typing examples of the monomorphic calculus  --
-- and the inference examples of the polymorphic calculus.            --
------------------------------------------------------------------------

module Grades.Examples.Worked.Operations.Grading where

open import Data.Product using (_×_; _,_)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; fast; ⌈_⌉)
open import Grades.Examples.Worked.Operations.Footprint using (touches)

------------------------------------------------------------------------
-- Upper bounds on time: the time an operation may take at worst

module Time-UpperBound where

  open import Grades.Examples.Time.UpperBound using (𝕀ᵣ; ↑_; [0,_])

  opTime : Op → 𝕀ᵣ
  opTime read  = [0, ↑ 1 ]
  opTime write = [0, ↑ 3 ]
  opTime send  = [0, ↑ 6 ]

------------------------------------------------------------------------
-- Lower bounds on time: the time an operation is guaranteed to take

module Time-LowerBound where

  open import Grades.Examples.Time.LowerBound using (𝕀; [_,+∞⟩)

  opTime : Op → 𝕀
  opTime read  = [ 1 ,+∞⟩
  opTime write = [ 2 ,+∞⟩
  opTime send  = [ 4 ,+∞⟩

------------------------------------------------------------------------
-- Intervals of time: the window an operation's running time falls in

module Time-Interval where

  open import Grades.Examples.Time.Interval
    using (Interval∞; ↑_; [_,_])

  opTime : Op → Interval∞
  opTime read  = [ 1 , ↑ 1 ]
  opTime write = [ 2 , ↑ 3 ]
  opTime send  = [ 4 , ↑ 6 ]

------------------------------------------------------------------------
-- Rational upper bounds on time: the measured worst case

module Time-Rational-UpperBound where

  open import Grades.Examples.Time.Rational.UpperBound using (𝕀ᵣ; ↑_; _/_; [0,_])

  opTime : Op → 𝕀ᵣ
  opTime read  = [0, ↑ (1 / 2) ]
  opTime write = [0, ↑ (5 / 2) ]
  opTime send  = [0, ↑ (11 / 2) ]

------------------------------------------------------------------------
-- Upper-bound timed traces: the run that performs an operation

module Traces-Banked-UpperBound where

  open import Grades.Examples.Worked.Traces.Banked.UpperBound
    using (Bounds; within_; Antichain; ⟅_⟆)

  opTime₀ : Op → Antichain
  opTime₀ o = ⟅ ⌈ o ⌉ ⟆

  opTime : Op → Bounds
  opTime o = within (opTime₀ o)

------------------------------------------------------------------------
-- Lower-bound timed traces: the run that performs an operation

module Traces-Banked-LowerBound where

  open import Grades.Examples.Worked.Traces.Banked.LowerBound
    using (Antichain; ⟅_⟆)

  opTime : Op → Antichain
  opTime o = ⟅ ⌈ o ⌉ ⟆

------------------------------------------------------------------------
-- Lower bounds on time with a lattice: guaranteed time and the
-- level touched

module Product-TimeLowerBoundLattice where

  open import Grades.Examples.Time.LowerBound using (𝕀; [_,+∞⟩)
  open import Grades.Examples.Lattice using (LowHigh)

  opTime : Op → 𝕀 × LowHigh
  opTime o = ([ fast o ,+∞⟩ , touches o)
