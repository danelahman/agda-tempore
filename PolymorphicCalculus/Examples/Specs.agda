------------------------------------------------------------------------
-- The languages the inference examples run in                        --
--                                                                    --
-- The sensor node's language (`Language.Examples.SensorNode`), with  --
-- the operation times of `Worked.Operations.Grading`, at several     --
-- grades. Each grade is a module giving the language `spec`, the     --
-- solver's `hints` and an enumeration `enum` of the operations.      --
--                                                                    --
-- The four main grades cover the two properties the solver reads     --
-- from the hints: whether the unit is least (`𝟏-least?`) and whether --
-- multiplication commutes (`·-comm?`).                               --
--                                                                    --
--   grade                      𝟏-least?   ·-comm?                    --
--   Time/UpperBound            yes        yes                        --
--   Time/LowerBound             no         yes                       --
--   Traces/Banked/UpperBound    yes        no                        --
--   Traces/Banked/LowerBound     no         no                       --
--                                                                    --
-- The others are time paired with a lattice (`Footprint`)            --
-- and dense time, each on both sides.                                --
--                                                                    --
-- The hints are `identityʰ`, with the grades the solver may try as   --
-- candidates: at time, the bounds `0, …, s+1` for constants summing  --
-- to `s` (a grid at dense time); at the products, these paired with  --
-- both levels; at the timed traces, none.                            --
------------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

open import Util.Equality

open import Grades.Hints using (SystemHints; noGradeHints)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import Grades.Examples.System.Identity using (identityʰ; noWitnesses)
open import Grades.Product using (_×ʷ_)
open import Language.Spec using (LanguageSpec)
import Grades.Examples.Worked.Operations.Grading as Grading

module PolymorphicCalculus.Examples.Specs where

-- The sensor alphabet, enumerated

sensor-ops : List Op
sensor-ops = read ∷ write ∷ send ∷ []

sensor-complete : (op : Op) → op ∈ sensor-ops
sensor-complete read  = here refl
sensor-complete write = there (here refl)
sensor-complete send  = there (there (here refl))

module Time-UpperBound where

  open import Grades.Examples.Time.UpperBound
    using (upper-bounds; upper-boundsʰ; upper-bound-witnesses)
  open Grading.Time-UpperBound using (opTime)
  open import Language.Examples.SensorNode.Identity upper-bounds opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ upper-boundsʰ upper-bound-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Time-LowerBound where

  open import Grades.Examples.Time.LowerBound
    using (lower-bounds; lower-boundsʰ; lower-bound-witnesses)
  open Grading.Time-LowerBound using (opTime)
  open import Language.Examples.SensorNode.Identity lower-bounds opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ lower-boundsʰ lower-bound-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Banked-UpperBound where

  open import Grades.Examples.Worked.Traces.Banked.UpperBound using (upper-bound; upper-boundʰ)
  open Grading.Traces-Banked-UpperBound using (opTime)
  open import Language.Examples.SensorNode.Identity upper-bound opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ upper-boundʰ noWitnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Banked-LowerBound where

  open import Grades.Examples.Worked.Traces.Banked.LowerBound using (lower-bound)
  open Grading.Traces-Banked-LowerBound using (opTime)
  open import Language.Examples.SensorNode.Identity lower-bound opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ noGradeHints noWitnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-TimeLowerBoundLattice where

  open import Grades.Examples.Product.TimeLowerBoundLattice
    using (time-lower-bound×low-high; time-lower-bound×low-highʰ)
  open import Grades.Examples.Time.LowerBound using (lower-bound-witnesses)
  open import Grades.Examples.Lattice using (low-high-witnesses)
  open Grading.Product-TimeLowerBoundLattice using (opTime)
  open import Language.Examples.SensorNode.Identity time-lower-bound×low-high opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ time-lower-bound×low-highʰ (lower-bound-witnesses ×ʷ low-high-witnesses)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-TimeUpperBoundLattice where

  open import Data.Product using (_×_; _,_)
  open import Grades.Examples.Product.TimeUpperBoundLattice
    using (time-upper-bound×low-high; time-upper-bound×low-highʰ)
  open import Grades.Examples.Time.UpperBound using (𝕀ᵣ; [0,_]; ↑_; upper-bound-witnesses)
  open import Grades.Examples.Lattice using (LowHigh; low-high-witnesses)
  open import Grades.Examples.Worked.Operations using (slow)
  open import Grades.Examples.Worked.Operations.Footprint using (touches)

  -- the time an operation may take at worst, and the level it touches

  opTime : Op → 𝕀ᵣ × LowHigh
  opTime o = ([0, ↑ slow o ] , touches o)

  open import Language.Examples.SensorNode.Identity time-upper-bound×low-high opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ time-upper-bound×low-highʰ (upper-bound-witnesses ×ʷ low-high-witnesses)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Rational-Time-UpperBound where

  open import Grades.Examples.Time.Rational.UpperBound
    using (rational-upper-bounds; rational-upper-boundsʰ; rational-upper-bound-witnesses)
  open Grading.Time-Rational-UpperBound using (opTime)
  open import Language.Examples.SensorNode.Identity rational-upper-bounds opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ rational-upper-boundsʰ rational-upper-bound-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Rational-Time-LowerBound where

  open import Grades.Base using (GradeMorphism)
  open import Grades.Examples.Time.Rational.LowerBound
    using (𝕀; rational-lower-bounds; rational-lower-boundsʰ; rational-lower-bound-witnesses;
           lower-bound→rational)
  module Discrete = Grading.Time-LowerBound

  -- the discrete figures, read in dense time

  opTime : Op → 𝕀
  opTime o = GradeMorphism.map lower-bound→rational (Discrete.opTime o)

  open import Language.Examples.SensorNode.Identity rational-lower-bounds opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ rational-lower-boundsʰ rational-lower-bound-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete
