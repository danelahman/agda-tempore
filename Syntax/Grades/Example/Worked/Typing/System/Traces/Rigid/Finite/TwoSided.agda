------------------------------------------------------------------------
-- Typed example computations over the duration-hull system of the    --
-- rigid finite-expression intervals, in dense time.                  --
--                                                                    --
-- Effect grades are consistent pairs of a lower and an upper bound   --
-- over interval letters, each operation graded by itself at both;    --
-- resource grades are intervals of dense time, and an effect grade   --
-- is measured by its duration hull. A box at the window between one  --
-- and three units may be opened after a reading and a wait of a      --
-- unit; right after the reading it may not, too little time being    --
-- certain to have passed, nor after a reading and a transmission,    --
-- too much possibly having passed. The effect grade records the run  --
-- itself, its two ends measured apart.                               --
--                                                                    --
-- Reading takes more than a quarter and at most half a unit, writing --
-- one to two units, sending two to four.                             --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.System.Traces.Rigid.Finite.TwoSided where

open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Syntax.Grades using (module Grade)
open import Syntax.Grades.Example.Time.Dense.TwoSided
  using (Interval; [_,_]; ]_,_]; ↑_; _/_; #_; _⊆ⁱ_; _⊆ⁱ?_)

open import Syntax.Grades.Example.Worked.Operations using (Op; read; write; send)
open import Syntax.Grades.Example.Worked.Typing.Traces.Rigid.Finite.TwoSided
  using (code; name; name-code; code-name; running)

import Syntax.Grades.Example.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running as L
import Syntax.Grades.Example.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running as U
open import Syntax.Grades.Example.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
  using (two-sided; operation; perform; delay) renaming ([_,_] to [_,_]ᵍ)
open import Syntax.Grades.Example.System.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
  using (intervalRunsToIntervalsGradeSystem)

-- containments of intervals, decided

⊆! : {i j : Interval} {w : True (i ⊆ⁱ? j)} → i ⊆ⁱ j
⊆! {w = w} = toWitness w

⊈! : {i j : Interval} {w : False (i ⊆ⁱ? j)} → ¬ (i ⊆ⁱ j)
⊈! {w = w} = toWitnessFalse w

------------------------------------------------------------------------
-- The operations, graded by themselves at both ends

opTime : Op → Grade.Carrier two-sided
opTime = operation

open import Syntax.Grades.Example.Worked.Typing.System
  intervalRunsToIntervalsGradeSystem opTime
  hiding (_/_)

------------------------------------------------------------------------
-- A box at the window between one and three units

window : R
window = [ # 1 , ↑ # 3 ]

-- opened after a reading and a wait of a unit: more than one and a
-- quarter, at most one and a half units have passed

in-window : [] ⊢C⦂ Unit ‼ _
in-window =
  box window (const 42)      -- ∷ [ window ] Reading
    (perform read ⋆          -- ⟨ ∣ opTime read ∣ ⟩ ∷ Reading
      (delay (# 1)           -- ⟨ of-dur 1 ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ⊆! (<:ᵛ-refl _)
                             -- ∷ Reading
          (perform write here (return ⋆)))))

-- right after the reading, half a unit at most has passed

too-soon : ¬ (uᵣ ·ᵣ mapᵉ (opTime read) ≾ᵣ window)
too-soon = ⊈!

-- after a reading and a transmission, up to four and a half units may
-- have passed

too-late : ¬ (uᵣ ·ᵣ mapᵉ (opTime read) ·ᵣ mapᵉ (opTime send) ≾ᵣ window)
too-late = ⊈!

-- the effect grade of the run is the run itself, at both ends

run : E
run = [ L.⌜ L.‵_ {L.lower} read L.· L.!≥ (# 1) L.· L.‵_ {L.lower} write ⌝
      , U.⌜ U.‵_ {U.upper} read U.· U.!≤ (# 1) U.· U.‵_ {U.upper} write ⌝
      ]ᵍ

run-measured : mapᵉ run ≡ ] 9 / 4 , ↑ 7 / 2 ]
run-measured = refl

run-is-delayed : run ≃ₑ opTime read ·ₑ of-durᵉ (# 1) ·ₑ opTime write
run-is-delayed = _
