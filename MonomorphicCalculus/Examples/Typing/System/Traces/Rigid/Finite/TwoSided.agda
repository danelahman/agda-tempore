------------------------------------------------------------------------
-- Typed computations over the duration-hull system of the rigid      --
-- finite-expression intervals, in dense time                         --
--                                                                    --
-- The grade system                                                   --
--   Effect grades are consistent pairs of a lower and an upper bound --
--   over interval letters, each operation graded by itself at both;  --
--   resource grades are intervals of dense time, and an effect grade --
--   is measured by its duration hull.                                --
--                                                                    --
--   Reading takes more than a quarter and at most half a unit,       --
--   writing one to two units, sending two to four.                   --
--                                                                    --
-- What it shows                                                      --
--   A box at the window between one and three units may be opened    --
--   after a reading and a wait of a unit. Right after the reading it --
--   may not, too little time being certain to have passed, nor after --
--   a reading and a transmission, too much possibly having passed.   --
--   The effect grade records the run itself, its two ends measured   --
--   apart.                                                           --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Finite.TwoSided where

open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Grades.Base using (module Grade)
open import Grades.Examples.Time.Dense.TwoSided
  using (Interval; [_,_]; ]_,_]; ↑_; _/_; #_; _⊆ⁱ_; _⊆ⁱ?_)

open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import MonomorphicCalculus.Examples.Typing.Traces.Rigid.Finite.TwoSided
  using (code; name; name-code; code-name; running)

import Grades.Examples.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running as L
import Grades.Examples.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running as U
open import Grades.Examples.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
  using (two-sided; operation; perform; delay) renaming ([_,_] to [_,_]ᵍ)
open import Grades.Examples.System.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
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

open import MonomorphicCalculus.Examples.Typing.System
  intervalRunsToIntervalsGradeSystem opTime
  hiding (_/_)

------------------------------------------------------------------------
-- A box at the window between one and three units

window : R
window = [ # 1 , ↑ # 3 ]

-- opened after a reading and a wait of a unit: more than one and a
-- quarter, at most one and a half units have passed

in-window : [] ⊢ᶜ⦂ unit ! _
in-window =
  box window (const reading 42) -- ∷ [ window ] Reading
    (perform read ⋆             -- ⟨ ∣ opTime read ∣ ⟩ ∷ Reading
      (delay (# 1)              -- ⟨ ι 1 ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ⊆! (<:ᵛ-refl _)
                             -- ∷ Reading
          (perform write here (return ⋆)))))

-- right after the reading, half a unit at most has passed

too-soon : ¬ (𝟏ᵣ ·ᵣ ∣ opTime read ∣ᵉ ≾ᵣ window)
too-soon = ⊈!

-- after a reading and a transmission, up to four and a half units may
-- have passed

too-late : ¬ (𝟏ᵣ ·ᵣ ∣ opTime read ∣ᵉ ·ᵣ ∣ opTime send ∣ᵉ ≾ᵣ window)
too-late = ⊈!

-- the effect grade of the run is the run itself, at both ends

run : E
run = [ L.⌜ L.‵_ {L.lower} read L.· L.idle L.≥ (# 1) L.· L.‵_ {L.lower} write ⌝
      , U.⌜ U.‵_ {U.upper} read U.· U.idle U.≤ (# 1) U.· U.‵_ {U.upper} write ⌝
      ]ᵍ

run-measured : ∣ run ∣ᵉ ≡ ] 9 / 4 , ↑ 7 / 2 ]
run-measured = refl

run-is-delayed : run ≃ₑ opTime read ·ₑ ιₑ (# 1) ·ₑ opTime write
run-is-delayed = _
