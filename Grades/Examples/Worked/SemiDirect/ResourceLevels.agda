------------------------------------------------------------------------
-- Worked instances of the resource levels.                           --
--                                                                    --
-- Opening a file is `(0 , [1 , 1] , 1)` and closing one              --
-- `(-1 , [-1 , -1] , 0)`. Opening and then closing holds one file at --
-- the peak and releases it, `(0 , [0 , 0] , 1)`; closing and then    --
-- opening dips one below the start, `(-1 , [0 , 0] , 0)`, so `_·_`   --
-- does not commute. A policy "at most two files at a time, all       --
-- released, none closed that was not opened" is `(0 , [0 , 0] , 2)`: --
-- two nested opens meet it, three do not, and neither does closing   --
-- first. A branch joins the ranges: opening a file or not is         --
-- `(0 , [0 , 1] , 1)`. By name, files and sockets are counted apart. --
-- Every ordering is established by the decision procedure of the     --
-- grade, and every computation by reduction.                         --
------------------------------------------------------------------------

module Grades.Examples.Worked.SemiDirect.ResourceLevels where

open import Data.Integer.Base as ℤ using (ℤ; +_)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.SemiDirect.ExtendedInteger
open import Grades.Examples.SemiDirect.ResourceLevels

open import Util.Equality

open Maps ℕ-names using (Map; _∣_; _!_)

private
  module L = Grade (one-resource {ℕᴰ})
  module R = Grade (resource-levels {ℕᴰ})

-- the trough `-a`, the range `[d₁ , d₂]` and the peak `h`

res : (a : ℕ) (d₁ d₂ : ℤ) (h : ℕ) {w : Wellformed ⟨ a ⟩ (fin (ℤ.- d₁)) (fin d₂) ⟨ h ⟩} → Level
res a d₁ d₂ h {w} = levelⁿ ⟨ a ⟩ (fin (ℤ.- d₁)) (fin d₂) ⟨ h ⟩ {w}

holds : (c d : Level) {p : True (c L.≾? d)} → c L.≾ d
holds c d {p} = toWitness p

fails : (c d : Level) {p : False (c L.≾? d)} → ¬ (c L.≾ d)
fails c d {p} = toWitnessFalse p

same : (c d : Level) {p : True (c L.≃? d)} → c L.≃ d
same c d {p} = toWitness p

open-file close-file : Level
open-file  = res 0 (+ 1) (+ 1) 1
close-file = res 1 (ℤ.- + 1) (ℤ.- + 1) 0

-- opening then closing peaks at one file and releases it

open-close : open-file L.· close-file L.≃ res 0 (+ 0) (+ 0) 1
open-close = same (open-file L.· close-file) (res 0 (+ 0) (+ 0) 1)

-- closing then opening dips below the start

close-open : close-file L.· open-file L.≃ res 1 (+ 0) (+ 0) 0
close-open = same (close-file L.· open-file) (res 1 (+ 0) (+ 0) 0)

not-commutative : ¬ (open-file L.· close-file L.≾ close-file L.· open-file)
not-commutative = fails (open-file L.· close-file) (close-file L.· open-file)

-- a policy: at most two files at a time, all released, none closed that
-- was not opened

two-at-a-time : Level
two-at-a-time = res 0 (+ 0) (+ 0) 2

nested : open-file L.· (open-file L.· close-file L.· close-file) L.≾ two-at-a-time
nested = holds (open-file L.· (open-file L.· close-file L.· close-file)) two-at-a-time

three-refused : ¬ (open-file L.· open-file L.· open-file L.· close-file L.· close-file L.· close-file
                   L.≾ two-at-a-time)
three-refused =
  fails (open-file L.· open-file L.· open-file L.· close-file L.· close-file L.· close-file)
        two-at-a-time

close-first-refused : ¬ (close-file L.· open-file L.≾ two-at-a-time)
close-first-refused = fails (close-file L.· open-file) two-at-a-time

-- a branch joins the ranges

branch : open-file L.⊔ L.𝟏 L.≃ res 0 (+ 0) (+ 1) 1
branch = same (open-file L.⊔ L.𝟏) (res 0 (+ 0) (+ 1) 1)

-- the unit is not least: opening is not above it

unit-not-least : ¬ (L.𝟏 L.≾ open-file)
unit-not-least = fails L.𝟏 open-file

-- the unit is the only grade below it: a grade that opens and closes is
-- not

open-close-not-below-unit : ¬ (open-file L.· close-file L.≾ L.𝟏)
open-close-not-below-unit = fails (open-file L.· close-file) L.𝟏

------------------------------------------------------------------------
-- By name: files (0) and sockets (1)

files sockets : ℕ
files   = 0
sockets = 1

-- `x` for the resource `r`, the unit for the others

only : ℕ → Level → Map Level
only r x = L.𝟏 ∣ ((r , x) ∷ [])

holdsᴿ : (c d : Map Level) {p : True (c R.≾? d)} → c R.≾ d
holdsᴿ c d {p} = toWitness p

failsᴿ : (c d : Map Level) {p : False (c R.≾? d)} → ¬ (c R.≾ d)
failsᴿ c d {p} = toWitnessFalse p

-- at most two files and one socket at a time, all released

budget : Map Level
budget = L.𝟏 ∣ ((files , two-at-a-time) ∷ (sockets , res 0 (+ 0) (+ 0) 1) ∷ [])

-- a file and a socket opened together, both closed

file-and-socket : Map Level
file-and-socket =
  only files open-file R.· only sockets open-file R.· only sockets close-file R.· only files close-file

within-budget : file-and-socket R.≾ budget
within-budget = holdsᴿ file-and-socket budget

-- two sockets are not

two-sockets-refused : ¬ (only sockets open-file R.· only sockets open-file
                         R.· only sockets close-file R.· only sockets close-file R.≾ budget)
two-sockets-refused =
  failsᴿ (only sockets open-file R.· only sockets open-file
          R.· only sockets close-file R.· only sockets close-file) budget

-- the files' levels are untouched by the sockets

files-alone : (only sockets open-file R.· only files open-file) ! files ≡ L.𝟏 L.· open-file
files-alone = refl
