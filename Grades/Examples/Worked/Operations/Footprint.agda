------------------------------------------------------------------------
-- What the operations of the sensor node do besides taking time.     --
--                                                                    --
-- Two figures per operation, for the grades that pair time with      --
-- another component:                                                 --
--                                                                    --
--            touches   draws                                         --
--   read     Low       1       a local sensor                        --
--   write    Low       2       local memory                          --
--   send     High      5       the radio                             --
--                                                                    --
-- `touches` is the level of the lattice an operation touches: the    --
-- radio is the one contact of the node with the outside network, so  --
-- a transmission touches `High` and taints the rest of the run, and  --
-- no local operation does. `draws` is the energy an operation draws  --
-- from the battery.                                                  --
------------------------------------------------------------------------

module Grades.Examples.Worked.Operations.Footprint where

open import Data.Nat.Base using (ℕ)

open import Grades.Examples.Lattice using (LowHigh; Low; High)

open import Grades.Examples.Worked.Operations using (Op; read; write; send)

-- the level an operation touches

touches : Op → LowHigh
touches read  = Low
touches write = Low
touches send  = High

-- the energy an operation draws

draws : Op → ℕ
draws read  = 1
draws write = 2
draws send  = 5
