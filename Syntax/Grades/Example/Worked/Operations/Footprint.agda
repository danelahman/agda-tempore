------------------------------------------------------------------------
-- What the sensor node's operations do besides take time.             --
--                                                                     --
-- Two figures per operation, for the grades that pair time with       --
-- something else:                                                     --
--                                                                     --
--            touches   draws                                          --
--   read     Low       1       a local sensor                         --
--   write    Low       2       local memory                           --
--   send     High      5       the radio                              --
--                                                                     --
-- `touches` is the security level an operation touches. The radio is  --
-- the node's one contact with the outside network, so a transmission  --
-- touches `High` and taints the rest of the run; nothing local does.  --
-- `draws` is the energy an operation draws from the battery, the      --
-- radio dominating.                                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Operations.Footprint where

open import Data.Nat.Base using (ℕ)

open import Syntax.Grades.Example.SecurityLevel using (LowHigh; Low; High)

open import Syntax.Grades.Example.Worked.Operations using (Op; read; write; send)

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
