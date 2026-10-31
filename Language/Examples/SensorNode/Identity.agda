------------------------------------------------------------------------
-- The language of the sensor node, over an identity grade system.    --
--                                                                    --
-- Effect grades and resource grades are the same monoid `G` and      --
-- `∣-∣ᵉ` is the identity. The instances vary `G` and the grade       --
-- `opTime` assigns to each operation.                                --
------------------------------------------------------------------------

open import Grades.Durations using (Duration)
open import Grades.Base

open import Grades.Examples.System.Identity

open import Grades.Examples.Worked.Operations using (Op)

module Language.Examples.SensorNode.Identity
  {D : Duration} (G : Grade D) (opTime : Op → Grade.Carrier G) where

open import Language.Examples.SensorNode (identityGradeSystem G) opTime public
