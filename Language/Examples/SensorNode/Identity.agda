------------------------------------------------------------------------
-- The language of the sensor node, over an identity grade system.    --
--                                                                    --
-- Effect grades and resource grades are the same monoid `G` and      --
-- `∣_∣ᵉ` is the identity. The instances vary `G`, the grade `opTime` --
-- assigns to each operation, and the candidate values `wit` of a     --
-- rigid.                                                             --
------------------------------------------------------------------------

open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)

open import Grades.Durations using (Duration)
open import Grades.Base

open import Grades.Examples.System.Identity

open import Grades.Examples.Worked.Operations using (Op)

module Language.Examples.SensorNode.Identity
  {D : Duration} (G : Grade D) (opTime : Op → Grade.Carrier G)
  (wit : ℕ → List (Grade.Carrier G) → List (Grade.Carrier G)) where

open import Language.Examples.SensorNode (identityGradeSystem G wit) opTime public
