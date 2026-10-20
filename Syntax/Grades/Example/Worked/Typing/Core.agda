------------------------------------------------------------------------
-- The language of the typing examples, over an identity grade        --
-- system.                                                            --
--                                                                    --
-- Effect grades and resource grades are the same monoid `G` and      --
-- `∣_∣ᵉ` is the identity, so `mapᵉ` reduces away. The instances vary --
-- `G`, the grade `opTime` assigns to each operation, and the         --
-- candidate values `wit` of a rigid. The language itself is          --
-- `Typing.System`; the example programs are in the instances.        --
------------------------------------------------------------------------

open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)

open import Syntax.Durations using (Duration)
open import Syntax.Grades

open import Syntax.Grades.Example.System.Identity

open import Syntax.Grades.Example.Worked.Operations using (Op)

module Syntax.Grades.Example.Worked.Typing.Core
  {D : Duration} (G : Grade D) (opTime : Op → Grade.Carrier G)
  (wit : ℕ → List (Grade.Carrier G) → List (Grade.Carrier G)) where

open import Syntax.Grades.Example.Worked.Typing.System (identityGradeSystem G wit) opTime public
