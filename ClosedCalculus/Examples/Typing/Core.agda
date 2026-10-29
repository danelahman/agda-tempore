------------------------------------------------------------------------
-- The language of the typing examples, over an identity grade        --
-- system.                                                            --
--                                                                    --
-- Effect grades and resource grades are the same monoid `G` and      --
-- `∣_∣ᵉ` is the identity, so `mapᵉ` reduces away. The instances vary --
-- `G` and the grade `opTime` assigns to each operation. The calculus --
-- over the language is `Typing.System`; the example programs are in  --
-- the instances.                                                     --
------------------------------------------------------------------------

open import Grades.Durations using (Duration)
open import Grades.Base

open import Grades.Examples.System.Identity

open import Grades.Examples.Worked.Operations using (Op)

module ClosedCalculus.Examples.Typing.Core
  {D : Duration} (G : Grade D) (opTime : Op → Grade.Carrier G) where

open import ClosedCalculus.Examples.Typing.System (identityGradeSystem G) opTime public
