------------------------------------------------------------------------
-- Programs of several top-level definitions: each definition inferred
-- in the program context of those before it, a definition used at two
-- instances of its scheme, and a use whose instance fails the scheme's
-- hypotheses. Exercises the generation of a use of a definition, the
-- inference of value schemes and the checking of programs (`Generate`,
-- `Values`, `Checking`).
------------------------------------------------------------------------

module PolymorphicCalculus.Examples.Programs.All where

import PolymorphicCalculus.Examples.Programs

import PolymorphicCalculus.Examples.Programs.Time.RightSided
import PolymorphicCalculus.Examples.Programs.Time.LeftSided
