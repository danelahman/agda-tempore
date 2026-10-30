------------------------------------------------------------------------
-- Effect handling for the free graded monad.                          --
--                                                                    --
-- A handler is a family of clause *morphisms*, one per operation and   --
-- residual effect grade, closing over an eternal parameter `P`.        --
-- `T-alg-of-handlerˢ` folds a computation tree, reinterpreting every   --
-- operation by the matching clause and keeping delays as delays; `P`   --
-- (an `Eternalᵒ`) is carried under the box at `delay`/`op` nodes.       --
--                                                                    --
-- Split for load time: the (slow) fold and its (co)naturality live in  --
-- `Handling.Core`; the algebra laws in `Handling.Laws` (η/delay/op/≤)  --
-- and `Handling.Mu` (the μ law). This module re-exports all three.     --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core S Wld GTy public
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Laws S Wld GTy public
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Mu   S Wld GTy public
