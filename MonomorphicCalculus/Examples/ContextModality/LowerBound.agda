------------------------------------------------------------------------
-- The context modality at lower bounds on time                       --
--                                                                    --
-- What it shows                                                      --
--   The unit `𝟏` of the grades is the greatest grade, so the context --
--   modality is a parametric right adjoint at every grade            --
--   (`PRA-left`), with the familial representation of                --
--   `Renaming/ContextModality/LowerBounds`. It has a left adjoint    --
--   only at `𝟏` (`no-left-adjoint-[1,∞⟩`).                           --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Product using (proj₂)
open import Relation.Nullary using (¬_)

open import Grades.Base
open import Grades.Examples.Time.LowerBound
open import Grades.Examples.System.Identity using (identity-grade-system)
open import Language.BaseTypes using (noBaseTypes)
open import Language.Spec
import Language.Operations as Ops

module MonomorphicCalculus.Examples.ContextModality.LowerBound where

G : GradeSystem
G = identity-grade-system lower-bound

ops : Ops.Operations G noBaseTypes
ops = record
  { Op = ⊥ ; _≟ₒ_ = λ () ; param = λ () ; arity = λ () ; op-grade = λ () }

spec : LanguageSpec
spec = withoutBaseTypes G ops

open GradeSystemInterface G

open import MonomorphicCalculus.Syntax.Renaming.ContextModality             spec
open import MonomorphicCalculus.Syntax.Renaming.ContextModality.LowerBounds spec

PRA-left : (ρ : R) → PRA ρ
PRA-left = PRA-everywhere ≾ᵣ-refl

no-left-adjoint-[1,∞⟩ : ¬ LeftAdjoint [ 1 ,+∞⟩
no-left-adjoint-[1,∞⟩ la with proj₂ (left-adjoint⇒ρ≃𝟏 la)
... | ()
