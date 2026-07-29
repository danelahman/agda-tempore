------------------------------------------------------------------------
-- The interpretation is natural in substitutions:                      --
--   ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ≈ ⟦ M ⟧ᶜᵗ ∘ᵐ sub-env x W   (dually for values). --
--                                                                    --
-- `sub-env x W : ⟦ split-l x ++ᶜ split-r x ⟧ →ᵐ ⟦ Γ ⟧` is the semantic  --
-- counterpart of the substitution: it reconstructs the environment for   --
-- `Γ` by inserting `⟦ W ⟧` at the position of `x`. It is defined by       --
-- structural recursion on `x` (the context splitting computes on `x`,     --
-- and the context interpretation distributes over `++ᶜ`), so no           --
-- transports along context equalities are needed.                         --
------------------------------------------------------------------------
-- The four parts below are the substitution's environment morphism, the
-- `unbox` and variable cases, the transports, and the theorem itself.
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad
module DenotationalSemantics.Interpretation.SubstitutionCoherence
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE public
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Unbox S Cat Fut Pst Adj GTy Mon GE public
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport S Cat Fut Pst Adj GTy Mon GE public
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Core S Cat Fut Pst Adj GTy Mon GE public
