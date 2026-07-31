------------------------------------------------------------------------
-- The interpretation is natural in substitutions:                      --
--   ⟦ C-sub₀ s M ⟧ᶜᵗ ≈ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ s ⟧ˢ₀        (dually for values). --
--                                                                    --
-- `⟦ s ⟧ˢ₀ : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ` is the semantic counterpart of a    --
-- `Sub₀ [] Γ Γ'`: each generator is a structural map of the model, so it  --
-- is defined by recursion on the substitution alone, and no transports     --
-- along context equalities are needed.                                     --
--                                                                          --
-- Replacing one variable is the instance at `sub-at₀ x W`, whose            --
-- environment morphism is `sub-env x W`.                                    --
------------------------------------------------------------------------
-- The four parts below are the eternal-value lemmas, the substitution's
-- environment morphism and the theorem, the transports, and the
-- one-variable instance.
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
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Env S Cat Fut Pst Adj GTy Mon GE public
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport S Cat Fut Pst Adj GTy Mon GE public
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Core S Cat Fut Pst Adj GTy Mon GE public
