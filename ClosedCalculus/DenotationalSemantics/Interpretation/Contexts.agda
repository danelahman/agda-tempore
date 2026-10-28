------------------------------------------------------------------------
-- Interpretation of the contexts in a model.                           --
--                                                                    --
-- A context is interpreted as an object: the empty context is the       --
-- terminal object, a variable extension `Γ ∷ A` is a product with the   --
-- value type's interpretation, and a time-passage lock `Γ ⟨ ρ ⟩` is     --
-- the context (possibility) modality `⟨ ρ ⟩ᵒ` applied to the            --
-- interpretation of `Γ`.                                                --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import ClosedCalculus.DenotationalSemantics.Model.Category
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
open import ClosedCalculus.DenotationalSemantics.Model.Monad

module ClosedCalculus.DenotationalSemantics.Interpretation.Contexts
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades

open import ClosedCalculus.Syntax.Contexts S

open Category Cat
open Past Pst
open import ClosedCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon

-- Interpretation of contexts

⟦_⟧ᶜᵗˣ : Ctx → Obj
⟦ []      ⟧ᶜᵗˣ = 𝟙ᵐ
⟦ Γ ∷ A   ⟧ᶜᵗˣ = ⟦ Γ ⟧ᶜᵗˣ ×ᵐ ⟦ A ⟧ᵛ
⟦ Γ ⟨ ρ ⟩ ⟧ᶜᵗˣ = ⟨ ρ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ
