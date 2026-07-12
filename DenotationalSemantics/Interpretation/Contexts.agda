------------------------------------------------------------------------
-- Interpretation of the contexts in a model.                           --
--                                                                    --
-- A context is interpreted as an object: the empty context is the       --
-- terminal object, a variable extension `Γ ∷ A` is a product with the   --
-- value type's interpretation, and a time-passage lock `Γ ⟨ ρ ⟩` is     --
-- the context (possibility) modality `⟨ ρ ⟩ᵒ` applied to the            --
-- interpretation of `Γ`.                                                --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Contexts
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts S

open Category Cat
open Past Pst
open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon

-- Interpretation of contexts

⟦_⟧ᶜᵗˣ : Ctx → Obj
⟦ []      ⟧ᶜᵗˣ = 𝟙ᵐ
⟦ Γ ∷ A   ⟧ᶜᵗˣ = ⟦ Γ ⟧ᶜᵗˣ ×ᵐ ⟦ A ⟧ᵛ
⟦ Γ ⟨ ρ ⟩ ⟧ᶜᵗˣ = ⟨ ρ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ
