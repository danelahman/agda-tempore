------------------------------------------------------------------------
-- Interpretation of the value and computation types in a model.        --
--                                                                    --
-- Value types are interpreted as objects: base types via the           --
-- `GroundTypes` interpretation, the finite-product/-coproduct and       --
-- function-type formers via the cartesian closed structure, and the     --
-- box modality `[ ρ ] A` via `[ ρ ]ᵒ`. A computation type               --
-- `A ‼ ε` is the graded monad applied to the value type, `Tᵒ ⟦ A ⟧ ε`.  --
--                                                                    --
-- The two interpretations are mutually recursive: a function type       --
-- `A ⇒ C` has a computation type as its codomain.                       --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Types
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

open import Syntax.Types S

open Category Cat
open Future Fut
open GroundTypes GTy
open Monad Mon

-- Interpretation of value and computation types

mutual

  ⟦_⟧ᵛ : VType → Obj
  ⟦ Base b   ⟧ᵛ = ⟦ b ⟧ᵇ
  ⟦ Unit     ⟧ᵛ = 𝟙ᵐ
  ⟦ A |×| B  ⟧ᵛ = ⟦ A ⟧ᵛ ×ᵐ ⟦ B ⟧ᵛ
  ⟦ Empty    ⟧ᵛ = 𝟘ᵐ
  ⟦ A ⇒ C    ⟧ᵛ = ⟦ A ⟧ᵛ ⇒ᵐ ⟦ C ⟧ᶜ
  ⟦ [ ρ ] A  ⟧ᵛ = [ ρ ]ᵒ ⟦ A ⟧ᵛ

  ⟦_⟧ᶜ : CType → Obj
  ⟦ A ‼ ε ⟧ᶜ = Tᵒ ⟦ A ⟧ᵛ ε
