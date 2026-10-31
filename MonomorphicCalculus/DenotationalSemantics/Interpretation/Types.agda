--------------------------------------------------------------------------
-- Interpretation of the value and computation types in a model.        --
--                                                                      --
-- Value types are interpreted as objects: base types via the           --
-- `GroundTypes` interpretation, the finite-product/-coproduct and      --
-- function-type formers via the cartesian closed structure, and the    --
-- box modality `[ ρ ] A` via `[ ρ ]ᵒ`, a handler type via `Hᵒ`. A      --
-- computation type                                                     --
-- `A ‼ ε` is the graded monad applied to the value type, `Tᵒ ⟦ A ⟧ ε`. --
--                                                                      --
-- The two interpretations are mutually recursive: a function type      --
-- `A ⇒ C` has a computation type as its codomain.                      --
--------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.DenotationalSemantics.Interpretation.Types
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

open import MonomorphicCalculus.Syntax.Types S

open Category Cat
open Future Fut
open GroundTypes GTy
open Monad Mon

-- Interpretation of value and computation types

mutual

  ⟦_⟧ᵛ : VType → Obj
  ⟦ Base b   ⟧ᵛ = ⟦ b ⟧ᵇ
  ⟦ Unit     ⟧ᵛ = 𝟙ᵐ
  ⟦ Bool     ⟧ᵛ = 𝔹ᵐ
  ⟦ Nat      ⟧ᵛ = ℕᵐ
  ⟦ A |×| B  ⟧ᵛ = ⟦ A ⟧ᵛ ×ᵐ ⟦ B ⟧ᵛ
  ⟦ A |+| B  ⟧ᵛ = ⟦ A ⟧ᵛ +ᵐ ⟦ B ⟧ᵛ
  ⟦ |List| A ⟧ᵛ = Listᵐ ⟦ A ⟧ᵛ
  ⟦ Empty    ⟧ᵛ = 𝟘ᵐ
  ⟦ A ⇒ C    ⟧ᵛ = ⟦ A ⟧ᵛ ⇒ᵐ ⟦ C ⟧ᶜ
  ⟦ (A ‼ ε) ⇛ (B ‼ ε') ⟧ᵛ = Hᵒ ⟦ A ⟧ᵛ ε ⟦ B ⟧ᵛ ε'
  ⟦ [ ρ ] A  ⟧ᵛ = [ ρ ]ᵒ ⟦ A ⟧ᵛ

  ⟦_⟧ᶜ : CType → Obj
  ⟦ A ‼ ε ⟧ᶜ = Tᵒ ⟦ A ⟧ᵛ ε
