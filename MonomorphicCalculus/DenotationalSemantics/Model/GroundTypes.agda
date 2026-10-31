-------------------------------------------------------------------------
-- Interpretation of ground types as objects of the model.             --
--                                                                     --
-- A `GroundTypes` structure supplies an interpretation `⟦_⟧ᵇ` of the  --
-- base types as objects; the interpretation `⟦_⟧ᵍ` of ground types is --
-- then determined by the structure of the model (unit, booleans,      --
-- naturals, empty, products, coproducts, lists) and the box `[ ρ ]ᵒ`  --
-- (for the ground box modality `[ ρ ]ᵍ`).                             --
-------------------------------------------------------------------------

open import Language.BaseTypes
open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future

module MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open BaseTypes BTs

open import Language.GroundTypes Grades BTs

record GroundTypes (Cat : Category) (Fut : Future Cat RGrade) : Set₁ where

  open Category Cat
  open Future Fut

  field
    -- interpretation of the base types
    ⟦_⟧ᵇ : BaseType → Obj

    -- interpretation of base-typed constants as global elements
    ⟦_⟧ᵇᶜ : ∀ {B} → BaseConstants B → 𝟙ᵐ →ᵐ ⟦ B ⟧ᵇ

  -- interpretation of the ground types

  ⟦_⟧ᵍ : GType → Obj
  ⟦ Base b     ⟧ᵍ = ⟦ b ⟧ᵇ
  ⟦ Unit       ⟧ᵍ = 𝟙ᵐ
  ⟦ Bool       ⟧ᵍ = 𝔹ᵐ
  ⟦ Nat        ⟧ᵍ = ℕᵐ
  ⟦ Empty      ⟧ᵍ = 𝟘ᵐ
  ⟦ G₁ |×|ᵍ G₂ ⟧ᵍ = ⟦ G₁ ⟧ᵍ ×ᵐ ⟦ G₂ ⟧ᵍ
  ⟦ G₁ |+|ᵍ G₂ ⟧ᵍ = ⟦ G₁ ⟧ᵍ +ᵐ ⟦ G₂ ⟧ᵍ
  ⟦ |List|ᵍ G  ⟧ᵍ = Listᵐ ⟦ G ⟧ᵍ
  ⟦ [ ρ ]ᵍ G   ⟧ᵍ = [ ρ ]ᵒ ⟦ G ⟧ᵍ
