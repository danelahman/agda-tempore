------------------------------------------------------------------------
-- Interpretation of ground types as objects of the model.             --
--                                                                    --
-- A `GroundTypes` structure supplies an interpretation `⟦_⟧ᵇ` of the  --
-- base types as objects; the interpretation `⟦_⟧ᵍ` of ground types is  --
-- then determined by the cartesian closed structure (unit, empty,      --
-- products) and the box modality (for the temporal ground modality     --
-- `[ ρ ]ᵍ`).                                                           --
------------------------------------------------------------------------

open import Syntax.BaseTypes
open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future

module DenotationalSemantics.Model.GroundTypes (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open BaseTypes BTs

open import Syntax.GroundTypes Grades BTs

record GroundTypes (Cat : Category) (Fut : Future Cat RGrade) : Set₁ where

  open Category Cat
  open Future Fut

  field
    -- interpretation of the base types
    ⟦_⟧ᵇ : BaseType → Obj

  -- interpretation of the ground types

  ⟦_⟧ᵍ : GType → Obj
  ⟦ Base b     ⟧ᵍ = ⟦ b ⟧ᵇ
  ⟦ Unit       ⟧ᵍ = 𝟙ᵐ
  ⟦ Empty      ⟧ᵍ = 𝟘ᵐ
  ⟦ G₁ |×|ᵍ G₂ ⟧ᵍ = ⟦ G₁ ⟧ᵍ ×ᵐ ⟦ G₂ ⟧ᵍ
  ⟦ [ ρ ]ᵍ G   ⟧ᵍ = [ ρ ]ᵒ ⟦ G ⟧ᵍ
