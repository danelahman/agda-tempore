------------------------------------------------------------------------
-- Eternal structure for the eternal base types.                        --
--                                                                    --
-- The variable rule may use a variable of an *eternal* type at any     --
-- grade, so the interpretation of an eternal type must carry an         --
-- `Eternalᵒ` structure (in particular the extraction `extᵉ`). For the   --
-- type formers this is derived (see `Interpretation.Variables`); the    --
-- only genuinely new datum is the eternal structure of the eternal      --
-- *base* types, supplied here. Concretely (`Example.PSh`) an eternal    --
-- base type is a constant presheaf, whose `Eternalᵒ` is `Kᵖ-eternalᵒ`.  --
------------------------------------------------------------------------

open import Syntax.BaseTypes
open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes

module DenotationalSemantics.Model.GroundEternal
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open BaseTypes BTs

open Category Cat
open GroundTypes GTy
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
  using (Eternalᵒ)

record GroundEternal : Set₁ where
  field
    -- the eternal structure of each eternal base type's interpretation
    ⟦_⟧ᵇᵉ : (b : BaseType) → EternalBaseType b → Eternalᵒ ⟦ b ⟧ᵇ
