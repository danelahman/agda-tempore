------------------------------------------------------------------------
-- Interpretation of context renamings.                                --
--                                                                    --
-- A renaming `Ren Γ Γ'` rewrites a `Γ'`-typed term into a `Γ`-typed    --
-- term (`V-rename`/`C-rename`), so on environments it runs             --
-- covariantly, as a reindexing `⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ`. Each           --
-- constructor is a structural map of the model: weakening projects      --
-- (`fstᵐ`), a variable renaming contracts (`⟨ idᵐ , var-morphism … ⟩ᵐ`), --
-- and the lock renamings are exactly the context modality's             --
-- unit `η`, counit `εᵘ`, multiplication `μ`, and monotonicity `⟨⟩-≤` —   --
-- all available at an *arbitrary* resource grade.                       --
-- The three parts below are the algebra structure of eternal contexts,
-- the extension of an environment morphism through a suffix, and the
-- denotation of each structural renaming.
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import ClosedCalculus.DenotationalSemantics.Model.Category
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
open import ClosedCalculus.DenotationalSemantics.Model.GroundEternal
open import ClosedCalculus.DenotationalSemantics.Model.Monad
module ClosedCalculus.DenotationalSemantics.Interpretation.Renaming
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Algebra S Cat Fut Pst Adj GTy Mon GE public
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Extension S Cat Fut Pst Adj GTy Mon GE public
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Structural S Cat Fut Pst Adj GTy Mon GE public
