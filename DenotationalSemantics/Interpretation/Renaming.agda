------------------------------------------------------------------------
-- Interpretation of context renamings.                                --
--                                                                    --
-- A renaming `Ren Γ Γ'` rewrites a `Γ`-typed term into a `Γ'`-typed    --
-- term (`V-rename`/`C-rename`), so on environments it runs             --
-- contravariantly, as a reindexing `⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ`. Each       --
-- constructor is a structural map of the model: weakening projects      --
-- (`fstᵐ`), a variable renaming contracts (`⟨ idᵐ , var-morphism … ⟩ᵐ`), --
-- and the lock (possibility) renamings are exactly the past modality's  --
-- unit `η`, counit `εᵘ`, multiplication `μ`, and monotonicity `⟨⟩-≤` —   --
-- all available at an *arbitrary* resource grade.                       --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Renaming
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Renamings S

open Category Cat
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤; η; μ; εᵘ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE

-- The reindexing morphism of a renaming (contravariant in the context).

⟦_⟧ʳ : ∀ {Γ Γ'} → Ren Γ Γ' → ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
⟦ id-ren ⟧ʳ              = idᵐ
⟦ r₂ ∘ʳ r₁ ⟧ʳ            = ⟦ r₁ ⟧ʳ ∘ᵐ ⟦ r₂ ⟧ʳ
⟦ wk-ren ⟧ʳ              = fstᵐ
⟦ var-ren p x ⟧ʳ         = ⟨ idᵐ , var-morphism (λ _ → p) x ⟩ᵐ
⟦ ⟨⟩-η-ren ⟧ʳ            = η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ          = εᵘ
⟦ ⟨⟩-μ-ren {Γ} {ρ} {ρ'} ⟧ʳ = μ {⟦ Γ ⟧ᶜᵗˣ} {ρ'} {ρ}
⟦ ⟨⟩-≤-ren rel ⟧ʳ        = ⟨⟩-≤ rel
⟦ cong-∷-ren r ⟧ʳ        = mapˣᵐ ⟦ r ⟧ʳ idᵐ
⟦ cong-⟨⟩-ren {ρ = ρ} r ⟧ʳ = ⟨ ρ ⟩ᶠ ⟦ r ⟧ʳ
