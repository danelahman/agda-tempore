------------------------------------------------------------------------
-- Eternal structure for the eternal base types.                        --
--                                                                    --
-- The variable rule may use a variable of an *eternal* type at any     --
-- grade, so the interpretation of an eternal type must carry an         --
-- `Eternalᵒ` structure (in particular the extraction `extᵉ`).           --
--                                                                    --
-- The structure is supplied for each *former* of `Syntax.Types.Eternal`: --
-- the eternal base types, and closure under `Unit`, `Bool`, `Empty`, and --
-- products. `Interpretation.Variables` then assembles an `Eternalᵒ` for  --
-- every eternal type by recursion on the eternality witness, so all the  --
-- eternal *laws* (grade-uniformity, the unit grade, the `⟨_⟩`-algebra    --
-- law) come from `Eternalᵒ` rather than being re-derived per former.     --
--                                                                    --
-- In the presheaf model (`Example.PSh.Modality.Eternal`) the constant    --
-- presheaves `Kᵖ` carry this structure (`Kᵖ-eternalᵒ`), and the formers  --
-- are covered by `𝟙ᵖ-eternalᵒ`, `𝔹ᵖ-eternalᵒ`, `𝟘ᵖ-eternalᵒ`, and        --
-- `×ᵖ-eternalᵒ`.                                                         --
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
open Past Pst using (⟨_⟩ᶠ)
open GroundTypes GTy
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
  using (Eternalᵒ)

record GroundEternal : Set₁ where
  field
    -- the eternal structure of each eternal base type's interpretation
    ⟦_⟧ᵇᵉ : (b : BaseType) → .(EternalBaseType b) → Eternalᵒ ⟦ b ⟧ᵇ

    -- closure of the eternal structure under the eternal type formers
    𝟙-eternalᵒ : Eternalᵒ 𝟙ᵐ
    𝟘-eternalᵒ : Eternalᵒ 𝟘ᵐ
    𝔹-eternalᵒ : Eternalᵒ 𝔹ᵐ
    ×-eternalᵒ : ∀ {A B} → Eternalᵒ A → Eternalᵒ B → Eternalᵒ (A ×ᵐ B)

    -- The product's eternal extraction acts componentwise (the closure is
    -- compatible with the projections).
    ×-eternalᵒ-extᵉ : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ}
                    → Eternalᵒ.extᵉ (×-eternalᵒ eA eB) {ρ}
                    ≈ᵐ ⟨ Eternalᵒ.extᵉ eA ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
                       , Eternalᵒ.extᵉ eB ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ

    -- A constant of an eternal base type denotes a *global* element: it is
    -- the same at every world, so the eternal extraction recovers it. This
    -- is what lets a constant be weakened under a lock (`eternal-val-ext`).
    ⟦⟧ᵇᶜ-eternal : ∀ {b} → .(eb : EternalBaseType b) → (c : BaseConstants b) → ∀ {ρ}
                 → Eternalᵒ.extᵉ (⟦ b ⟧ᵇᵉ eb) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (⟦_⟧ᵇᶜ {b} c)
                 ≈ᵐ ⟦_⟧ᵇᶜ {b} c ∘ᵐ terminalᵐ

    -- The two booleans are global elements in the same sense.
    trueᵐ-eternal : ∀ {ρ}
                  → Eternalᵒ.extᵉ 𝔹-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ trueᵐ
                  ≈ᵐ trueᵐ ∘ᵐ terminalᵐ
    falseᵐ-eternal : ∀ {ρ}
                   → Eternalᵒ.extᵉ 𝔹-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ falseᵐ
                   ≈ᵐ falseᵐ ∘ᵐ terminalᵐ
