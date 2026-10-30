------------------------------------------------------------------------
-- Eternal structure for the eternal base types.                        --
--                                                                    --
-- The variable rule may use a variable of an *eternal* type at any     --
-- grade, so the interpretation of an eternal type must carry an         --
-- `Eternalᵒ` structure (in particular the extraction `extᵉ`).           --
--                                                                    --
-- The structure is supplied for each *former* of                         --
-- `MonomorphicCalculus.Syntax.Types.Eternal`:                        --
-- the eternal base types, and closure under `Unit`, `Bool`, `Nat`,      --
-- `Empty`, products, sums and lists. `Interpretation.Variables` then     --
-- assembles an `Eternalᵒ` for every eternal type by recursion on the     --
-- eternality witness, so all the eternal *laws* (grade-uniformity, the   --
-- unit grade, the `⟨_⟩`-algebra law) come from `Eternalᵒ` rather than    --
-- being re-derived per former.                                           --
--                                                                    --
-- An eternal base type also carries its order, a comparison morphism    --
-- (`cmpᵇᵐ`) agreeing with the signature's order on the constants;       --
-- `Interpretation.Comparisons` extends it to every eternal type.         --
--                                                                    --
-- In the presheaf model (`Example.PSh.Modality.Eternal`) the constant    --
-- presheaves `Kᵖ` carry this structure (`Kᵖ-eternalᵒ`), and the formers  --
-- are covered by `𝟙ᵖ-eternalᵒ`, `𝔹ᵖ-eternalᵒ`, `ℕᵖ-eternalᵒ`,          --
-- `𝟘ᵖ-eternalᵒ`, `×ᵖ-eternalᵒ`, `+ᵖ-eternalᵒ` and `Listᵖ-eternalᵒ`.    --
------------------------------------------------------------------------

open import Language.BaseTypes
open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
import MonomorphicCalculus.DenotationalSemantics.Model.Comparison as Comparison
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes

module MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
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
open Comparison Cat using (Ordᵐ; Compares)
open Past Pst using (⟨_⟩ᶠ)
open GroundTypes GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
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
    ℕ-eternalᵒ : Eternalᵒ ℕᵐ
    ×-eternalᵒ : ∀ {A B} → Eternalᵒ A → Eternalᵒ B → Eternalᵒ (A ×ᵐ B)

    -- The product's eternal extraction acts componentwise (the closure is
    -- compatible with the projections).
    ×-eternalᵒ-extᵉ : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ}
                    → Eternalᵒ.extᵉ (×-eternalᵒ eA eB) {ρ}
                    ≈ᵐ ⟨ Eternalᵒ.extᵉ eA ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
                       , Eternalᵒ.extᵉ eB ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ

    +-eternalᵒ : ∀ {A B} → Eternalᵒ A → Eternalᵒ B → Eternalᵒ (A +ᵐ B)

    -- The coproduct's eternal extraction acts summandwise (the closure is
    -- compatible with the injections).
    +-eternalᵒ-inl : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ}
                   → Eternalᵒ.extᵉ (+-eternalᵒ eA eB) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ inlᵐ
                   ≈ᵐ inlᵐ ∘ᵐ Eternalᵒ.extᵉ eA {ρ}
    +-eternalᵒ-inr : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ}
                   → Eternalᵒ.extᵉ (+-eternalᵒ eA eB) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ inrᵐ
                   ≈ᵐ inrᵐ ∘ᵐ Eternalᵒ.extᵉ eB {ρ}

    List-eternalᵒ : ∀ {A} → Eternalᵒ A → Eternalᵒ (Listᵐ A)

    -- The list's eternal extraction acts elementwise (the closure is
    -- compatible with the constructors).
    List-eternalᵒ-nil : ∀ {A} → (eA : Eternalᵒ A) → ∀ {ρ}
                      → Eternalᵒ.extᵉ (List-eternalᵒ eA) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ nilᵐ
                      ≈ᵐ nilᵐ ∘ᵐ terminalᵐ
    List-eternalᵒ-cons : ∀ {A} → (eA : Eternalᵒ A) → ∀ {ρ}
                       → Eternalᵒ.extᵉ (List-eternalᵒ eA) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ consᵐ
                       ≈ᵐ consᵐ ∘ᵐ ⟨ Eternalᵒ.extᵉ eA {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
                                  , Eternalᵒ.extᵉ (List-eternalᵒ eA) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ

    -- A constant of an eternal base type denotes a *global* element: it is
    -- the same at every world, so the eternal extraction recovers it. This
    -- is what lets a constant be weakened under a lock (`eternal-val-ext`).
    ⟦⟧ᵇᶜ-eternal : ∀ {b} → .(eb : EternalBaseType b) → (c : BaseConstants b) → ∀ {ρ}
                 → Eternalᵒ.extᵉ (⟦ b ⟧ᵇᵉ eb) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (⟦_⟧ᵇᶜ {b} c)
                 ≈ᵐ ⟦_⟧ᵇᶜ {b} c ∘ᵐ terminalᵐ

    -- An eternal base type's order: a comparison, which compares two
    -- constants as the signature orders them.
    cmpᵇᵐ    : (b : BaseType) → .(EternalBaseType b) → ⟦ b ⟧ᵇ ×ᵐ ⟦ b ⟧ᵇ →ᵐ Ordᵐ
    cmpᵇᵐ-pt : ∀ {b} → .(eb : EternalBaseType b)
             → Compares (cmpᵇᵐ b eb) (⟦_⟧ᵇᶜ {b}) (compareᵇ eb)

    -- The two booleans are global elements in the same sense.
    trueᵐ-eternal : ∀ {ρ}
                  → Eternalᵒ.extᵉ 𝔹-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ trueᵐ
                  ≈ᵐ trueᵐ ∘ᵐ terminalᵐ
    falseᵐ-eternal : ∀ {ρ}
                   → Eternalᵒ.extᵉ 𝔹-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ falseᵐ
                   ≈ᵐ falseᵐ ∘ᵐ terminalᵐ

    -- Zero is a global element in the same sense, and the eternal
    -- extraction commutes with the successor.
    zeroᵐ-eternal : ∀ {ρ}
                  → Eternalᵒ.extᵉ ℕ-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ zeroᵐ
                  ≈ᵐ zeroᵐ ∘ᵐ terminalᵐ
    succᵐ-eternal : ∀ {ρ}
                  → Eternalᵒ.extᵉ ℕ-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ succᵐ
                  ≈ᵐ succᵐ ∘ᵐ Eternalᵒ.extᵉ ℕ-eternalᵒ {ρ}
