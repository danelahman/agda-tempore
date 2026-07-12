------------------------------------------------------------------------
-- Interpretation of variables.                                         --
--                                                                    --
-- A variable `x : A ∈[ ρ ] Γ` is projected through the context to the  --
-- possibility modality at its accumulated grade, `var-proj x :          --
-- ⟦ Γ ⟧ →ᵐ ⟨ ρ ⟩ᵒ ⟦ A ⟧`. It is then extracted to `⟦ A ⟧`: for a        --
-- non-eternal type this needs `ρ ≾ uᵣ` and uses the unit-graded counit   --
-- `εᵘ`; for an eternal type it uses the eternal extraction `extᵉ` at     --
-- the arbitrary grade `ρ`.                                              --
--                                                                    --
-- The eternal extraction of a *composite* eternal type is derived here  --
-- law-free (it is only a morphism, no coherence needed): `Unit` uses    --
-- the terminal map, products the functorial action, and `Empty` the     --
-- adjunction counit on `⟨ ρ ⟩ᶠ initialᵐ`. Only the eternal *base* types  --
-- need supplied structure (`GroundEternal`).                            --
------------------------------------------------------------------------

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Variables
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

open import Syntax.Types S
open import Syntax.Contexts S

open Category Cat
open Future Fut using ([_]ᵒ)
open Past Pst
open Adjunction Adj using (ε⊣)
open GroundEternal GE
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon

-- Project a variable through the context to the possibility modality.

var-proj : ∀ {A ρ Γ} → A ∈[ ρ ] Γ → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟨ ρ ⟩ᵒ ⟦ A ⟧ᵛ
var-proj Hd                    = η ∘ᵐ sndᵐ
var-proj (Tl-∷ x)              = var-proj x ∘ᵐ fstᵐ
var-proj (Tl-⟨⟩ {ρ = ρ} x)     = μ ∘ᵐ ⟨ ρ ⟩ᶠ (var-proj x)

-- Eternal extraction at an arbitrary grade, derived by recursion on the
-- eternality witness (base from `GroundEternal`; formers derived).

eternalᵛ-extᵉ : ∀ {A} → Eternal A → ∀ {ρ} → ⟨ ρ ⟩ᵒ ⟦ A ⟧ᵛ →ᵐ ⟦ A ⟧ᵛ
eternalᵛ-extᵉ (Baseₑ b eb)      = Eternalᵒ.extᵉ (⟦ b ⟧ᵇᵉ eb)
eternalᵛ-extᵉ Unitₑ             = terminalᵐ
eternalᵛ-extᵉ (et₁ |×|ₑ et₂) {ρ} =
  mapˣᵐ (eternalᵛ-extᵉ et₁) (eternalᵛ-extᵉ et₂) ∘ᵐ ⟨ ⟨ ρ ⟩ᶠ fstᵐ , ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ
eternalᵛ-extᵉ Emptyₑ {ρ}        = ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ (initialᵐ {[ ρ ]ᵒ 𝟘ᵐ})

-- The morphism interpreting a variable: project, then extract.

var-morphism : ∀ {Γ A ρ} → (¬ Eternal A → ρ ≾ᵣ uᵣ) → A ∈[ ρ ] Γ
             → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
var-morphism {A = A} f x with eternal? A
... | yes et = eternalᵛ-extᵉ et ∘ᵐ var-proj x
... | no ¬et = εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj x
