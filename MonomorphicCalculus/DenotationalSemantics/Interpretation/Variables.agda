------------------------------------------------------------------------
-- Interpretation of variables.                                       --
--                                                                    --
-- A variable `x : A ∈[ ρ ] Γ` projects through the context to the    --
-- context modality at its accumulated grade, then extracts to        --
-- `⟦ A ⟧`: a noneternal type needs `ρ ≾ 𝟏ᵣ` and the possibility      --
-- counit `εᵘ`; an eternal type uses the eternal extraction `extᵉ` at --
-- any grade `ρ`.                                                     --
--                                                                    --
-- An eternal type's `Eternalᵒ` structure is assembled by recursion   --
-- on the eternality witness from `GroundEternal`'s per-former        --
-- structure, so the eternal laws are inherited rather than           --
-- re-proved for each former.                                         --
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)

open import Relation.Nullary using (¬_; yes; no)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; ε)
open Past Pst
open Adjunction Adj using (ε⊣; ε⊣-≤; ε⊣-𝟏)
open GroundEternal GE
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon

-- Project a variable through the context to the context modality.

var-proj : ∀ {A ρ Γ} → A ∈[ ρ ] Γ → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟨ ρ ⟩ᵒ ⟦ A ⟧ᵛ
var-proj Hd                    = η ∘ᵐ sndᵐ
var-proj (Tl-∷ x)              = var-proj x ∘ᵐ fstᵐ
var-proj (Tl-⟨⟩ {ρ = ρ} x)     = μ ∘ᵐ ⟨ ρ ⟩ᶠ (var-proj x)

-- The eternal structure of an eternal type's interpretation, assembled by
-- recursion on the eternality witness from the structure supplied for each
-- former by `GroundEternal`. The eternal laws below are then `Eternalᵒ`
-- fields or derived from them, not re-proved for each former.

eternalᵛ-Eternalᵒ : ∀ {A} → Et A → Eternalᵒ ⟦ A ⟧ᵛ
eternalᵛ-Eternalᵒ (Baseₑ {b} eb) = ⟦ b ⟧ᵇᵉ eb
eternalᵛ-Eternalᵒ unitₑ          = 𝟙-eternalᵒ
eternalᵛ-Eternalᵒ boolₑ          = 𝔹-eternalᵒ
eternalᵛ-Eternalᵒ natₑ           = ℕ-eternalᵒ
eternalᵛ-Eternalᵒ emptyₑ         = 𝟘-eternalᵒ
eternalᵛ-Eternalᵒ (et₁ |×|ₑ et₂) =
  ×-eternalᵒ (eternalᵛ-Eternalᵒ et₁) (eternalᵛ-Eternalᵒ et₂)
eternalᵛ-Eternalᵒ (et₁ |+|ₑ et₂) =
  +-eternalᵒ (eternalᵛ-Eternalᵒ et₁) (eternalᵛ-Eternalᵒ et₂)
eternalᵛ-Eternalᵒ (listₑ et)     = List-eternalᵒ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction at an arbitrary grade.

eternalᵛ-extᵉ : ∀ {A} → Et A → ∀ {ρ} → ⟨ ρ ⟩ᵒ ⟦ A ⟧ᵛ →ᵐ ⟦ A ⟧ᵛ
eternalᵛ-extᵉ et = Eternalᵒ.extᵉ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction is uniform in the grade, is the possibility counit
-- `εᵘ` at the unit grade, and is a graded `⟨_⟩`-algebra.

eternalᵛ-extᵉ-≤ : ∀ {A} → (et : Et A) → ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ᵣ ρ₂)
                → eternalᵛ-extᵉ et {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ eternalᵛ-extᵉ et {ρ₁}
eternalᵛ-extᵉ-≤ et = Eternalᵒ.extᵉ-≤ (eternalᵛ-Eternalᵒ et)

eternalᵛ-extᵉ-𝟏 : ∀ {A} → (et : Et A) → eternalᵛ-extᵉ et {𝟏ᵣ} ≈ᵐ εᵘ
eternalᵛ-extᵉ-𝟏 et = Eternalᵒ.extᵉ-𝟏 (eternalᵛ-Eternalᵒ et)

eternalᵛ-extᵉ-μ : ∀ {A} → (et : Et A) → ∀ {ρ₁ ρ₂}
                → eternalᵛ-extᵉ et {ρ₂ ·ᵣ ρ₁} ∘ᵐ μ {⟦ A ⟧ᵛ} {ρ₁} {ρ₂}
                ≈ᵐ eternalᵛ-extᵉ et {ρ₁} ∘ᵐ ⟨ ρ₁ ⟩ᶠ (eternalᵛ-extᵉ et {ρ₂})
eternalᵛ-extᵉ-μ et = Eternalᵒ.extᵉ-μ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction does not depend on how eternality was established
-- (`Et` is a property: `MonomorphicCalculus.Syntax.Types.eternal-irrelevant`).

eternalᵛ-extᵉ-irr : ∀ {A} → (et et' : Et A) → ∀ {ρ}
                  → eternalᵛ-extᵉ et {ρ} ≈ᵐ eternalᵛ-extᵉ et' {ρ}
eternalᵛ-extᵉ-irr et et' with eternal-irrelevant et et'
... | refl = ≈ᵐ-refl

-- The morphism interpreting a variable: project, then extract.

var-morphism : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → .(A Et∨≾ᵘ ρ)
             → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
var-morphism {A = A} x f with eternal? A
... | yes et = eternalᵛ-extᵉ et ∘ᵐ var-proj x
... | no ¬et = εᵘ ∘ᵐ ⟨⟩-≤ (Et∨≾ᵘ→¬Et⇒≾ f ¬et) ∘ᵐ var-proj x

-- Unfold `var-morphism` at an eternal type (handles the internal `eternal?`).

var-morphism-unfoldᵉ : ∀ {Γ A ρ} → (et : Et A) → .(f : A Et∨≾ᵘ ρ)
                     → (y : A ∈[ ρ ] Γ)
                     → var-morphism y f ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ var-proj y
var-morphism-unfoldᵉ {A = A} et f y with eternal? A
... | yes et' = ∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et)
... | no ¬et = ⊥-elim (¬et et)

-- Two facts about `var-morphism` at the top of a context, used wherever a
-- renaming's denotation has to be computed.

private
  infixr 3 _∙ᵛ_
  _∙ᵛ_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙ᵛ_ = ≈ᵐ-trans

-- The head variable denotes the second projection: at a noneternal type the
-- grade bound is reflexive and the possibility counit cancels `η`; at an
-- eternal one the extraction cancels it.
var-morphism-Hd : ∀ {Γ A} → .(f : A Et∨≾ᵘ 𝟏ᵣ)
                → var-morphism {Γ ∷ A} Hd f ≈ᵐ sndᵐ
var-morphism-Hd {A = A} f with eternal? A
... | yes et =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵛ ∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-𝟏 et) ∙ᵛ ⟨⟩-εᵘ∘η≡id)
  ∙ᵛ ∘ᵐ-identityˡ _
... | no ¬et =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr (Et∨≾ᵘ→¬Et⇒≾ f ¬et) ≾ᵣ-refl ∙ᵛ ⟨⟩-≤-refl) ∙ᵛ ∘ᵐ-identityˡ _)
  ∙ᵛ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵛ ∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id
  ∙ᵛ ∘ᵐ-identityˡ _

-- Weakening a variable past a `∷` projects the environment.
var-morphism-Tl-∷ : ∀ {Γ A B ρ'} → (y : B ∈[ ρ' ] Γ) → .(f : B Et∨≾ᵘ ρ')
                  → var-morphism {Γ ∷ A} (Tl-∷ y) f ≈ᵐ var-morphism y f ∘ᵐ fstᵐ
var-morphism-Tl-∷ {B = B} y f with eternal? B
... | yes et = ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
... | no ¬et = ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
