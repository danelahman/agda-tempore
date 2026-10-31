------------------------------------------------------------------------
-- Interpretation of variables.                                       --
--                                                                    --
-- A variable `x : A ∈[ ρ ] Γ` projects through the context to the    --
-- context modality at its accumulated grade, then extracts to        --
-- `⟦ A ⟧`: a non-eternal type needs `ρ ≾ uᵣ` and the possibility     --
-- counit `εᵘ`; an eternal type uses the eternal extraction `extᵉ`    --
-- at any grade `ρ`.                                                  --
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
open Adjunction Adj using (ε⊣; ε⊣-≤; ε⊣-u)
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
-- former by `GroundEternal`. Because this lands in `Eternalᵒ`, all the
-- eternal laws below are `Eternalᵒ` fields (or derived there), rather than
-- being re-proved by induction for each former.

eternalᵛ-Eternalᵒ : ∀ {A} → Eternal A → Eternalᵒ ⟦ A ⟧ᵛ
eternalᵛ-Eternalᵒ (Baseₑ {b} eb) = ⟦ b ⟧ᵇᵉ eb
eternalᵛ-Eternalᵒ Unitₑ          = 𝟙-eternalᵒ
eternalᵛ-Eternalᵒ Boolₑ          = 𝔹-eternalᵒ
eternalᵛ-Eternalᵒ Natₑ           = ℕ-eternalᵒ
eternalᵛ-Eternalᵒ Emptyₑ         = 𝟘-eternalᵒ
eternalᵛ-Eternalᵒ (et₁ |×|ₑ et₂) =
  ×-eternalᵒ (eternalᵛ-Eternalᵒ et₁) (eternalᵛ-Eternalᵒ et₂)
eternalᵛ-Eternalᵒ (et₁ |+|ₑ et₂) =
  +-eternalᵒ (eternalᵛ-Eternalᵒ et₁) (eternalᵛ-Eternalᵒ et₂)
eternalᵛ-Eternalᵒ (|List|ₑ et)   = List-eternalᵒ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction at an arbitrary grade.

eternalᵛ-extᵉ : ∀ {A} → Eternal A → ∀ {ρ} → ⟨ ρ ⟩ᵒ ⟦ A ⟧ᵛ →ᵐ ⟦ A ⟧ᵛ
eternalᵛ-extᵉ et = Eternalᵒ.extᵉ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction is uniform in the grade, is the possibility counit
-- `εᵘ` at the unit grade, and is a graded `⟨_⟩`-algebra.

eternalᵛ-extᵉ-≤ : ∀ {A} → (et : Eternal A) → ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ᵣ ρ₂)
                → eternalᵛ-extᵉ et {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ eternalᵛ-extᵉ et {ρ₁}
eternalᵛ-extᵉ-≤ et = Eternalᵒ.extᵉ-≤ (eternalᵛ-Eternalᵒ et)

eternalᵛ-extᵉ-u : ∀ {A} → (et : Eternal A) → eternalᵛ-extᵉ et {uᵣ} ≈ᵐ εᵘ
eternalᵛ-extᵉ-u et = Eternalᵒ.extᵉ-u (eternalᵛ-Eternalᵒ et)

eternalᵛ-extᵉ-μ : ∀ {A} → (et : Eternal A) → ∀ {ρ₁ ρ₂}
                → eternalᵛ-extᵉ et {ρ₂ ·ᵣ ρ₁} ∘ᵐ μ {⟦ A ⟧ᵛ} {ρ₁} {ρ₂}
                ≈ᵐ eternalᵛ-extᵉ et {ρ₁} ∘ᵐ ⟨ ρ₁ ⟩ᶠ (eternalᵛ-extᵉ et {ρ₂})
eternalᵛ-extᵉ-μ et = Eternalᵒ.extᵉ-μ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction does not depend on how eternality was established
-- (`Eternal` is a property — see `MonomorphicCalculus.Syntax.Types.eternal-irrelevant`).

eternalᵛ-extᵉ-irr : ∀ {A} → (et et' : Eternal A) → ∀ {ρ}
                  → eternalᵛ-extᵉ et {ρ} ≈ᵐ eternalᵛ-extᵉ et' {ρ}
eternalᵛ-extᵉ-irr et et' with eternal-irrelevant et et'
... | refl = ≈ᵐ-refl

-- The morphism interpreting a variable: project, then extract.

var-morphism : ∀ {Γ A ρ} → (¬ Eternal A → ρ ≾ᵣ uᵣ) → A ∈[ ρ ] Γ
             → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
var-morphism {A = A} f x with eternal? A
... | yes et = eternalᵛ-extᵉ et ∘ᵐ var-proj x
... | no ¬et = εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj x

-- Unfold `var-morphism` at an eternal type (handles the internal `eternal?`).

var-morphism-unfoldᵉ : ∀ {Γ A ρ} → (et : Eternal A) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
                     → (y : A ∈[ ρ ] Γ)
                     → var-morphism f y ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ var-proj y
var-morphism-unfoldᵉ {A = A} et f y with eternal? A
... | yes et' = ∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et)
... | no ¬et = ⊥-elim (¬et et)

-- Two facts about `var-morphism` at the top of a context, used wherever a
-- renaming's denotation has to be computed.

private
  infixr 3 _∙ᵛ_
  _∙ᵛ_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙ᵛ_ = ≈ᵐ-trans

-- The head variable denotes the second projection: at a non-eternal type the
-- grade bound is reflexive and the possibility counit cancels `η`; at an
-- eternal one the extraction cancels it.
var-morphism-Hd : ∀ {Γ A} → (f : ¬ Eternal A → uᵣ ≾ᵣ uᵣ)
                → var-morphism {Γ ∷ A} f Hd ≈ᵐ sndᵐ
var-morphism-Hd {A = A} f with eternal? A
... | yes et =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵛ ∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et) ∙ᵛ ⟨⟩-εᵘ∘η≡id)
  ∙ᵛ ∘ᵐ-identityˡ _
... | no ¬et =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr (f ¬et) ≾ᵣ-refl ∙ᵛ ⟨⟩-≤-refl) ∙ᵛ ∘ᵐ-identityˡ _)
  ∙ᵛ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵛ ∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id
  ∙ᵛ ∘ᵐ-identityˡ _

-- Weakening a variable past a `∷` projects the environment.
var-morphism-Tl-∷ : ∀ {Γ A B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                  → var-morphism {Γ ∷ A} f (Tl-∷ y) ≈ᵐ var-morphism f y ∘ᵐ fstᵐ
var-morphism-Tl-∷ {B = B} y f with eternal? B
... | yes et = ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
... | no ¬et = ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
