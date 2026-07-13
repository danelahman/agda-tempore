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
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; ε)
open Past Pst
open Adjunction Adj using (ε⊣; ε⊣-≤; ε⊣-u)
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

-- Eternal extraction is uniform in the grade (base from `Eternalᵒ.extᵉ-≤`;
-- `Unit`/`Empty` by (co)uniqueness, product functorially).

eternalᵛ-extᵉ-≤ : ∀ {A} → (et : Eternal A) → ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ᵣ ρ₂)
                → eternalᵛ-extᵉ et {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ eternalᵛ-extᵉ et {ρ₁}
eternalᵛ-extᵉ-≤ (Baseₑ b eb)   p = Eternalᵒ.extᵉ-≤ (⟦ b ⟧ᵇᵉ eb) p
eternalᵛ-extᵉ-≤ Unitₑ          p = terminalᵐ-unique
eternalᵛ-extᵉ-≤ Emptyₑ         p =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-nat _ p))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (ε⊣-≤ p))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ ([]-≤ p) _)))
            (∘ᵐ-congʳ (⟨⟩-congᶠ initialᵐ-unique)))))))
eternalᵛ-extᵉ-≤ (et₁ |×|ₑ et₂) p =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ ⟨ ⟨⟩-≤-nat _ p , ⟨⟩-≤-nat _ p ⟩ᵐ-cong)
  (≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
  (≈ᵐ-trans (⟨ ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (eternalᵛ-extᵉ-≤ et₁ p))
             , ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (eternalᵛ-extᵉ-≤ et₂ p)) ⟩ᵐ-cong)
            (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))))))

-- At the unit grade the eternal extraction is the possibility counit `εᵘ`.

eternalᵛ-extᵉ-u : ∀ {A} → (et : Eternal A) → eternalᵛ-extᵉ et {uᵣ} ≈ᵐ εᵘ
eternalᵛ-extᵉ-u (Baseₑ b eb)   = Eternalᵒ.extᵉ-u (⟦ b ⟧ᵇᵉ eb)
eternalᵛ-extᵉ-u Unitₑ          = ≈ᵐ-sym terminalᵐ-unique
eternalᵛ-extᵉ-u Emptyₑ         =
  ≈ᵐ-trans (∘ᵐ-congˡ ε⊣-u)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ ε _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-trans initialᵐ-unique (≈ᵐ-sym initialᵐ-unique))))
  (≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
            (∘ᵐ-identityʳ εᵘ)))))
eternalᵛ-extᵉ-u (et₁ |×|ₑ et₂) =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨ ∘ᵐ-congˡ (eternalᵛ-extᵉ-u et₁) , ∘ᵐ-congˡ (eternalᵛ-extᵉ-u et₂) ⟩ᵐ-cong)
  (≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (εᵘ-nat fstᵐ) , ≈ᵐ-sym (εᵘ-nat sndᵐ) ⟩ᵐ-cong)
  (≈ᵐ-trans (≈ᵐ-sym (⟨⟩ᵐ-∘ fstᵐ sndᵐ εᵘ))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ fstᵐ) (∘ᵐ-identityʳ sndᵐ))))
            (∘ᵐ-identityˡ εᵘ)))))

-- `η` after eternal extraction at grade `ρ` (with `ρ ≾ uᵣ`) is the grade
-- relaxation `⟨⟩-≤`: the eternal value is available regardless of budget.

eternalᵛ-η-ext : ∀ {A} → (et : Eternal A) → ∀ {ρ} → (p : ρ ≾ᵣ uᵣ)
               → η ∘ᵐ eternalᵛ-extᵉ et {ρ} ≈ᵐ ⟨⟩-≤ p
eternalᵛ-η-ext et p =
  ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et p)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-η∘εᵘ≡id)
            (∘ᵐ-identityˡ (⟨⟩-≤ p)))))

-- The morphism interpreting a variable: project, then extract.

var-morphism : ∀ {Γ A ρ} → (¬ Eternal A → ρ ≾ᵣ uᵣ) → A ∈[ ρ ] Γ
             → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
var-morphism {A = A} f x with eternal? A
... | yes et = eternalᵛ-extᵉ et ∘ᵐ var-proj x
... | no ¬et = εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj x
