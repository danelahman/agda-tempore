------------------------------------------------------------------------
-- Interpretation of variables.                                         --
--                                                                    --
-- A variable `x : A ∈[ ρ ] Γ` is projected through the context to the  --
-- context modality at its accumulated grade, `var-proj x :              --
-- ⟦ Γ ⟧ →ᵐ ⟨ ρ ⟩ᵒ ⟦ A ⟧`. It is then extracted to `⟦ A ⟧`: for a        --
-- non-eternal type this needs `ρ ≾ uᵣ` and uses the unit-graded counit   --
-- `εᵘ`; for an eternal type it uses the eternal extraction `extᵉ` at     --
-- the arbitrary grade `ρ`.                                              --
--                                                                    --
-- The `Eternalᵒ` structure of an eternal type is assembled by recursion   --
-- on the eternality witness from the per-former structure supplied by     --
-- `GroundEternal` (base types, `Unit`, `Empty`, and products). Landing in --
-- `Eternalᵒ` means the eternal laws — grade-uniformity `extᵉ-≤`, the unit --
-- grade `extᵉ-u`, and the `⟨_⟩`-algebra law `extᵉ-μ` — are inherited      --
-- rather than re-proved for each former.                                  --
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

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
         (Mon : Monad S Cat Fut Pst Adj GTy)
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

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon

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
eternalᵛ-Eternalᵒ (Baseₑ b eb)   = ⟦ b ⟧ᵇᵉ eb
eternalᵛ-Eternalᵒ Unitₑ          = 𝟙-eternalᵒ
eternalᵛ-Eternalᵒ Emptyₑ         = 𝟘-eternalᵒ
eternalᵛ-Eternalᵒ (et₁ |×|ₑ et₂) =
  ×-eternalᵒ (eternalᵛ-Eternalᵒ et₁) (eternalᵛ-Eternalᵒ et₂)

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

-- The eternal `⟨_⟩`-strength at an arbitrary grade, and its β-rules reading
-- back the two factors. Used to interpret `⟨⟩-ext-ren` (extruding an eternal
-- variable past a lock).

eternalᵛ-strᵉ : ∀ {A} → (et : Eternal A) → ∀ {ρ X} → ⟨ ρ ⟩ᵒ X ×ᵐ ⟦ A ⟧ᵛ →ᵐ ⟨ ρ ⟩ᵒ (X ×ᵐ ⟦ A ⟧ᵛ)
eternalᵛ-strᵉ et = Eternalᵒ.strᵉ (eternalᵛ-Eternalᵒ et)

eternalᵛ-strᵉ-fstᵐ : ∀ {A} → (et : Eternal A) → ∀ {ρ X}
                   → ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ eternalᵛ-strᵉ et {ρ} {X} ≈ᵐ fstᵐ
eternalᵛ-strᵉ-fstᵐ et = Eternalᵒ.strᵉ-fstᵐ (eternalᵛ-Eternalᵒ et)

eternalᵛ-strᵉ-sndᵐ : ∀ {A} → (et : Eternal A) → ∀ {ρ X}
                   → eternalᵛ-extᵉ et ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ eternalᵛ-strᵉ et {ρ} {X} ≈ᵐ sndᵐ
eternalᵛ-strᵉ-sndᵐ et = Eternalᵒ.strᵉ-sndᵐ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction does not depend on how eternality was established
-- (`Eternal` is a property — see `Syntax.Types.eternal-irrelevant`).

eternalᵛ-extᵉ-irr : ∀ {A} → (et et' : Eternal A) → ∀ {ρ}
                  → eternalᵛ-extᵉ et {ρ} ≈ᵐ eternalᵛ-extᵉ et' {ρ}
eternalᵛ-extᵉ-irr et et' with eternal-irrelevant et et'
... | refl = ≈ᵐ-refl

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

-- The eternal restriction of a context interprets to an *eternal* object,
-- assembled by recursion following `_ᴱ`: `[]` and locks give `𝟙`/nothing, an
-- eternal variable a factor with its own eternal structure, a non-eternal
-- variable nothing. This is what a handler's eternal parameter `⟦ Γ ᴱ ⟧` is.

⟦_⟧ᴱ-Eternalᵒ : (Γ : Ctx) → Eternalᵒ ⟦ Γ ᴱ ⟧ᶜᵗˣ
⟦ [] ⟧ᴱ-Eternalᵒ      = 𝟙-eternalᵒ
⟦ Γ ∷ A ⟧ᴱ-Eternalᵒ   with eternal? A
... | yes et = ×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)
... | no  _  = ⟦ Γ ⟧ᴱ-Eternalᵒ
⟦ Γ ⟨ ρ ⟩ ⟧ᴱ-Eternalᵒ = ⟦ Γ ⟧ᴱ-Eternalᵒ

-- The eternal projection: discard the non-eternal / time-passed part of the
-- context, keeping the eternal skeleton. Under a lock it uses the eternal
-- extraction `extᵉ` of the (eternal) restricted context.

projᴱ : (Γ : Ctx) → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
projᴱ []        = idᵐ
projᴱ (Γ ∷ A)   with eternal? A
... | yes _ = mapˣᵐ (projᴱ Γ) idᵐ
... | no  _ = projᴱ Γ ∘ᵐ fstᵐ
projᴱ (Γ ⟨ ρ ⟩) = Eternalᵒ.extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) ∘ᵐ ⟨ ρ ⟩ᶠ (projᴱ Γ)

-- The eternal extraction of a restricted context (its `Eternalᵒ` structure).

projᴱ-extᵉ : (Γ : Ctx) → ∀ {ρ} → ⟨ ρ ⟩ᵒ ⟦ Γ ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
projᴱ-extᵉ Γ {ρ} = Eternalᵒ.extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) {ρ}

-- `fstᵐ`/`sndᵐ` intertwine the extraction of an eternal `∷`-extension with the
-- extractions of the two factors (from `×-eternalᵒ-extᵉ`).

projᴱ-extᵉ-fst : ∀ {Γ A} → (et : Eternal A) → ∀ {ρ}
               → fstᵐ ∘ᵐ Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)) {ρ}
               ≈ᵐ projᴱ-extᵉ Γ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
projᴱ-extᵉ-fst {Γ} et =
  ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)))
           (⟨⟩ᵐ-fstᵐ _ _)

×-eternalᵒ-sndᵉ : ∀ {Γ A} → (et : Eternal A) → ∀ {ρ}
                → sndᵐ ∘ᵐ Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)) {ρ}
                ≈ᵐ eternalᵛ-extᵉ et {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ
×-eternalᵒ-sndᵉ {Γ} et =
  ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)))
           (⟨⟩ᵐ-sndᵐ _ _)


-- The interpretation of an eternal variable (projected into `Γ ᴱ`) is a
-- morphism of eternal objects: it commutes with the eternal extractions. This
-- is what carries the eternal parameter across a lock in `var-projᴱ` below.
-- Proved by recursion on the variable; `Γ ᴱ` is lock-free, so only the `∷`
-- structure is traversed (the `⟨⟩` case just drops the lock).

eternal-mor : ∀ {Γ A ρ₀} → (et : Eternal A) → (x : A ∈[ ρ₀ ] Γ) → ∀ {ρ}
            → eternalᵛ-extᵉ et {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (eternalᵛ-extᵉ et {uᵣ} ∘ᵐ var-proj (∈-ᴱ et x))
            ≈ᵐ (eternalᵛ-extᵉ et {uᵣ} ∘ᵐ var-proj (∈-ᴱ et x)) ∘ᵐ projᴱ-extᵉ Γ
eternal-mor {Γ ∷ A} et Hd {ρ} with eternal? A
... | yes eA =
  -- g = extᵉ{uᵣ} ∘ η ∘ sndᵐ ≈ sndᵐ; both sides reduce to the 2nd projection
  -- of the product extraction (`×-eternalᵒ-extᵉ`), up to `extᵉ` irrelevance.
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ g≈snd))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et eA))
  (≈ᵐ-trans (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eA))))
            (∘ᵐ-congˡ (≈ᵐ-sym g≈snd)))))
  where
    g≈snd : eternalᵛ-extᵉ et {uᵣ} ∘ᵐ (η ∘ᵐ sndᵐ) ≈ᵐ sndᵐ
    g≈snd =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et)))
      (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id)
                (∘ᵐ-identityˡ sndᵐ)))
... | no ¬eA = ⊥-elim (¬eA et)
eternal-mor {Γ ∷ B} et (Tl-∷ x) {ρ} with eternal? B
... | yes eB =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternal-mor et x))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (×-fstᵐ-extᵉ B eB)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))))
  where
    -- fstᵐ intertwines the product extraction with the sub-context extraction
    ×-fstᵐ-extᵉ : (B : VType) → (eB : Eternal B)
                → fstᵐ ∘ᵐ Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eB)) {ρ}
                ≈ᵐ projᴱ-extᵉ Γ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
    ×-fstᵐ-extᵉ B eB =
      ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eB)))
               (⟨⟩ᵐ-fstᵐ _ _)
... | no ¬eB = eternal-mor et x
eternal-mor {Γ ⟨ ρ' ⟩} et (Tl-⟨⟩ x) = eternal-mor et x

-- The interpretation of an eternal variable factors through the eternal
-- projection `projᴱ Γ`: interpreting it in `Γ` equals interpreting its image
-- `∈-ᴱ et x` in `Γ ᴱ`, precomposed with the projection. This is the variable
-- case of `projᴱ`-naturality. The lock case uses `eternalᵛ-extᵉ-μ` (to split
-- the extraction across the lock) and `eternal-mor` (to carry it under `⟨ ρ ⟩`).

var-projᴱ : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
          → eternalᵛ-extᵉ et {ρ} ∘ᵐ var-proj x
          ≈ᵐ (eternalᵛ-extᵉ et {uᵣ} ∘ᵐ var-proj (∈-ᴱ et x)) ∘ᵐ projᴱ Γ
var-projᴱ {Γ ∷ A} et Hd with eternal? A
... | yes eA =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))
              (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))
... | no ¬eA = ⊥-elim (¬eA et)
var-projᴱ {Γ ∷ B} et (Tl-∷ x) with eternal? B
... | yes eB =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (var-projᴱ et x))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))
... | no ¬eB =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (var-projᴱ et x))
            (∘ᵐ-assoc _ _ _))
var-projᴱ {Γ ⟨ ρ' ⟩} et (Tl-⟨⟩ {ρ = ρ'} x) =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (var-projᴱ et x)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternal-mor et x))
            (∘ᵐ-assoc _ _ _))))))))

-- The eternal variable case of `projᴱ`-naturality, packaged at `var-morphism`
-- level: a variable of eternal type factors through the eternal projection.

var-morphism-eternal : ∀ {Γ A ρ} → (p : ρ ≾ᵣ uᵣ) → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
                     → var-morphism (λ _ → p) x
                     ≈ᵐ var-morphism (λ _ → ≾ᵣ-refl) (∈-ᴱ et x) ∘ᵐ projᴱ Γ
var-morphism-eternal {A = A} p et x with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))
  (≈ᵐ-trans (var-projᴱ et x)
            (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))
... | no ¬et = ⊥-elim (¬et et)

-- `var-morphism` of an eternal variable in `Γ ᴱ` is a morphism of eternal
-- objects (it commutes with the extractions). Unfolds `var-morphism` and
-- applies `eternal-mor`. Used by `restrict-ren`'s variable case.

var-morphism-∈ᴱ-mor : ∀ {Γ A ρ₀} → (et : Eternal A) → (x : A ∈[ ρ₀ ] Γ) → ∀ {ρ}
                    → eternalᵛ-extᵉ et {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (var-morphism (λ _ → ≾ᵣ-refl) (∈-ᴱ et x))
                    ≈ᵐ var-morphism (λ _ → ≾ᵣ-refl) (∈-ᴱ et x) ∘ᵐ projᴱ-extᵉ Γ
var-morphism-∈ᴱ-mor {A = A} et x with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))))
  (≈ᵐ-trans (eternal-mor et x)
            (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))
... | no ¬et = ⊥-elim (¬et et)

-- Unfold `var-morphism` at an eternal type (handles the internal `eternal?`).

var-morphism-unfoldᵉ : ∀ {Γ A ρ} → (et : Eternal A) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
                     → (y : A ∈[ ρ ] Γ)
                     → var-morphism f y ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ var-proj y
var-morphism-unfoldᵉ {A = A} et f y with eternal? A
... | yes et' = ∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et)
... | no ¬et = ⊥-elim (¬et et)

-- ═══════════════════════════════════════════════════════════════════════════
-- SPLITTING AN EXTENDED CONTEXT ALONG ITS ETERNAL BASE
--
-- The eternal base `⟦ Γ ᴱ ⟧` is an `Eternalᵒ` object, so it distributes out of
-- every lock in an extension `Γ'` (via `strᵉ`/`costrᵉ`) and hence splits off as
-- a product factor:  `⟦ Γ ᴱ ++ᶜ Γ' ⟧ ≅ ⟦ Γ' ⟧ ×ᵐ ⟦ Γ ᴱ ⟧`  — eternal on the
-- right, matching the strength's orientation. This is what makes the eternal
-- base act functorially in the extension `Γ'`.
-- ═══════════════════════════════════════════════════════════════════════════

-- Swap the last two factors of a left-nested triple (its own inverse).
swap₂₃ : ∀ {Y A B} → (Y ×ᵐ A) ×ᵐ B →ᵐ (Y ×ᵐ B) ×ᵐ A
swap₂₃ = ⟨ ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ

swap₂₃-iso : ∀ {Y A B} → swap₂₃ {Y} {B} {A} ∘ᵐ swap₂₃ {Y} {A} {B} ≈ᵐ idᵐ
swap₂₃-iso =
  ≈ᵐ-trans (⟨⟩ᵐ-unique fstᵐ sndᵐ (swap₂₃ ∘ᵐ swap₂₃) fst-eq snd-eq)
           (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))
  where
    fst-eq : fstᵐ ∘ᵐ (swap₂₃ ∘ᵐ swap₂₃) ≈ᵐ fstᵐ
    fst-eq =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ swap₂₃ swap₂₃))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ swap₂₃)
      (≈ᵐ-trans (⟨ ≈ᵐ-trans (∘ᵐ-assoc fstᵐ fstᵐ swap₂₃)
                            (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _))
                 , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
                (≈ᵐ-sym (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ fstᵐ) (sndᵐ ∘ᵐ fstᵐ) fstᵐ ≈ᵐ-refl ≈ᵐ-refl)))))
    snd-eq : sndᵐ ∘ᵐ (swap₂₃ ∘ᵐ swap₂₃) ≈ᵐ sndᵐ
    snd-eq =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ swap₂₃ swap₂₃))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
      (≈ᵐ-trans (∘ᵐ-assoc sndᵐ fstᵐ swap₂₃)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                (⟨⟩ᵐ-sndᵐ _ _))))

-- The forward split: `⟦ Γ ᴱ ++ᶜ Γ' ⟧ →ᵐ ⟦ Γ' ⟧ ×ᵐ ⟦ Γ ᴱ ⟧`, by recursion on
-- the extension. The lock case is exactly the eternal costrength.
splitᴱ : (Γ Γ' : Ctx) → ⟦ Γ ᴱ ++ᶜ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ ×ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
splitᴱ Γ []         = ⟨ terminalᵐ , idᵐ ⟩ᵐ
splitᴱ Γ (Γ' ∷ A)   = swap₂₃ ∘ᵐ mapˣᵐ (splitᴱ Γ Γ') idᵐ
splitᴱ Γ (Γ' ⟨ ρ ⟩) = Eternalᵒ.costrᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) ∘ᵐ ⟨ ρ ⟩ᶠ (splitᴱ Γ Γ')

-- Its inverse (the eternal strength in the lock case).
splitᴱ⁻¹ : (Γ Γ' : Ctx) → ⟦ Γ' ⟧ᶜᵗˣ ×ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ++ᶜ Γ' ⟧ᶜᵗˣ
splitᴱ⁻¹ Γ []         = sndᵐ
splitᴱ⁻¹ Γ (Γ' ∷ A)   = mapˣᵐ (splitᴱ⁻¹ Γ Γ') idᵐ ∘ᵐ swap₂₃
splitᴱ⁻¹ Γ (Γ' ⟨ ρ ⟩) = ⟨ ρ ⟩ᶠ (splitᴱ⁻¹ Γ Γ') ∘ᵐ Eternalᵒ.strᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ)

splitᴱ-iso : (Γ Γ' : Ctx) → splitᴱ Γ Γ' ∘ᵐ splitᴱ⁻¹ Γ Γ' ≈ᵐ idᵐ
splitᴱ-iso Γ [] =
  ≈ᵐ-trans (⟨⟩ᵐ-∘ terminalᵐ idᵐ sndᵐ)
  (≈ᵐ-trans (⟨ ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique)
             , ∘ᵐ-identityˡ sndᵐ ⟩ᵐ-cong)
            (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _))))
splitᴱ-iso Γ (Γ' ∷ A) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ MM⁻≈id))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) swap₂₃-iso)))
  where
    MM⁻≈id = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
             (≈ᵐ-trans (mapˣᵐ-cong (splitᴱ-iso Γ Γ') (∘ᵐ-identityˡ _)) mapˣᵐ-idᵐ)
splitᴱ-iso Γ (Γ' ⟨ ρ ⟩) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ bc≈id))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
            (Eternalᵒ.strᵉ-costrᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ)))))
  where
    bc≈id = ≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-trans (⟨⟩-congᶠ (splitᴱ-iso Γ Γ')) ⟨⟩-idᵐ)

splitᴱ⁻¹-iso : (Γ Γ' : Ctx) → splitᴱ⁻¹ Γ Γ' ∘ᵐ splitᴱ Γ Γ' ≈ᵐ idᵐ
splitᴱ⁻¹-iso Γ []         = ⟨⟩ᵐ-sndᵐ terminalᵐ idᵐ
splitᴱ⁻¹-iso Γ (Γ' ∷ A) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ swap₂₃-iso))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) M⁻M≈id)))
  where
    M⁻M≈id = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
             (≈ᵐ-trans (mapˣᵐ-cong (splitᴱ⁻¹-iso Γ Γ') (∘ᵐ-identityˡ _)) mapˣᵐ-idᵐ)
splitᴱ⁻¹-iso Γ (Γ' ⟨ ρ ⟩) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (Eternalᵒ.costrᵉ-strᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) cb≈id)))
  where
    cb≈id = ≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-trans (⟨⟩-congᶠ (splitᴱ⁻¹-iso Γ Γ')) ⟨⟩-idᵐ)

-- ───────────────────────────────────────────────────────────────────────────
-- THE FUNCTORIAL LIFT OF AN EXTENSION MAP UNDER THE ETERNAL BASE
--
-- A map `ρ : ⟦ Γ' ⟧ →ᵐ ⟦ Γ'' ⟧` between extensions lifts to one between the
-- extended contexts, acting only on the extension and identity on `⟦ Γ ᴱ ⟧`.
-- This is the action that makes the handler clauses a functor of the extension.
-- ───────────────────────────────────────────────────────────────────────────

infix 8 _⋉_

_⋉_ : (Γ : Ctx) → ∀ {Γ' Γ''} → (⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ'' ⟧ᶜᵗˣ)
    → ⟦ Γ ᴱ ++ᶜ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ++ᶜ Γ'' ⟧ᶜᵗˣ
_⋉_ Γ {Γ'} {Γ''} ρ = splitᴱ⁻¹ Γ Γ'' ∘ᵐ mapˣᵐ ρ idᵐ ∘ᵐ splitᴱ Γ Γ'

-- congruence, so a lifted map can be rewritten. `⟦_⟧ᶜᵗˣ` is not injective, so
-- the extensions can only be pinned by an occurrence outside `⟦_⟧` — the clause
-- application at the `CtxParamʰ` use site. These standalone laws lack that
-- anchor, so they take the extensions explicitly and pass them to `_⋉_`.
⋉-cong : (Γ Γ' Γ'' : Ctx) → {ρ ρ' : ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ'' ⟧ᶜᵗˣ}
       → ρ ≈ᵐ ρ' → _⋉_ Γ {Γ'} {Γ''} ρ ≈ᵐ _⋉_ Γ {Γ'} {Γ''} ρ'
⋉-cong Γ Γ' Γ'' p = ∘ᵐ-congʳ (∘ᵐ-congˡ (mapˣᵐ-cong p ≈ᵐ-refl))

-- functoriality: identities and composition
⋉-id : (Γ Γ' : Ctx) → _⋉_ Γ {Γ'} {Γ'} (idᵐ {⟦ Γ' ⟧ᶜᵗˣ}) ≈ᵐ idᵐ
⋉-id Γ Γ' =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ mapˣᵐ-idᵐ))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
            (splitᴱ⁻¹-iso Γ Γ'))

⋉-∘ : (Γ Γ' Γ'' Γ''' : Ctx)
    → (σ : ⟦ Γ'' ⟧ᶜᵗˣ →ᵐ ⟦ Γ''' ⟧ᶜᵗˣ) → (ρ : ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ'' ⟧ᶜᵗˣ)
    → _⋉_ Γ {Γ'} {Γ'''} (σ ∘ᵐ ρ)
    ≈ᵐ _⋉_ Γ {Γ''} {Γ'''} σ ∘ᵐ _⋉_ Γ {Γ'} {Γ''} ρ
⋉-∘ Γ Γ' Γ'' Γ''' σ ρ = ≈ᵐ-sym
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (∘ᵐ-congʳ
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (splitᴱ-iso Γ Γ''))
                  (∘ᵐ-identityˡ _))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congˡ (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong ≈ᵐ-refl (∘ᵐ-identityˡ _)))))))))

-- lifting the terminal map is the projection onto the eternal base; this is
-- what discharges the operational `term∅` instance (at `Γ ᴱ ≡ []`).
⋉-proj : (Γ Γ' : Ctx)
       → _⋉_ Γ {Γ'} {[]} (terminalᵐ {⟦ Γ' ⟧ᶜᵗˣ}) ≈ᵐ sndᵐ ∘ᵐ splitᴱ Γ Γ'
⋉-proj Γ Γ' =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
           (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _)))

-- ───────────────────────────────────────────────────────────────────────────
-- NATURALITY OF THE SPLIT UNDER A MORPHISM OF THE ETERNAL BASE
--
-- Generic building block: `costrᵉ` is natural in the eternal factor along any
-- morphism of eternal objects `m` (one that commutes with the extractions).
-- This is what carries `splitᴱ` across an ambient renaming/substitution, whose
-- eternal-base action (`restrict-ren`/`restrict-sub-env`) is exactly such a
-- morphism (`restrict-ren-mor` / `restrict-sub-env-extᵉ`).
-- ───────────────────────────────────────────────────────────────────────────

costrᵉ-nat : ∀ {P P'} → (eP : Eternalᵒ P) → (eP' : Eternalᵒ P') → (m : P' →ᵐ P)
           → (m-mor : ∀ {ρ} → Eternalᵒ.extᵉ eP {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ m
                            ≈ᵐ m ∘ᵐ Eternalᵒ.extᵉ eP' {ρ})
           → ∀ {ρ X} → Eternalᵒ.costrᵉ eP {ρ} {X} ∘ᵐ ⟨ ρ ⟩ᶠ (mapˣᵐ idᵐ m)
                     ≈ᵐ mapˣᵐ idᵐ m ∘ᵐ Eternalᵒ.costrᵉ eP' {ρ} {X}
costrᵉ-nat eP eP' m m-mor {ρ} {X} =
  ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
  (≈ᵐ-trans
    (⟨ -- first factor: both reduce to `⟨ρ⟩ᶠ fstᵐ`
       ≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
         (≈ᵐ-trans (⟨⟩-congᶠ (≈ᵐ-trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)))
                   (≈ᵐ-sym (∘ᵐ-identityˡ _)))
     -- second factor: naturality of the extraction (`m-mor`)
     , ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
         (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
         (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
         (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congˡ m-mor) (∘ᵐ-assoc _ _ _))))))
     ⟩ᵐ-cong)
    (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _)))

-- `swap₂₃` is natural in its middle (`A`) factor.
swap₂₃-nat : ∀ {Y A A' B} → (g : A →ᵐ A')
           → swap₂₃ {Y} {A'} {B} ∘ᵐ mapˣᵐ (mapˣᵐ idᵐ g) idᵐ
           ≈ᵐ mapˣᵐ idᵐ g ∘ᵐ swap₂₃ {Y} {A} {B}
swap₂₃-nat g =
  ≈ᵐ-trans (⟨⟩ᵐ-unique _ _ _ ≈ᵐ-refl ≈ᵐ-refl)
           (≈ᵐ-sym (⟨⟩ᵐ-unique _ _ _ (≈ᵐ-sym fst-eq) (≈ᵐ-sym snd-eq)))
  where
    fst-inner =
      ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)))))
    fst-eq =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
      (≈ᵐ-trans (⟨ fst-inner , ≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _) ⟩ᵐ-cong)
      (≈ᵐ-sym
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _))
                  (⟨⟩ᵐ-fstᵐ _ _))))))))
    snd-eq =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-sym
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                  (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))))))))))
