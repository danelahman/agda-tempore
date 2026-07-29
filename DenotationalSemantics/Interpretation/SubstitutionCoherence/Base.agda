------------------------------------------------------------------------
-- The environment morphism of a substitution, and eternal values.
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad
module DenotationalSemantics.Interpretation.SubstitutionCoherence.Base
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S
open import Syntax.Substitutions S
open import Syntax.Renamings.Equivalence S using (eternal?-no; unbox-var-ren)

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open GroundEternal GE
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE


-- The environment morphism realising the substitution of `W` for `x`:
-- rebuild a `Γ`-environment from one for `Γ` with `x` removed, by
-- computing the missing component with `⟦ W ⟧`.

-- `eternal-val-ext`/`eternal-val-restrict` build only variables, constants,
-- units and pairs — never a `lam` — so their results are parametric outright.

eternal-val-extᴾ : ∀ {Γ A ρ} → (et : Eternal A) → (V : Γ ⊢V⦂ A)
                 → Paramᵛ (eternal-val-ext {ρ = ρ} et V)
eternal-val-extᴾ et (var _ x)                  = tt
eternal-val-extᴾ _  (const b)                  = tt
eternal-val-extᴾ _  ⋆                          = tt
eternal-val-extᴾ (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊    =
  eternal-val-extᴾ et₁ V₁ , eternal-val-extᴾ et₂ V₂

eternal-val-restrictᴾ : ∀ {Γ A} → (et : Eternal A) → (V : Γ ⊢V⦂ A)
                      → Paramᵛ (eternal-val-restrict et V)
eternal-val-restrictᴾ et (var _ x)               = tt
eternal-val-restrictᴾ _  (const b)               = tt
eternal-val-restrictᴾ _  ⋆                       = tt
eternal-val-restrictᴾ (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  eternal-val-restrictᴾ et₁ V₁ , eternal-val-restrictᴾ et₂ V₂

sub-env : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A) → Paramᵛ W
        → ⟦ split-l x ++ᶜ split-r x ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
sub-env Hd                W pW = ⟨ idᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
sub-env (Tl-∷ x)          W pW = mapˣᵐ (sub-env x W pW) idᵐ
sub-env (Tl-⟨⟩ {ρ = ρ} x) W pW = ⟨ ρ ⟩ᶠ (sub-env x W pW)

-- (`var-morphism-Tl-∷` lives in `Interpretation.Variables`.)

-- Weakening a value of *eternal* type under a lock: denotationally this is
-- the eternal extraction applied to the locked environment. Proved by
-- induction on the value (only the eternal formers can occur).

eternal-val-ext-nat : ∀ {Γ A ρ} → (et : Eternal A) → (V : Γ ⊢V⦂ A) → (pV : Paramᵛ V)
                    → ⟦ eternal-val-ext {ρ = ρ} et V ⟧ᵛᵗ (eternal-val-extᴾ et V)
                      ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ ⟨ ρ ⟩ᶠ (⟦ V ⟧ᵛᵗ pV)

eternal-val-ext-nat {A = A} et (var f y) _ with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))))))
... | no ¬et' = ⊥-elim (¬et' et)
eternal-val-ext-nat (Baseₑ b eb) (const c) _ =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (⟦⟧ᵇᶜ-eternal eb c))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat Unitₑ ⋆ _ =
  ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique)
eternal-val-ext-nat (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ (p₁ , p₂) =
  ≈ᵐ-trans (⟨ eternal-val-ext-nat et₁ V₁ p₁ , eternal-val-ext-nat et₂ V₂ p₂ ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
             , ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))) ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) , ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) , ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong)
  (≈ᵐ-trans (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (×-eternalᵒ-extᵉ (eternalᵛ-Eternalᵒ et₁)
                                              (eternalᵛ-Eternalᵒ et₂))))))))

-- The eternal-parameter transform induced by a substitution: the restriction
-- of `sub-env` to the eternal skeletons. Defined by recursion on the variable,
-- mirroring `sub-env`; at the head an eternal-typed substituend contributes its
-- restricted value, and locks are dropped. This is the substitution analog of
-- `restrict-ren`'s interpretation.

restrict-sub-env : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
                 → ⟦ (split-l x ++ᶜ split-r x) ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
restrict-sub-env {A = A} Hd W with eternal? A
... | yes et = ⟨ idᵐ , ⟦ eternal-val-restrict et W ⟧ᵛᵗ (eternal-val-restrictᴾ et W) ⟩ᵐ
... | no  _  = idᵐ
restrict-sub-env (Tl-∷ {B = B} x) W with eternal? B
... | yes _ = mapˣᵐ (restrict-sub-env x W) idᵐ
... | no  _ = restrict-sub-env x W
restrict-sub-env (Tl-⟨⟩ x) W = restrict-sub-env x W

-- An eternal value's interpretation factors through the eternal projection:
-- the value-level counterpart of `var-projᴱ` (and the value analog of
-- `eternal-val-ext-nat`). This carries the substituted eternal value onto the
-- eternal parameter in the handler substitution coherence below.

eternal-val-restrict-nat : ∀ {Γ A} → (et : Eternal A) → (V : Γ ⊢V⦂ A) → (pV : Paramᵛ V)
                         → ⟦ V ⟧ᵛᵗ pV
                         ≈ᵐ ⟦ eternal-val-restrict et V ⟧ᵛᵗ (eternal-val-restrictᴾ et V)
                              ∘ᵐ projᴱ Γ
-- The interpretation of a *restricted* eternal value is a morphism of eternal
-- objects (commutes with the extractions). Its variables are all `∈-ᴱ` images,
-- so the variable case is exactly `eternal-mor`. This is what makes
-- `restrict-sub-env` a coalgebra morphism at the head.

restrict-val-mor : ∀ {Γ A} → (et : Eternal A) → (W : Γ ⊢V⦂ A) → ∀ {ρ}
                 → eternalᵛ-extᵉ et {ρ}
                     ∘ᵐ ⟨ ρ ⟩ᶠ (⟦ eternal-val-restrict et W ⟧ᵛᵗ (eternal-val-restrictᴾ et W))
                 ≈ᵐ ⟦ eternal-val-restrict et W ⟧ᵛᵗ (eternal-val-restrictᴾ et W)
                      ∘ᵐ Eternalᵒ.extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ)
restrict-val-mor {A = A} et (var f x) with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))))
  (≈ᵐ-trans (eternal-mor et x)
            (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))
... | no ¬et' = ⊥-elim (¬et' et)
restrict-val-mor (Baseₑ b eb) (const c) =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟦⟧ᵇᶜ-eternal eb c))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ terminalᵐ-unique)
            (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique)))))))
restrict-val-mor Unitₑ ⋆ =
  ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique)
restrict-val-mor (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-extᵉ (eternalᵛ-Eternalᵒ et₁) (eternalᵛ-Eternalᵒ et₂)))
  (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
  (≈ᵐ-trans
    (⟨ ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
       (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
       (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
                 (restrict-val-mor et₁ V₁)))
     , ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
       (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
       (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
                 (restrict-val-mor et₂ V₂))) ⟩ᵐ-cong)
    (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))

eternal-val-restrict-nat {A = A} et (var f x) _ with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))
  (≈ᵐ-trans (var-projᴱ et x)
            (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))
... | no ¬et' = ⊥-elim (¬et' et)
eternal-val-restrict-nat _ (const c) _ =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
eternal-val-restrict-nat _ ⋆ _ =
  ≈ᵐ-sym terminalᵐ-unique
eternal-val-restrict-nat (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ (p₁ , p₂) =
  ≈ᵐ-trans (⟨ eternal-val-restrict-nat et₁ V₁ p₁ , eternal-val-restrict-nat et₂ V₂ p₂ ⟩ᵐ-cong)
           (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))

-- `restrict-sub-env` is a morphism of eternal objects (commutes with the
-- extractions). Recursion on the variable, mirroring `restrict-ren-mor`; the
-- head-eternal case uses `restrict-val-mor` for the substituted value.

restrict-sub-env-extᵉ : ∀ {Γ A ρ₀} → (x : A ∈[ ρ₀ ] Γ) → (W : split-l x ⊢V⦂ A) → ∀ {ρ}
                      → projᴱ-extᵉ Γ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (restrict-sub-env x W)
                      ≈ᵐ restrict-sub-env x W ∘ᵐ projᴱ-extᵉ (split-l x ++ᶜ split-r x) {ρ}
restrict-sub-env-extᵉ {Γ ∷ A} Hd W {ρ} with eternal? A
... | yes et =
  prod-ext
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ} {A} et {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
    (≈ᵐ-trans (∘ᵐ-identityʳ _)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-assoc _ _ _))))))))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ} {A} et {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (restrict-val-mor et W)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)))
              (∘ᵐ-assoc _ _ _))))))))
... | no  _  =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-sub-env-extᵉ (Tl-∷ {Γ = Γ₀} {B = B} x) W {ρ} with eternal? B
... | yes etB =
  prod-ext
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ₀} {B} etB {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (restrict-sub-env-extᵉ x W))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (projᴱ-extᵉ-fst {split-l x ++ᶜ split-r x} {B} etB {ρ})))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-assoc _ _ _)))))))))))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ₀} {B} etB {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-identityˡ _)))
    (≈ᵐ-sym (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
            (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _))
                      (×-eternalᵒ-sndᵉ {split-l x ++ᶜ split-r x} {B} etB {ρ})))))))))))
... | no  _  = restrict-sub-env-extᵉ x W
restrict-sub-env-extᵉ (Tl-⟨⟩ x) W = restrict-sub-env-extᵉ x W

-- The `necᵉ`/`Future` mate (as `restrict-ren-necᵉ` from `restrict-ren-mor`).

restrict-sub-env-necᵉ : ∀ {Γ A ρ₀} → (x : A ∈[ ρ₀ ] Γ) → (W : split-l x ⊢V⦂ A) → ∀ {ρ}
                      → [ ρ ]ᶠ (restrict-sub-env x W)
                          ∘ᵐ Eternalᵒ.necᵉ (⟦ split-l x ++ᶜ split-r x ⟧ᴱ-Eternalᵒ) {ρ}
                      ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) {ρ} ∘ᵐ restrict-sub-env x W
restrict-sub-env-necᵉ {Γ} x W {ρ} =
  ≈ᵐ-trans (∘ᵐ-congʳ (Eternalᵒ.necᵉ-mate (⟦ split-l x ++ᶜ split-r x ⟧ᴱ-Eternalᵒ)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (restrict-sub-env-extᵉ x W))))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.necᵉ-mate (⟦ Γ ⟧ᴱ-Eternalᵒ)))))))))))

-- Naturality of the eternal projection along a substitution (as `projᴱ-nat`
-- for renamings). The head-eternal case uses `eternal-val-restrict-nat`; the
-- lock case uses `restrict-sub-env-extᵉ`.

projᴱ-subst-nat : ∀ {Γ A ρ₀} → (x : A ∈[ ρ₀ ] Γ) → (W : split-l x ⊢V⦂ A)
                → (pW : Paramᵛ W)
                → projᴱ Γ ∘ᵐ sub-env x W pW
                ≈ᵐ restrict-sub-env x W ∘ᵐ projᴱ (split-l x ++ᶜ split-r x)
projᴱ-subst-nat {Γ ∷ A} Hd W pW with eternal? A
... | yes et =
  ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
  (≈ᵐ-trans (⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , eternal-val-restrict-nat et W pW ⟩ᵐ-cong)
            (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))))
projᴱ-subst-nat (Tl-∷ {B = B} x) W pW with eternal? B
... | yes _ =
  ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
  (≈ᵐ-trans (mapˣᵐ-cong (projᴱ-subst-nat x W pW) ≈ᵐ-refl)
            (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-subst-nat x W pW))
            (∘ᵐ-assoc _ _ _))))
projᴱ-subst-nat (Tl-⟨⟩ x) W pW =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (projᴱ-subst-nat x W pW)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (restrict-sub-env-extᵉ x W))
            (∘ᵐ-assoc _ _ _))))))

-- (`eq-ren-∷` / `eq-ren-⟨⟩` / `eq-ren-irr` live with the other renaming
-- denotation lemmas in `Interpretation.Renaming`.)

-- The variable that a context splitting points at.

split-var : ∀ {Γ Γ₁ Γ₂ A} → Γ₁ ∷ A , Γ₂ split Γ → A ∈[ ctx-grade Γ₂ ] Γ
split-var split-[]     = Hd
split-var (split-∷ c)  = Tl-∷ (split-var c)
split-var (split-⟨⟩ c) = Tl-⟨⟩ (split-var c)

-- Looking a variable up through the splitting of its context: the composite
-- of the grade-weakening renaming with the transport along the splitting is
-- exactly the variable's projection. Induction on the splitting witness (it
-- is what makes `wk-ren-⟨ρ⟩-ctx`'s equality argument reduce).

split-lookup-gen : ∀ {Γ Γ₁ Γ₂ A} → (c : Γ₁ ∷ A , Γ₂ split Γ)
                 → ⟨ ctx-grade Γ₂ ⟩ᶠ sndᵐ
                     ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {Γ₁ ∷ A} {Γ₂} refl ⟧ʳ
                     ∘ᵐ ⟦ eq-ren (split-≡ c) ⟧ʳ
                   ≈ᵐ var-proj (split-var c)
split-lookup-gen split-[] =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) (⟨⟩-η-nat sndᵐ)
split-lookup-gen (split-∷ {A = B} c) =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (eq-ren-∷ (split-≡ c))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (split-lookup-gen c))))))
split-lookup-gen (split-⟨⟩ {ρ = ρ} c) =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (eq-ren-⟨⟩ (split-≡ c))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-μ-nat sndᵐ))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (∘ᵐ-congʳ (⟨⟩-congᶠ (split-lookup-gen c)))))))))

-- The variable a splitting points at is the variable it came from.

subst-grade-Tl-∷ : ∀ {Γ A B ρ ρ'} → (e : ρ ≡ ρ') → (v : A ∈[ ρ ] Γ)
           → subst (A ∈[_] (Γ ∷ B)) e (Tl-∷ v) ≡ Tl-∷ (subst (A ∈[_] Γ) e v)
subst-grade-Tl-∷ refl v = refl

subst-grade-Tl-⟨⟩ : ∀ {Γ A σ ρ ρ'} → (e : ρ ≡ ρ') → (v : A ∈[ ρ ] Γ)
            → subst (A ∈[_] (Γ ⟨ σ ⟩)) (cong (_·ᵣ σ) e) (Tl-⟨⟩ v)
              ≡ Tl-⟨⟩ (subst (A ∈[_] Γ) e v)
subst-grade-Tl-⟨⟩ refl v = refl

split-var-≡ : ∀ {Γ A ρ} → (z : A ∈[ ρ ] Γ)
            → subst (A ∈[_] Γ) (split-grade-≡ z) (split-var (split-pf z)) ≡ z
split-var-≡ Hd         = refl
split-var-≡ (Tl-∷ z)   =
  trans (subst-grade-Tl-∷ (split-grade-≡ z) (split-var (split-pf z)))
        (cong Tl-∷ (split-var-≡ z))
split-var-≡ (Tl-⟨⟩ z)  =
  trans (subst-grade-Tl-⟨⟩ (split-grade-≡ z) (split-var (split-pf z)))
        (cong Tl-⟨⟩ (split-var-≡ z))

-- and hence the lookup lemma in the form the `unbox` cases need.

-- (the grade is an independent variable here, so the equality proof can be
-- matched against `refl` — it cannot be in `split-lookup` below, where the
-- grade also occurs inside `split-r z`)

split-lookup-e : ∀ {Γ Γ₁ Γ₂ A ρ} → (c : Γ₁ ∷ A , Γ₂ split Γ) → (e : ctx-grade Γ₂ ≡ ρ)
               → ⟨ ρ ⟩ᶠ sndᵐ
                   ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {Γ₁ ∷ A} {Γ₂} e ⟧ʳ
                   ∘ᵐ ⟦ eq-ren (split-≡ c) ⟧ʳ
                 ≈ᵐ var-proj (subst (A ∈[_] Γ) e (split-var c))
split-lookup-e c refl = split-lookup-gen c

split-lookup : ∀ {Γ A ρ} → (z : A ∈[ ρ ] Γ)
             → ⟨ ρ ⟩ᶠ sndᵐ
                 ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {split-l z ∷ A} {split-r z} (split-grade-≡ z) ⟧ʳ
                 ∘ᵐ ⟦ eq-ren (split-≡ (split-pf z)) ⟧ʳ
               ≈ᵐ var-proj z
split-lookup z =
  ≈ᵐ-trans (split-lookup-e (split-pf z) (split-grade-≡ z))
           (≡→≈ᵐ (cong var-proj (split-var-≡ z)))

