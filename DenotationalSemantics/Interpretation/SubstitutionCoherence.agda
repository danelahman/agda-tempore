------------------------------------------------------------------------
-- The interpretation is natural in substitutions:                      --
--   ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ≈ ⟦ M ⟧ᶜᵗ ∘ᵐ sub-env x W   (dually for values). --
--                                                                    --
-- `sub-env x W : ⟦ split-l x ++ᶜ split-r x ⟧ →ᵐ ⟦ Γ ⟧` is the semantic  --
-- counterpart of the substitution: it reconstructs the environment for   --
-- `Γ` by inserting `⟦ W ⟧` at the position of `x`. It is defined by       --
-- structural recursion on `x` (the context splitting computes on `x`,     --
-- and the context interpretation distributes over `++ᶜ`), so no           --
-- transports along context equalities are needed.                         --
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

module DenotationalSemantics.Interpretation.SubstitutionCoherence
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

-- Weakening a variable past a `∷` projects the environment (both sides of
-- the equation mention `var-morphism` at the same type, so the `eternal?`
-- split reduces them simultaneously).

var-morphism-Tl-∷ : ∀ {Γ A B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                  → var-morphism {Γ ∷ A} f (Tl-∷ y) ≈ᵐ var-morphism f y ∘ᵐ fstᵐ
var-morphism-Tl-∷ {B = B} y f with eternal? B
... | yes et = ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
... | no ¬et = ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))

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

-- Transport renamings along a context equality commute with the context
-- formers (both sides are the identity once the equality is `refl`).

eq-ren-∷ : ∀ {Γ Γ' B} → (e : Γ ≡ Γ')
         → ⟦ eq-ren (cong (_∷ B) e) ⟧ʳ ≈ᵐ mapˣᵐ ⟦ eq-ren e ⟧ʳ idᵐ
eq-ren-∷ refl = ≈ᵐ-sym mapˣᵐ-idᵐ

eq-ren-⟨⟩ : ∀ {Γ Γ' ρ} → (e : Γ ≡ Γ')
          → ⟦ eq-ren (cong (_⟨ ρ ⟩) e) ⟧ʳ ≈ᵐ ⟨ ρ ⟩ᶠ ⟦ eq-ren e ⟧ʳ
eq-ren-⟨⟩ refl = ≈ᵐ-sym ⟨⟩-idᵐ

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

subst-Tl-∷ : ∀ {Γ A B ρ ρ'} → (e : ρ ≡ ρ') → (v : A ∈[ ρ ] Γ)
           → subst (A ∈[_] (Γ ∷ B)) e (Tl-∷ v) ≡ Tl-∷ (subst (A ∈[_] Γ) e v)
subst-Tl-∷ refl v = refl

subst-Tl-⟨⟩ : ∀ {Γ A σ ρ ρ'} → (e : ρ ≡ ρ') → (v : A ∈[ ρ ] Γ)
            → subst (A ∈[_] (Γ ⟨ σ ⟩)) (cong (_·ᵣ σ) e) (Tl-⟨⟩ v)
              ≡ Tl-⟨⟩ (subst (A ∈[_] Γ) e v)
subst-Tl-⟨⟩ refl v = refl

split-var-≡ : ∀ {Γ A ρ} → (z : A ∈[ ρ ] Γ)
            → subst (A ∈[_] Γ) (split-grade-≡ z) (split-var (split-pf z)) ≡ z
split-var-≡ Hd         = refl
split-var-≡ (Tl-∷ z)   =
  trans (subst-Tl-∷ (split-grade-≡ z) (split-var (split-pf z)))
        (cong Tl-∷ (split-var-≡ z))
split-var-≡ (Tl-⟨⟩ z)  =
  trans (subst-Tl-⟨⟩ (split-grade-≡ z) (split-var (split-pf z)))
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

-- The resource lookup morphism of an `unbox`.

lk : ∀ {Γ A ρ ρ'} → [ ρ ] A ∈[ ρ' ] Γ → ρ' ≾ᵣ ρ → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
lk z rel = ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj z

-- The `unbox-var` smart constructor rebuilds an unboxing whose looked-up
-- resource is the very variable it was built from: interpreting it runs
-- `unbox⇒var` on the rebuilt renaming, and `split-lookup` shows the result
-- is again `z`'s projection.

-- projecting the head variable through one lock and relaxing the redundant
-- `uᵣ ·ᵣ ρ` back to `ρ` is just the (locked) second projection

hd-lookup : ∀ {Δ₀ B ρ} → (c : uᵣ ·ᵣ ρ ≾ᵣ ρ)
          → ⟨⟩-≤ c ∘ᵐ var-proj (Tl-⟨⟩ {Γ = Δ₀ ∷ B} {ρ = ρ} Hd) ≈ᵐ ⟨ ρ ⟩ᶠ sndᵐ
hd-lookup c =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ η sndᵐ)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ ⟨⟩-μ∘Tη≡id))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans _ c))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl))
  (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
            (∘ᵐ-identityˡ _)))))))

-- the renaming that `unbox-var` builds

unbox-var-ren : ∀ {Γ A ρ ρ'} → (z : [ ρ ] A ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ)
              → Ren ((split-l z ∷ [ ρ ] A) ⟨ ρ ⟩) Γ
unbox-var-ren z rel =
     eq-ren (split-≡ (split-pf z))
  ∘ʳ wk-ren-⟨ρ⟩-ctx (split-grade-≡ z)
  ∘ʳ ⟨⟩-≤-ren rel

-- Interpreting an unboxing whose value is the head variable: the looked-up
-- resource is the (locked) second projection, reindexed by the renaming.
-- The renaming must be a *variable* here, so that `var-rename` is stuck and
-- the `with` can abstract it.

unbox⇒var-Hd : ∀ {Γ Δ₀ A ρ} → (W : Ren ((Δ₀ ∷ [ ρ ] A) ⟨ ρ ⟩) Γ)
             → lk (proj₁ (proj₂ (unbox⇒var W (var (λ _ → ≾ᵣ-refl) Hd))))
                  (proj₂ (proj₂ (unbox⇒var W (var (λ _ → ≾ᵣ-refl) Hd))))
               ≈ᵐ ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ ⟦ W ⟧ʳ
unbox⇒var-Hd {Δ₀ = Δ₀} {A = A} {ρ = ρ} W
  with var-rename W (Tl-⟨⟩ Hd) | var-proj-nat W (Tl-⟨⟩ Hd) (λ ())
... | ρ'' , b , z'' | vpn =
  ∘ᵐ-congʳ
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans (b (λ ())) _)))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ vpn)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congˡ (hd-lookup {Δ₀ = Δ₀} {B = [ ρ ] A} {ρ = ρ} _))))))

unbox-varᴾ : ∀ {Γ A C ρ ρ'} → (z : [ ρ ] A ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ)
           → (M : Γ ∷ A ⊢C⦂ C) → Paramᶜ M → Paramᶜ (unbox-var z rel M)
unbox-varᴾ z rel M pM = tt , pM

unbox-var-nat : ∀ {Γ A C ρ ρ'} → (z : [ ρ ] A ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ)
              → (M : Γ ∷ A ⊢C⦂ C) → (pM : Paramᶜ M)
              → ⟦ unbox-var z rel M ⟧ᶜᵗ (unbox-varᴾ z rel M pM)
              ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , lk z rel ⟩ᵐ
unbox-var-nat z rel M pM =
  ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , inner ⟩ᵐ-cong)
  where
    inner : _ ≈ᵐ lk z rel
    inner =
      ≈ᵐ-trans (unbox⇒var-Hd (unbox-var-ren z rel))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-nat sndᵐ rel)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
                (∘ᵐ-congʳ (∘ᵐ-congʳ (split-lookup z)))))))

-- Given that the continuation and the resource lookup each commute with the
-- substitution, so does the whole unboxing. (This is all that is left of the
-- `unbox` case once `unbox-var-nat` has rebuilt both sides.)

unbox-step : ∀ {Γ Γ' A C} → {M' : Γ' ∷ A ⊢C⦂ C} → {M : Γ ∷ A ⊢C⦂ C}
           → {σ : ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ}
           → {lk' : ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ} → {lkᵒ : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ}
           → {pM' : Paramᶜ M'} → {pM : Paramᶜ M}
           → ⟦ M' ⟧ᶜᵗ pM' ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ mapˣᵐ σ idᵐ
           → lk' ≈ᵐ lkᵒ ∘ᵐ σ
           → ⟦ M' ⟧ᶜᵗ pM' ∘ᵐ ⟨ idᵐ , lk' ⟩ᵐ ≈ᵐ (⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , lkᵒ ⟩ᵐ) ∘ᵐ σ
unbox-step {σ = σ} {lkᵒ = lkᵒ} eM elk =
  ≈ᵐ-trans (∘ᵐ-congˡ eM)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ
              (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
               , ≈ᵐ-trans (∘ᵐ-identityˡ _) elk ⟩ᵐ-cong))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ idᵐ lkᵒ σ)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))

-- Unfoldings of `var-morphism` once eternality has been decided. (Stating
-- them as lemmas is what lets the `eternal?` split reduce `var-morphism`
-- inside a recursive call's type.)

var-morphism-et : ∀ {Γ B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                → (et : Eternal B)
                → var-morphism f y ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ var-proj y
var-morphism-et {B = B} y f et with eternal? B
... | yes et' = ∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et)
... | no ¬et' = ⊥-elim (¬et' et)

var-morphism-¬et : ∀ {Γ B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                 → (¬et : ¬ Eternal B)
                 → var-morphism f y ≈ᵐ εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj y
var-morphism-¬et {B = B} y f ¬et with eternal? B
... | yes et'  = ⊥-elim (¬et et')
... | no ¬et'' = ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))

-- Substitution in a *resource* variable: the substituted variable's
-- projection, relaxed back to the original grade, is the original variable's
-- projection reindexed by the substitution. (The exact analogue of
-- `var-proj-nat` for renamings.)

sub-rvar-nat : ∀ {Γ A B ρ σ τ}
             → (y : [ ρ ] B ∈[ σ ] Γ) → (x : A ∈[ τ ] Γ) → (W : split-l x ⊢V⦂ A)
             → (pW : Paramᵛ W)
             → ⟨⟩-≤ (proj₂ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
                 ∘ᵐ var-proj (proj₁ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
               ≈ᵐ var-proj y ∘ᵐ sub-env x W pW

sub-rvar-nat Hd Hd W pW with grad-typ⇒var W
... | σ' , v , f , refl =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-nat Hd (Tl-∷ x) W pW =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
sub-rvar-nat (Tl-∷ y) Hd W pW =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-nat (Tl-∷ y) (Tl-∷ x) W pW with ⟨ y ⟩[ x ↦ W ]rvar | sub-rvar-nat y x W pW
... | σ' , v , p | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-nat (Tl-⟨⟩ y) (Tl-⟨⟩ x) W pW with ⟨ y ⟩[ x ↦ W ]rvar | sub-rvar-nat y x W pW
... | σ' , v , p | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (μ-≤ˡ p))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ ih))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))

-- hence the resource *lookup* commutes with the substitution

sub-lk : ∀ {Γ A B ρ σ τ}
       → (y : [ ρ ] B ∈[ σ ] Γ) → (rel : σ ≾ᵣ ρ)
       → (x : A ∈[ τ ] Γ) → (W : split-l x ⊢V⦂ A) → (pW : Paramᵛ W)
       → lk (proj₁ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
            (≾ᵣ-trans (proj₂ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar)) rel)
         ≈ᵐ lk y rel ∘ᵐ sub-env x W pW
sub-lk y rel x W pW =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans _ rel))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sub-rvar-nat y x W pW)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

-- The `unbox` case of the substitution coherence, with the unboxed resource
-- variable `y`/`rel` and the continuation's induction hypothesis taken as
-- parameters (so that the clause below needs only a single `with`).

unbox-subst-nat : ∀ {Γ A B C ρ σ τ}
                → (y : [ ρ ] B ∈[ σ ] Γ) → (rel : σ ≾ᵣ ρ)
                → (M : Γ ∷ B ⊢C⦂ C) → (x : A ∈[ τ ] Γ) → (W : split-l x ⊢V⦂ A)
                → (pW : Paramᵛ W) → {pM : Paramᶜ M}
                → {pM' : Paramᶜ (M [ Tl-∷ x ↦ W ]c)}
                → ⟦ M [ Tl-∷ x ↦ W ]c ⟧ᶜᵗ pM'
                  ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ mapˣᵐ (sub-env x W pW) idᵐ
                → ⟦ unbox-var (proj₁ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
                              (≾ᵣ-trans (proj₂ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar)) rel)
                              (M [ Tl-∷ x ↦ W ]c) ⟧ᶜᵗ
                       (unbox-varᴾ (proj₁ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
                                   (≾ᵣ-trans (proj₂ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar)) rel)
                                   (M [ Tl-∷ x ↦ W ]c) pM')
                  ≈ᵐ (⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , lk y rel ⟩ᵐ) ∘ᵐ sub-env x W pW
unbox-subst-nat y rel M x W pW ih with ⟨ y ⟩[ x ↦ W ]rvar | sub-lk y rel x W pW
... | _ , v , p | slk =
  ≈ᵐ-trans (unbox-var-nat v (≾ᵣ-trans p rel) (M [ Tl-∷ x ↦ W ]c) _)
           (unbox-step {M' = M [ Tl-∷ x ↦ W ]c} {M = M} {σ = sub-env x W pW}
                       {lk' = lk v (≾ᵣ-trans p rel)} {lkᵒ = lk y rel} ih slk)

-- Substitution in a variable.

-- Substituting into a variable yields either a variable (parametric outright),
-- a weakening of the substituend, or its eternal extension.

subvarᴾ : ∀ {Γ A B ρ ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
        → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A) → Paramᵛ W
        → Paramᵛ (⟨ y , f ⟩[ x ↦ W ]var)
subvarᴾ Hd       _ Hd        W pW = pW
subvarᴾ Hd       f (Tl-∷ _)  _ pW = tt
subvarᴾ (Tl-∷ y) f Hd        _ pW = tt
subvarᴾ (Tl-∷ y) f (Tl-∷ x)  W pW =
  renᵛ wk-ren ⟨ y , f ⟩[ x ↦ W ]var (subvarᴾ y f x W pW)
subvarᴾ {B = B} (Tl-⟨⟩ y) f (Tl-⟨⟩ x) W pW with eternal? B
... | yes p  = eternal-val-extᴾ p ⟨ y , (λ z → ≾ᵣ-zero-productˡ (f (λ z₁ → z p))) ⟩[ x ↦ W ]var
... | no  ¬p = renᵛ (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬p)) ∘ʳ ⟨⟩-η⁻¹-ren)
                 ⟨ y , (λ z → ≾ᵣ-zero-productˡ (f z)) ⟩[ x ↦ W ]var
                 (subvarᴾ y (λ z → ≾ᵣ-zero-productˡ (f z)) x W pW)

sub-var-nat : ∀ {Γ A B ρ ρ'}
            → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
            → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A) → (pW : Paramᵛ W)
            → ⟦ ⟨ y , f ⟩[ x ↦ W ]var ⟧ᵛᵗ (subvarᴾ y f x W pW)
            ≈ᵐ var-morphism f y ∘ᵐ sub-env x W pW

-- the substituted variable is the one being replaced
sub-var-nat {B = B} Hd f Hd W pW with eternal? B
... | yes et =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et)) ⟨⟩-εᵘ∘η≡id))
              (∘ᵐ-identityˡ _))))))
... | no ¬et =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩-≤-irr (f ¬et) ≾ᵣ-refl) ⟨⟩-≤-refl)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id)
              (∘ᵐ-identityˡ _)))))))))

-- the variable is the head, the substitution acts deeper: the head component
-- of the environment is untouched (`sub-env (Tl-∷ x)` is `mapˣᵐ … idᵐ`)
sub-var-nat {B = B} Hd f (Tl-∷ x) W pW with eternal? B
... | yes et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))
                   (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))
... | no ¬et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))
                   (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))))

-- the variable is deeper, the substitution replaces the head: the variable's
-- projection discards the substituted component
sub-var-nat {B = B} (Tl-∷ y) f Hd W pW with eternal? B
... | yes et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
                   (∘ᵐ-congʳ (∘ᵐ-identityʳ _)))))
... | no ¬et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
                   (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityʳ _)))))))

-- both deeper: recurse, weakening the substituted value (uses `V-rename-nat`)
sub-var-nat (Tl-∷ y) f (Tl-∷ x) W pW =
  ≈ᵐ-trans (V-rename-nat wk-ren ⟨ y , f ⟩[ x ↦ W ]var (subvarᴾ y f x W pW))
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-nat y f x W pW))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (var-morphism-Tl-∷ y f)))))))

sub-var-nat {B = B} (Tl-⟨⟩ y) f (Tl-⟨⟩ x) W pW with eternal? B
... | yes et =
  ≈ᵐ-trans (eternal-val-ext-nat et ⟨ y , _ ⟩[ x ↦ W ]var _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (sub-var-nat y _ x W pW)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (var-morphism-et y _ et))))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-μ et)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
... | no ¬et =
  ≈ᵐ-trans (V-rename-nat (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren)
                         ⟨ y , _ ⟩[ x ↦ W ]var _)
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-nat y _ x W pW))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (var-morphism-¬et y _ ¬et)))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (ext-nat _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (ext-alg _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))))))))))

-- Interpreting a context-equality transport of a computation: the transport
-- becomes the corresponding equality renaming (both are the identity when the
-- equality is `refl`). Used to strip the `subst`s that `_[_↦_]c` inserts in the
-- handler clauses.

-- Retyping a clause along a context equality preserves parametricity.

substᴾᶜ : ∀ {Δ Δ' D C} → (e : Δ ≡ Δ') → (t : Δ ++ᶜ D ⊢C⦂ C)
        → Paramᶜ t → Paramᶜ (subst (λ Γ₀ → Γ₀ ++ᶜ D ⊢C⦂ C) e t)
substᴾᶜ refl t p = p

substᴾᶜ′ : ∀ {Δ Δ' C} → {e : Δ ≡ Δ'} → (t : Δ ⊢C⦂ C)
         → Paramᶜ t → Paramᶜ (subst (_⊢C⦂ C) e t)
substᴾᶜ′ {e = refl} t p = p

substᴾᵛ : ∀ {Δ Δ' A} → {e : Δ ≡ Δ'} → (t : Δ ⊢V⦂ A)
        → Paramᵛ t → Paramᵛ (subst (_⊢V⦂ A) e t)
substᴾᵛ {e = refl} t p = p

subst-ctx-interp : ∀ {Δ Δ' C} → (e : Δ ≡ Δ') → (t : Δ ⊢C⦂ C) → (p : Paramᶜ t)
                 → ⟦ subst (_⊢C⦂ C) e t ⟧ᶜᵗ (substᴾᶜ′ {e = e} t p)
                 ≈ᵐ ⟦ t ⟧ᶜᵗ p ∘ᵐ ⟦ eq-ren e ⟧ʳ
subst-ctx-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

subst-clause-interp : ∀ {Δ Δ' D C} → (e : Δ ≡ Δ') → (t : Δ ++ᶜ D ⊢C⦂ C)
                    → (p : Paramᶜ t)
                    → ⟦ subst (λ Γ₀ → Γ₀ ++ᶜ D ⊢C⦂ C) e t ⟧ᶜᵗ (substᴾᶜ e t p)
                    ≈ᵐ ⟦ t ⟧ᶜᵗ p ∘ᵐ ⟦ eq-ren (cong (_++ᶜ D) e) ⟧ʳ
subst-clause-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

-- The interpretation of an equality renaming depends only on the endpoints of
-- the context equality (UIP), so any two proofs give the same transport.

eq-ren-irr : ∀ {Γ Γ'} → (e e' : Γ ≡ Γ') → ⟦ eq-ren e ⟧ʳ ≈ᵐ ⟦ eq-ren e' ⟧ʳ
eq-ren-irr e e' = ≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (uip {p = e} {q = e'}))

-- Context extension is injective, so an equality between two contexts sharing
-- their last two entries restricts to their ambient parts.

ctx-∷-inj : ∀ {Δ Δ' A} → Δ ∷ A ≡ Δ' ∷ A → Δ ≡ Δ'
ctx-∷-inj refl = refl

-- Hence such a retyping is a nested product reindexing whose inner component
-- depends only on the ambient parts — in particular not on the residual grade
-- carried by the last entry.

eq-ren-∷∷ : ∀ {Δ Δ' pt kt} → (e : (Δ ∷ pt) ∷ kt ≡ (Δ' ∷ pt) ∷ kt)
          → ⟦ eq-ren e ⟧ʳ
          ≈ᵐ mapˣᵐ (mapˣᵐ ⟦ eq-ren (ctx-∷-inj (ctx-∷-inj e)) ⟧ʳ idᵐ) idᵐ
eq-ren-∷∷ {pt = pt} {kt = kt} e =
  ≈ᵐ-trans (eq-ren-irr e (cong (_∷ kt) (cong (_∷ pt) (ctx-∷-inj (ctx-∷-inj e)))))
  (≈ᵐ-trans (eq-ren-∷ (cong (_∷ pt) (ctx-∷-inj (ctx-∷-inj e))))
            (mapˣᵐ-cong (eq-ren-∷ (ctx-∷-inj (ctx-∷-inj e))) ≈ᵐ-refl))

-- A clause-context retyping is a nested product reindexing, and in particular
-- acts only on the ambient part — it is independent of the residual grade the
-- continuation slot carries.

eq-ren-clause : ∀ {Δ Δ'} → (e : Δ ≡ Δ') → (Γ' : Ctx) → (pt kt : VType)
              → ⟦ eq-ren (cong (_++ᶜ (Γ' ∷ pt ∷ kt)) e) ⟧ʳ
              ≈ᵐ mapˣᵐ (mapˣᵐ ⟦ eq-ren (cong (_++ᶜ Γ') e) ⟧ʳ idᵐ) idᵐ
eq-ren-clause e Γ' pt kt =
  ≈ᵐ-trans (eq-ren-irr (cong (_++ᶜ (Γ' ∷ pt ∷ kt)) e)
                       (cong (_∷ kt) (cong (_∷ pt) (cong (_++ᶜ Γ') e))))
  (≈ᵐ-trans (eq-ren-∷ (cong (_∷ pt) (cong (_++ᶜ Γ') e)))
            (mapˣᵐ-cong (eq-ren-∷ (cong (_++ᶜ Γ') e)) ≈ᵐ-refl))


-- Retyping a clause family's ambient context preserves the clauses' uniformity
-- in the residual grade: the retyping acts on the ambient context only, so it
-- commutes with the continuation's coercion (`mapˣ-swapᵐ`), after which the
-- original uniformity applies.

subst-clauses-uniform :
  ∀ {Δ Δ' B} → (e : Δ ≡ Δ')
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Δ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
  → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'') → (Γ' : Ctx)
       → ⟦ H op ε₂'' Γ' ⟧ᶜᵗ (pH op ε₂'' Γ')
           ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
       ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' Γ' ⟧ᶜᵗ (pH op ε₁'' Γ'))
  → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'') → (Γ' : Ctx)
       → ⟦ subst (λ Γ₀ → Γ₀ ++ᶜ Γ' ∷ type-of-gtype (param op)
                            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₂'')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε₂''))
                 e (H op ε₂'' Γ') ⟧ᶜᵗ (substᴾᶜ e (H op ε₂'' Γ') (pH op ε₂'' Γ'))
           ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
       ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q)
           ∘ᵐ ⟦ subst (λ Γ₀ → Γ₀ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₁'')
                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₁''))
                      e (H op ε₁'' Γ') ⟧ᶜᵗ (substᴾᶜ e (H op ε₁'' Γ') (pH op ε₁'' Γ')))
subst-clauses-uniform e H pH uH op q Γ' =
  ≈ᵐ-trans (∘ᵐ-congˡ (subst-clause-interp e (H op _ Γ') (pH op _ Γ')))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ
    (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-clause e Γ' _ _))
    (≈ᵐ-trans (mapˣ-swapᵐ _ _)
              (∘ᵐ-congʳ (≈ᵐ-sym (eq-ren-clause e Γ' _ _))))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (uH op q Γ'))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (subst-clause-interp e (H op _ Γ') (pH op _ Γ')))))))))

-- Parametricity-in-`Γ'` transports across a non-eternal retyping (base equality
-- `e : Γ ᴱ ≡ Γ₀ ᴱ`): the retyping reindexes the eternal base by `eq-ren`, and
-- `⋉ᴰ-eq` (fed `Eternalᵒ-coh` to relate the two bases' eternal structures)
-- commutes it past the lift. Mirrors `subst-clauses-uniform`, with
-- `mapˣ²-comm (⋉ᴰ-eq …)` in place of `mapˣ-swapᵐ`.
subst-clauses-ctxparam :
  ∀ {Γ Γ₀ B} → (e : Γ ᴱ ≡ Γ₀ ᴱ)
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
  → CtxParamʰ {Γ} H pH
  → CtxParamʰ {Γ₀}
      (λ op ε'' Γ' → subst (λ Γ₁ → Γ₁ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                                   ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                           e (H op ε'' Γ'))
      (λ op ε'' Γ' → substᴾᶜ e (H op ε'' Γ') (pH op ε'' Γ'))
subst-clauses-ctxparam {Γ} {Γ₀} e H pH cH op ε'' {Γ'a} {Γ'b} ρ =
  ≈ᵐ-trans (∘ᵐ-congˡ (subst-clause-interp e (H op ε'' Γ'b) (pH op ε'' Γ'b)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ
    (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-clause e Γ'b _ _))
    (≈ᵐ-trans (mapˣ²-comm (⋉ᴰ-eq (Γ ᴱ) (Γ₀ ᴱ) (⟦ Γ ⟧ᴱ-Eternalᵒ) (⟦ Γ₀ ⟧ᴱ-Eternalᵒ)
                            e (Eternalᵒ-coh e) Γ'a Γ'b ρ))
              (∘ᵐ-congʳ (≈ᵐ-sym (eq-ren-clause e Γ'a _ _))))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (cH op ε'' {Γ'a} {Γ'b} ρ))
            (≈ᵐ-sym (subst-clause-interp e (H op ε'' Γ'a) (pH op ε'' Γ'a)))))))

-- When the substituted variable is not eternal, `restrict-sub-env` is the pure
-- reindexing transport of the (equal) eternal skeletons. Induction on the
-- variable, mirroring `restrict-sub-env`'s `with`-structure; the head is the
-- identity and each `∷`/`⟨⟩` step is `eq-ren-∷`/`eq-ren-irr` bookkeeping.

restrict-transport : ∀ {Γ A ρ} → (¬et : ¬ Eternal A) → (x : A ∈[ ρ ] Γ)
                   → (W : split-l x ⊢V⦂ A) → (e : Γ ᴱ ≡ (split-l x ++ᶜ split-r x) ᴱ)
                   → restrict-sub-env x W ≈ᵐ ⟦ eq-ren e ⟧ʳ
restrict-transport {A = A} ¬et Hd W e with eternal? A
... | yes et = ⊥-elim (¬et et)
... | no  _  = ≈ᵐ-sym (eq-ren-irr e refl)
restrict-transport ¬et (Tl-∷ {Γ = Γ₀} {B = B} x) W e with eternal? B
... | yes _ =
  ≈ᵐ-trans (mapˣᵐ-cong (restrict-transport ¬et x W (ᴱ-drop-split ¬et x)) ≈ᵐ-refl)
  (≈ᵐ-trans (≈ᵐ-sym (eq-ren-∷ (ᴱ-drop-split ¬et x)))
            (eq-ren-irr (cong (_∷ B) (ᴱ-drop-split ¬et x)) e))
... | no  _ = restrict-transport ¬et x W e
restrict-transport ¬et (Tl-⟨⟩ x) W e = restrict-transport ¬et x W e

-- The canonical eternal-skeleton transport for an eternal variable: it
-- reconciles the split point of `∈-ᴱ-split` (via `split→∈-split-l`/`-r`) with
-- the eternal restrictions of the two halves.

canon-e : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
        → split-l (split→∈ (∈-ᴱ-split et x)) ++ᶜ split-r (split→∈ (∈-ᴱ-split et x))
          ≡ (split-l x ++ᶜ split-r x) ᴱ
canon-e et x =
  trans (cong₂ _++ᶜ_ (split→∈-split-l (∈-ᴱ-split et x)) (split→∈-split-r (∈-ᴱ-split et x)))
        (sym (ᴱ-++ᶜ (split-l x) (split-r x)))

-- When the substituted variable *is* eternal, its restricted value is placed
-- (via `sub-env` at the split point of `∈-ᴱ-split`) exactly where
-- `restrict-sub-env` inserts it, once the eternal-skeleton transport is
-- accounted for. Induction on the variable; the head uses `eternal-irrelevant`
-- to reconcile the two `Eternal` witnesses.

eternal-bridge-core : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
                    → (W : split-l x ⊢V⦂ A)
                    → (e : split-l (split→∈ (∈-ᴱ-split et x)) ++ᶜ split-r (split→∈ (∈-ᴱ-split et x))
                           ≡ (split-l x ++ᶜ split-r x) ᴱ)
                    → sub-env (split→∈ (∈-ᴱ-split et x))
                        (subst (_⊢V⦂ A) (sym (split→∈-split-l (∈-ᴱ-split et x)))
                          (eternal-val-restrict et W))
                        (substᴾᵛ {e = sym (split→∈-split-l (∈-ᴱ-split et x))}
                                 (eternal-val-restrict et W)
                                 (eternal-val-restrictᴾ et W))
                        ∘ᵐ ⟦ eq-ren e ⟧ʳ
                      ≈ᵐ restrict-sub-env x W
eternal-bridge-core {A = A} et Hd W e with eternal? A
... | yes p =
  ≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-irr e refl))
  (≈ᵐ-trans (∘ᵐ-identityʳ _)
            (⟨ ≈ᵐ-refl
             , ≡→≈ᵐ (cong (λ q → ⟦ eternal-val-restrict q W ⟧ᵛᵗ
                                    (eternal-val-restrictᴾ q W))
                          (eternal-irrelevant et p)) ⟩ᵐ-cong))
... | no ¬et = ⊥-elim (¬et et)
eternal-bridge-core et (Tl-∷ {B = B} x) W e with eternal? B
... | yes _ =
  ≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-irr e (cong (_∷ B) (canon-e et x))))
  (≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-∷ (canon-e et x)))
  (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (eternal-bridge-core et x W (canon-e et x)) (∘ᵐ-identityˡ _))))
... | no _ = eternal-bridge-core et x W e
eternal-bridge-core et (Tl-⟨⟩ x) W e = eternal-bridge-core et x W e

mutual

  subᵛ : ∀ {Γ A B ρ} → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
       → Paramᵛ V → Paramᵛ W → Paramᵛ (V [ x ↦ W ]v)
  subᵛ (var f y)   x W _         pW = subvarᴾ y f x W pW
  subᵛ (const c)   x W _         pW = tt
  subᵛ ⋆           x W _         pW = tt
  subᵛ ⦉ V₁ , V₂ ⦊ x W (p₁ , p₂) pW = subᵛ V₁ x W p₁ pW , subᵛ V₂ x W p₂ pW
  subᵛ (lam M)     x W pM        pW = subᶜ M (Tl-∷ x) W pM pW

  subᶜ : ∀ {Γ A C ρ} → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
       → Paramᶜ M → Paramᵛ W → Paramᶜ (M [ x ↦ W ]c)
  subᶜ (return V)       x W pV        pW = subᵛ V x W pV pW
  subᶜ (M ⨟ N)          x W (pM , pN) pW =
    subᶜ M x W pM pW , subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW
  subᶜ (V₁ · V₂)        x W (p₁ , p₂) pW = subᵛ V₁ x W p₁ pW , subᵛ V₂ x W p₂ pW
  subᶜ (match V `in N)  x W (pV , pN) pW =
    subᵛ V x W pV pW , subᶜ N (Tl-∷ (Tl-∷ x)) W pN pW
  subᶜ (absurd V)       x W pV        pW = subᵛ V x W pV pW
  subᶜ (perform op V M) x W (pV , pM) pW =
    subᵛ V x W pV pW , subᶜ M (Tl-∷ (Tl-⟨⟩ x)) W pM pW
  subᶜ (delay τ M)      x W pM        pW = subᶜ M (Tl-⟨⟩ x) W pM pW
  subᶜ (unbox w V M)    x W (pV , pM) pW = tt , subᶜ M (Tl-∷ x) W pM pW
  subᶜ (box V N)        x W (pV , pN) pW =
    subᵛ V (Tl-⟨⟩ x) W pV pW , subᶜ N (Tl-∷ x) W pN pW
  subᶜ (coerce rel M)   x W pM        pW = subᶜ M x W pM pW
  subᶜ {A = A} (handle_`with_`in {B = B} M H N) x W (pM , pN , pH , uH , cH) pW
    with eternal? A
  ... | no ¬et =
      subᶜ M x W pM pW
    , subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW
    , (λ op ε'' Γ' → substᴾᶜ (ᴱ-drop-split ¬et x) (H op ε'' Γ') (pH op ε'' Γ'))
    , subst-clauses-uniform (ᴱ-drop-split ¬et x) H pH uH
    , subst-clauses-ctxparam (ᴱ-drop-split ¬et x) H pH cH
  ... | yes et =
      subᶜ M x W pM pW
    , subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW
    -- The clause retyping is spelled out exactly as in `_[_↦_]c`, so that
    -- `substᴾᶜ′`'s equality is solved rather than left to inversion.
    , (λ op ε'' Γ' →
         let D = Γ' ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
             s = split-++ʳ (∈-ᴱ-split et x) D
             Wv = subst (_⊢V⦂ A) (sym (split→∈-split-l s)) (eternal-val-restrict et W)
             e = trans (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
                   (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D))
                          (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
         in substᴾᶜ′ {e = e} ((H op ε'' Γ') [ split→∈ s ↦ Wv ]c)
              (subᶜ (H op ε'' Γ') (split→∈ s) Wv (pH op ε'' Γ')
                 (substᴾᵛ {e = sym (split→∈-split-l s)}
                    (eternal-val-restrict et W) (eternal-val-restrictᴾ et W))))
    , (λ op {ε₁''} {ε₂''} q Γ' →
         let D₁ = Γ' ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₁'')
             D₂ = Γ' ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₂'')
             s₁ = split-++ʳ (∈-ᴱ-split et x) D₁
             s₂ = split-++ʳ (∈-ᴱ-split et x) D₂
             Wv₁ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₁)) (eternal-val-restrict et W)
             Wv₂ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₂)) (eternal-val-restrict et W)
             pWv₁ = substᴾᵛ {e = sym (split→∈-split-l s₁)}
                      (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
             pWv₂ = substᴾᵛ {e = sym (split→∈-split-l s₂)}
                      (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
             e₁ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₁) (split→∈-split-r s₁))
                    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₁))
                           (cong (_++ᶜ D₁) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
             e₂ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂))
                    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₂))
                           (cong (_++ᶜ D₂) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
         in
          ≈ᵐ-trans (∘ᵐ-congˡ (subst-ctx-interp e₂ ((H op ε₂'' Γ') [ split→∈ s₂ ↦ Wv₂ ]c)
                                (subᶜ (H op ε₂'' Γ') (split→∈ s₂) Wv₂ (pH op ε₂'' Γ') pWv₂)))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (C-subst-nat (H op ε₂'' Γ') (split→∈ s₂) Wv₂ (pH op ε₂'' Γ') pWv₂)))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-∷∷ e₂)) (≈ᵐ-trans (mapˣ-swapᵐ _ _) (∘ᵐ-congʳ (≈ᵐ-trans (mapˣᵐ-cong (mapˣᵐ-cong (eq-ren-irr (ctx-∷-inj (ctx-∷-inj e₂)) (ctx-∷-inj (ctx-∷-inj e₁))) ≈ᵐ-refl) ≈ᵐ-refl) (≈ᵐ-sym (eq-ren-∷∷ e₁))))))) (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (mapˣ-swapᵐ _ _)) (∘ᵐ-assoc _ _ _))))))
          (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          (≈ᵐ-trans (∘ᵐ-congˡ (uH op q Γ'))
          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          ((∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat (H op ε₁'' Γ') (split→∈ s₁) Wv₁ (pH op ε₁'' Γ') pWv₁))) (≈ᵐ-sym (subst-ctx-interp e₁ ((H op ε₁'' Γ') [ split→∈ s₁ ↦ Wv₁ ]c) (subᶜ (H op ε₁'' Γ') (split→∈ s₁) Wv₁ (pH op ε₁'' Γ') pWv₁)))))))))))))))

  V-subst-nat : ∀ {Γ A B ρ} → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → (pV : Paramᵛ V) → (pW : Paramᵛ W)
              → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ (subᵛ V x W pV pW)
              ≈ᵐ ⟦ V ⟧ᵛᵗ pV ∘ᵐ sub-env x W pW
  V-subst-nat (var f y) x W _ pW = sub-var-nat y f x W pW
  V-subst-nat (const c) x W _ pW =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-subst-nat ⋆ x W _ pW = ≈ᵐ-sym terminalᵐ-unique
  V-subst-nat ⦉ V₁ , V₂ ⦊ x W (p₁ , p₂) pW =
    ≈ᵐ-trans (⟨ V-subst-nat V₁ x W p₁ pW , V-subst-nat V₂ x W p₂ pW ⟩ᵐ-cong)
             (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  V-subst-nat (lam M) x W pM pW =
    ≈ᵐ-trans (curryᵐ-cong (C-subst-nat M (Tl-∷ x) W pM pW))
             (curryᵐ-nat (sub-env x W pW) (⟦ M ⟧ᶜᵗ pM))

  C-subst-nat : ∀ {Γ A C ρ} → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → (pM : Paramᶜ M) → (pW : Paramᵛ W)
              → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ (subᶜ M x W pM pW)
              ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ sub-env x W pW
  C-subst-nat (return V) x W pV pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (M ⨟ N) x W (pM , pN) pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W pN pW))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat (sub-env x W pW)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W pM pW) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-subst-nat (V₁ · V₂) x W (p₁ , p₂) pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-subst-nat V₁ x W p₁ pW , V-subst-nat V₂ x W p₂ pW ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (match V `in N) x W (pV , pN) pW =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ (Tl-∷ x)) W pN pW))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
                   (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                    , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
  C-subst-nat (absurd V) x W pV pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (perform op V M) x W (pV , pM) pW =
    ≈ᵐ-trans (∘ᵐ-congʳ
      (⟨ ≈ᵐ-trans (substᶜ-≈ (ty-gty (param op)) (V-subst-nat V x W pV pW))
                  (≡→≈ᵐ (sym (substᶜ-∘ (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV) (sub-env x W pW))))
       , ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                    (≈ᵐ-trans (substᵈ-≈ (ty-gty (arity op))
                                (C-subst-nat M (Tl-∷ (Tl-⟨⟩ x)) W pM pW))
                              (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)
                                           (⟨ mapᵉ (op-grade op) ⟩ᶠ (sub-env x W pW)))))))))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-nat _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W pW)))
                   (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (delay τ M) x W pM pW =
    ≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (sub-env x W pW)))))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
                (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (C-subst-nat M (Tl-⟨⟩ x) W pM pW))))))))))
  -- The handle case mirrors `C-rename-nat`'s: the environment-threading second
  -- component commutes as for `⨟` (`seq-nat`), and the handler algebra is
  -- reindexed by `restrict-sub-env x W` (`alg-nat`, via `T-alg-of-handlerᵀ`'s
  -- congruence and naturality-in-P). The substitution splits on whether the
  -- variable is eternal; the two branches differ only in `⟦H'⟧ʰᵗ-nat`, which
  -- relates the substituted clause to the original reindexed clause — a pure
  -- reindexing transport when non-eternal (`restrict-transport`), and the
  -- restricted value placed at the split point when eternal (`eternal-bridge`).
  C-subst-nat {Γ = Γ} {A = A} (handle_`with_`in {A = Aₘ} {B = Bₘ} {ε} {ε'} M H N) x W
              (pM , pN , pH , uH) pW
    with eternal? A
  ... | no ¬et =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-subst-nat x W pW) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
    where
      Γ₀ : Ctx
      Γ₀ = split-l x ++ᶜ split-r x
      H' : (op : Op) → (ε'' : E) → (Γ' : Ctx)
         → Γ₀ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
            ⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε'')
      H' op ε'' Γ' =
        subst (λ Γ₁ → Γ₁ ++ᶜ Γ' ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
                       ⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε''))
              (ᴱ-drop-split ¬et x) (H op ε'' Γ')
      seq-nat : Tᶠ (⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ (subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW))
                  ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ (subᶜ M x W pM pW) ⟩ᵐ
              ≈ᵐ (Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ) ∘ᵐ sub-env x W pW
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W pN pW)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat (sub-env x W pW)
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W pM pW) ⟩ᵐ-cong)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
      adapt-commute : ∀ {D D' P Q R S} → (g : D →ᵐ D') → (p : Q →ᵐ P) → (a : S →ᵐ R)
                    → mapˣᵐ (mapˣᵐ g idᵐ) idᵐ ∘ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D}) p) a ∘ᵐ ×ᵐ-assoc⁻¹)
                    ≈ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D'}) p) a ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ mapˣᵐ g idᵐ
      adapt-commute g p a =
        ≈ᵐ-trans (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ab≈canon))
        (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (≈ᵐ-trans (∘ᵐ-congʳ (×ᵐ-assoc⁻¹-natˡ g))
                (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                          (∘ᵐ-congˡ ba≈canon)))))
        where
          ab≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _)))
                        (∘ᵐ-identityˡ _))
          ba≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _)))
                        (∘ᵐ-identityʳ _))
      pH' : ∀ op ε'' Γ' → Paramᶜ (H' op ε'' Γ')
      pH' op ε'' Γ' = substᴾᶜ (ᴱ-drop-split ¬et x) (H op ε'' Γ') (pH op ε'' Γ')
      step1 : ∀ op ε''
            → ⟦ H' op ε'' [] ⟧ᶜᵗ (pH' op ε'' [])
            ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' [])
                 ∘ᵐ mapˣᵐ (mapˣᵐ (restrict-sub-env x W) idᵐ) idᵐ
      step1 op ε'' =
        ≈ᵐ-trans (subst-clause-interp (ᴱ-drop-split ¬et x) (H op ε'' [])
                    (pH op ε'' []))
                 (∘ᵐ-congʳ ⟦eqren⟧≈)
        where
          ptᵥ = type-of-gtype (param op)
          ktᵥ = [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
          D₀ = [] ∷ ptᵥ ∷ ktᵥ
          ⟦eqren⟧≈ =
            ≈ᵐ-trans (eq-ren-irr (cong (_++ᶜ D₀) (ᴱ-drop-split ¬et x))
                                 (cong (_∷ ktᵥ) (cong (_∷ ptᵥ) (ᴱ-drop-split ¬et x))))
            (≈ᵐ-trans (eq-ren-∷ (cong (_∷ ptᵥ) (ᴱ-drop-split ¬et x)))
                      (mapˣᵐ-cong
                        (≈ᵐ-trans (eq-ren-∷ (ᴱ-drop-split ¬et x))
                                  (mapˣᵐ-cong
                                    (≈ᵐ-sym (restrict-transport ¬et x W (ᴱ-drop-split ¬et x)))
                                    ≈ᵐ-refl))
                        ≈ᵐ-refl))
      uH' : ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'') → (Γ' : Ctx)
          → ⟦ H' op ε₂'' Γ' ⟧ᶜᵗ (pH' op ε₂'' Γ')
              ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
          ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H' op ε₁'' Γ' ⟧ᶜᵗ (pH' op ε₁'' Γ')
      uH' = subst-clauses-uniform (ᴱ-drop-split ¬et x) H pH uH
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → clauseᵀ (⟦_⟧ʰᵗ {Γ₀} H' pH' uH') op ε''
                 ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε''
                      ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (step1 op ε''))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat = T-alg-of-handlerᵀ-natᴾ ((⟦ Γ ⟧ᴱ-Eternalᵒ)) ((⟦ Γ₀ ⟧ᴱ-Eternalᵒ))
                  (restrict-sub-env x W) (restrict-sub-env-necᵉ x W)
                  (⟦_⟧ʰᵗ {Γ} H pH uH) _ ⟦H'⟧ʰᵗ-nat
  ... | yes et =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-subst-nat x W pW) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
    where
      Γ₀ : Ctx
      Γ₀ = split-l x ++ᶜ split-r x
      H' : (op : Op) → (ε'' : E) → (Γ' : Ctx)
         → Γ₀ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
            ⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε'')
      H' op ε'' Γ' =
        subst (_⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε''))
          (trans (cong₂ _++ᶜ_ (split→∈-split-l (split-++ʳ (∈-ᴱ-split et x) (Γ' ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε''))))
                              (split→∈-split-r (split-++ʳ (∈-ᴱ-split et x) (Γ' ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))))
            (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) (Γ' ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε''))))
                   (cong (_++ᶜ (Γ' ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))
                         (sym (ᴱ-++ᶜ (split-l x) (split-r x))))))
          ((H op ε'' Γ') [ split→∈ (split-++ʳ (∈-ᴱ-split et x) (Γ' ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))
                         ↦ subst (_⊢V⦂ A)
                             (sym (split→∈-split-l (split-++ʳ (∈-ᴱ-split et x) (Γ' ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))))
                             (eternal-val-restrict et W) ]c)
      seq-nat : Tᶠ (⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ (subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW))
                  ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ (subᶜ M x W pM pW) ⟩ᵐ
              ≈ᵐ (Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ) ∘ᵐ sub-env x W pW
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W pN pW)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat (sub-env x W pW)
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W pM pW) ⟩ᵐ-cong)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
      adapt-commute : ∀ {D D' P Q R S} → (g : D →ᵐ D') → (p : Q →ᵐ P) → (a : S →ᵐ R)
                    → mapˣᵐ (mapˣᵐ g idᵐ) idᵐ ∘ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D}) p) a ∘ᵐ ×ᵐ-assoc⁻¹)
                    ≈ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D'}) p) a ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ mapˣᵐ g idᵐ
      adapt-commute g p a =
        ≈ᵐ-trans (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ab≈canon))
        (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (≈ᵐ-trans (∘ᵐ-congʳ (×ᵐ-assoc⁻¹-natˡ g))
                (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                          (∘ᵐ-congˡ ba≈canon)))))
        where
          ab≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _)))
                        (∘ᵐ-identityˡ _))
          ba≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _)))
                        (∘ᵐ-identityʳ _))
      pH' : ∀ op ε'' Γ' → Paramᶜ (H' op ε'' Γ')
      pH' op ε'' Γ' =
        let D = Γ' ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
            sp = split-++ʳ (∈-ᴱ-split et x) D
            Wv = subst (_⊢V⦂ A) (sym (split→∈-split-l sp)) (eternal-val-restrict et W)
            e = trans (cong₂ _++ᶜ_ (split→∈-split-l sp) (split→∈-split-r sp))
                  (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D))
                         (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
        in substᴾᶜ′ {e = e} ((H op ε'' Γ') [ split→∈ sp ↦ Wv ]c)
             (subᶜ (H op ε'' Γ') (split→∈ sp) Wv (pH op ε'' Γ')
                (substᴾᵛ {e = sym (split→∈-split-l sp)}
                   (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)))
      step1 : ∀ op ε''
            → ⟦ H' op ε'' [] ⟧ᶜᵗ (pH' op ε'' [])
            ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' [])
                 ∘ᵐ mapˣᵐ (mapˣᵐ (restrict-sub-env x W) idᵐ) idᵐ
      step1 op ε'' =
        ≈ᵐ-trans (subst-ctx-interp ctxEq body _)
        (≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat (H op ε'' []) (split→∈ s₀) Wᴱ₀
                               (pH op ε'' []) _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (∘ᵐ-congʳ
          (≈ᵐ-trans (∘ᵐ-congʳ ⟦ctxEq⟧≈)
          (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                    (mapˣᵐ-cong
                      (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                (mapˣᵐ-cong (eternal-bridge-core et x W (canon-e et x)) (∘ᵐ-identityˡ _)))
                      (∘ᵐ-identityˡ _)))))))
        where
          ptᵥ = type-of-gtype (param op)
          ktᵥ = [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
          D₀ = [] ∷ ptᵥ ∷ ktᵥ
          s₀ = split-++ʳ (∈-ᴱ-split et x) D₀
          Wᴱ₀ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₀)) (eternal-val-restrict et W)
          body = (H op ε'' []) [ split→∈ s₀ ↦ Wᴱ₀ ]c
          ctxEq = trans (cong₂ _++ᶜ_ (split→∈-split-l s₀) (split→∈-split-r s₀))
                    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₀))
                           (cong (_++ᶜ D₀) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
          ⟦ctxEq⟧≈ =
            ≈ᵐ-trans (eq-ren-irr ctxEq (cong (_∷ ktᵥ) (cong (_∷ ptᵥ) (canon-e et x))))
            (≈ᵐ-trans (eq-ren-∷ (cong (_∷ ptᵥ) (canon-e et x)))
                      (mapˣᵐ-cong (eq-ren-∷ (canon-e et x)) ≈ᵐ-refl))
      uH' : ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'') → (Γ' : Ctx)
          → ⟦ H' op ε₂'' Γ' ⟧ᶜᵗ (pH' op ε₂'' Γ')
              ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
          ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H' op ε₁'' Γ' ⟧ᶜᵗ (pH' op ε₁'' Γ')
      uH' op {ε₁''} {ε₂''} q Γ' =
        let D₁ = Γ' ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε₁'')
            D₂ = Γ' ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε₂'')
            s₁ = split-++ʳ (∈-ᴱ-split et x) D₁
            s₂ = split-++ʳ (∈-ᴱ-split et x) D₂
            Wv₁ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₁)) (eternal-val-restrict et W)
            Wv₂ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₂)) (eternal-val-restrict et W)
            pWv₁ = substᴾᵛ {e = sym (split→∈-split-l s₁)}
                     (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
            pWv₂ = substᴾᵛ {e = sym (split→∈-split-l s₂)}
                     (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
            e₁ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₁) (split→∈-split-r s₁))
                   (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₁))
                          (cong (_++ᶜ D₁) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
            e₂ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂))
                   (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₂))
                          (cong (_++ᶜ D₂) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
        in
         ≈ᵐ-trans (∘ᵐ-congˡ (subst-ctx-interp e₂ ((H op ε₂'' Γ') [ split→∈ s₂ ↦ Wv₂ ]c)
                               (subᶜ (H op ε₂'' Γ') (split→∈ s₂) Wv₂ (pH op ε₂'' Γ') pWv₂)))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (C-subst-nat (H op ε₂'' Γ') (split→∈ s₂) Wv₂ (pH op ε₂'' Γ') pWv₂)))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-∷∷ e₂)) (≈ᵐ-trans (mapˣ-swapᵐ _ _) (∘ᵐ-congʳ (≈ᵐ-trans (mapˣᵐ-cong (mapˣᵐ-cong (eq-ren-irr (ctx-∷-inj (ctx-∷-inj e₂)) (ctx-∷-inj (ctx-∷-inj e₁))) ≈ᵐ-refl) ≈ᵐ-refl) (≈ᵐ-sym (eq-ren-∷∷ e₁))))))) (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (mapˣ-swapᵐ _ _)) (∘ᵐ-assoc _ _ _))))))
         (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congˡ (uH op q Γ'))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         ((∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat (H op ε₁'' Γ') (split→∈ s₁) Wv₁ (pH op ε₁'' Γ') pWv₁))) (≈ᵐ-sym (subst-ctx-interp e₁ ((H op ε₁'' Γ') [ split→∈ s₁ ↦ Wv₁ ]c) (subᶜ (H op ε₁'' Γ') (split→∈ s₁) Wv₁ (pH op ε₁'' Γ') pWv₁))))))))))))))
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → clauseᵀ (⟦_⟧ʰᵗ {Γ₀} H' pH' uH') op ε''
                 ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε''
                      ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (step1 op ε''))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat = T-alg-of-handlerᵀ-natᴾ ((⟦ Γ ⟧ᴱ-Eternalᵒ)) ((⟦ Γ₀ ⟧ᴱ-Eternalᵒ))
                  (restrict-sub-env x W) (restrict-sub-env-necᵉ x W)
                  (⟦_⟧ʰᵗ {Γ} H pH uH) _ ⟦H'⟧ʰᵗ-nat
  -- The substitution rebuilds the unboxing with `unbox-var`, so `unbox-var-nat`
  -- turns it back into a lookup; `unbox-step` then splits the goal into the
  -- continuation (the IH) and the lookup (`sub-lk`).
  C-subst-nat (unbox w V M) x W (pV , pM) pW
    with grad-typ⇒var V | var-rename w (Tl-⟨⟩ (proj₁ (proj₂ (grad-typ⇒var V))))
  ... | _ , yv , f , refl | _ , b , y =
    unbox-subst-nat y
      (≾ᵣ-trans (b (λ ())) (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (f (λ ()))) (≾ᵣ-reflexive (·ᵣ-identityˡ _))))
      M x W pW (C-subst-nat M (Tl-∷ x) W pM pW)
  C-subst-nat (box V N) x W (pV , pN) pW =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ x) W pN pW))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (V-subst-nat V (Tl-⟨⟩ x) W pV pW)))
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
                   (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W pW)))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-subst-nat (coerce rel M) x W pM pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-subst-nat M x W pM pW)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
