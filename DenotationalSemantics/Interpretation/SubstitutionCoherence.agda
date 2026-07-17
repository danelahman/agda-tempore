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
         (Mon : Monad S Cat Fut GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
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
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ; eternalᵒ-boxCoalg)
open import DenotationalSemantics.Model.Modality.BoxCoalg
       Cat (GradeSystem.RGrade Grades) Fut using (BoxCoalg)

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

-- The environment morphism realising the substitution of `W` for `x`:
-- rebuild a `Γ`-environment from one for `Γ` with `x` removed, by
-- computing the missing component with `⟦ W ⟧`.

sub-env : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
        → ⟦ split-l x ++ᶜ split-r x ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
sub-env Hd                W = ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
sub-env (Tl-∷ x)          W = mapˣᵐ (sub-env x W) idᵐ
sub-env (Tl-⟨⟩ {ρ = ρ} x) W = ⟨ ρ ⟩ᶠ (sub-env x W)

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

eternal-val-ext-nat : ∀ {Γ A ρ} → (et : Eternal A) → (V : Γ ⊢V⦂ A)
                    → ⟦ eternal-val-ext {ρ = ρ} et V ⟧ᵛᵗ
                      ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ ⟨ ρ ⟩ᶠ ⟦ V ⟧ᵛᵗ

eternal-val-ext-nat {A = A} et (var f y) with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))))))
... | no ¬et' = ⊥-elim (¬et' et)
eternal-val-ext-nat (Baseₑ b eb) (const c) =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (⟦⟧ᵇᶜ-eternal eb c))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat Unitₑ ⋆ =
  ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique)
eternal-val-ext-nat (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ≈ᵐ-trans (⟨ eternal-val-ext-nat et₁ V₁ , eternal-val-ext-nat et₂ V₂ ⟩ᵐ-cong)
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
... | yes et = ⟨ idᵐ , ⟦ eternal-val-restrict et W ⟧ᵛᵗ ⟩ᵐ
... | no  _  = idᵐ
restrict-sub-env (Tl-∷ {B = B} x) W with eternal? B
... | yes _ = mapˣᵐ (restrict-sub-env x W) idᵐ
... | no  _ = restrict-sub-env x W
restrict-sub-env (Tl-⟨⟩ x) W = restrict-sub-env x W

-- An eternal value's interpretation factors through the eternal projection:
-- the value-level counterpart of `var-projᴱ` (and the value analog of
-- `eternal-val-ext-nat`). This carries the substituted eternal value onto the
-- eternal parameter in the handler substitution coherence below.

eternal-val-restrict-nat : ∀ {Γ A} → (et : Eternal A) → (V : Γ ⊢V⦂ A)
                         → ⟦ V ⟧ᵛᵗ ≈ᵐ ⟦ eternal-val-restrict et V ⟧ᵛᵗ ∘ᵐ projᴱ Γ
-- The interpretation of a *restricted* eternal value is a morphism of eternal
-- objects (commutes with the extractions). Its variables are all `∈-ᴱ` images,
-- so the variable case is exactly `eternal-mor`. This is what makes
-- `restrict-sub-env` a coalgebra morphism at the head.

restrict-val-mor : ∀ {Γ A} → (et : Eternal A) → (W : Γ ⊢V⦂ A) → ∀ {ρ}
                 → eternalᵛ-extᵉ et {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ ⟦ eternal-val-restrict et W ⟧ᵛᵗ
                 ≈ᵐ ⟦ eternal-val-restrict et W ⟧ᵛᵗ ∘ᵐ Eternalᵒ.extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ)
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

eternal-val-restrict-nat {A = A} et (var f x) with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))
  (≈ᵐ-trans (var-projᴱ et x)
            (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))
... | no ¬et' = ⊥-elim (¬et' et)
eternal-val-restrict-nat _ (const c) =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
eternal-val-restrict-nat _ ⋆ =
  ≈ᵐ-sym terminalᵐ-unique
eternal-val-restrict-nat (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ≈ᵐ-trans (⟨ eternal-val-restrict-nat et₁ V₁ , eternal-val-restrict-nat et₂ V₂ ⟩ᵐ-cong)
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
                → projᴱ Γ ∘ᵐ sub-env x W
                ≈ᵐ restrict-sub-env x W ∘ᵐ projᴱ (split-l x ++ᶜ split-r x)
projᴱ-subst-nat {Γ ∷ A} Hd W with eternal? A
... | yes et =
  ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
  (≈ᵐ-trans (⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , eternal-val-restrict-nat et W ⟩ᵐ-cong)
            (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))))
projᴱ-subst-nat (Tl-∷ {B = B} x) W with eternal? B
... | yes _ =
  ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
  (≈ᵐ-trans (mapˣᵐ-cong (projᴱ-subst-nat x W) ≈ᵐ-refl)
            (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-subst-nat x W))
            (∘ᵐ-assoc _ _ _))))
projᴱ-subst-nat (Tl-⟨⟩ x) W =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (projᴱ-subst-nat x W)))
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

unbox-var-nat : ∀ {Γ A C ρ ρ'} → (z : [ ρ ] A ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ)
              → (M : Γ ∷ A ⊢C⦂ C)
              → ⟦ unbox-var z rel M ⟧ᶜᵗ ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , lk z rel ⟩ᵐ
unbox-var-nat z rel M =
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
           → ⟦ M' ⟧ᶜᵗ ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ mapˣᵐ σ idᵐ
           → lk' ≈ᵐ lkᵒ ∘ᵐ σ
           → ⟦ M' ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , lk' ⟩ᵐ ≈ᵐ (⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , lkᵒ ⟩ᵐ) ∘ᵐ σ
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
             → ⟨⟩-≤ (proj₂ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
                 ∘ᵐ var-proj (proj₁ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
               ≈ᵐ var-proj y ∘ᵐ sub-env x W

sub-rvar-nat Hd Hd W with grad-typ⇒var W
... | σ' , v , f , refl =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-nat Hd (Tl-∷ x) W =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
sub-rvar-nat (Tl-∷ y) Hd W =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-nat (Tl-∷ y) (Tl-∷ x) W with ⟨ y ⟩[ x ↦ W ]rvar | sub-rvar-nat y x W
... | σ' , v , p | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-nat (Tl-⟨⟩ y) (Tl-⟨⟩ x) W with ⟨ y ⟩[ x ↦ W ]rvar | sub-rvar-nat y x W
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
       → (x : A ∈[ τ ] Γ) → (W : split-l x ⊢V⦂ A)
       → lk (proj₁ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
            (≾ᵣ-trans (proj₂ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar)) rel)
         ≈ᵐ lk y rel ∘ᵐ sub-env x W
sub-lk y rel x W =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans _ rel))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sub-rvar-nat y x W)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

-- The `unbox` case of the substitution coherence, with the unboxed resource
-- variable `y`/`rel` and the continuation's induction hypothesis taken as
-- parameters (so that the clause below needs only a single `with`).

unbox-subst-nat : ∀ {Γ A B C ρ σ τ}
                → (y : [ ρ ] B ∈[ σ ] Γ) → (rel : σ ≾ᵣ ρ)
                → (M : Γ ∷ B ⊢C⦂ C) → (x : A ∈[ τ ] Γ) → (W : split-l x ⊢V⦂ A)
                → ⟦ M [ Tl-∷ x ↦ W ]c ⟧ᶜᵗ ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ mapˣᵐ (sub-env x W) idᵐ
                → ⟦ unbox-var (proj₁ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar))
                              (≾ᵣ-trans (proj₂ (proj₂ ⟨ y ⟩[ x ↦ W ]rvar)) rel)
                              (M [ Tl-∷ x ↦ W ]c) ⟧ᶜᵗ
                  ≈ᵐ (⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , lk y rel ⟩ᵐ) ∘ᵐ sub-env x W
unbox-subst-nat y rel M x W ih with ⟨ y ⟩[ x ↦ W ]rvar | sub-lk y rel x W
... | _ , v , p | slk =
  ≈ᵐ-trans (unbox-var-nat v (≾ᵣ-trans p rel) (M [ Tl-∷ x ↦ W ]c))
           (unbox-step {M' = M [ Tl-∷ x ↦ W ]c} {M = M} {σ = sub-env x W}
                       {lk' = lk v (≾ᵣ-trans p rel)} {lkᵒ = lk y rel} ih slk)

-- Substitution in a variable.

sub-var-nat : ∀ {Γ A B ρ ρ'}
            → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
            → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
            → ⟦ ⟨ y , f ⟩[ x ↦ W ]var ⟧ᵛᵗ ≈ᵐ var-morphism f y ∘ᵐ sub-env x W

-- the substituted variable is the one being replaced
sub-var-nat {B = B} Hd f Hd W with eternal? B
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
sub-var-nat {B = B} Hd f (Tl-∷ x) W with eternal? B
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
sub-var-nat {B = B} (Tl-∷ y) f Hd W with eternal? B
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
sub-var-nat (Tl-∷ y) f (Tl-∷ x) W =
  ≈ᵐ-trans (V-rename-nat wk-ren ⟨ y , f ⟩[ x ↦ W ]var)
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-nat y f x W))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (var-morphism-Tl-∷ y f)))))))

sub-var-nat {B = B} (Tl-⟨⟩ y) f (Tl-⟨⟩ x) W with eternal? B
... | yes et =
  ≈ᵐ-trans (eternal-val-ext-nat et ⟨ y , _ ⟩[ x ↦ W ]var)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (sub-var-nat y _ x W)))
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
                         ⟨ y , _ ⟩[ x ↦ W ]var)
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-nat y _ x W))
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

subst-ctx-interp : ∀ {Δ Δ' C} → (e : Δ ≡ Δ') → (t : Δ ⊢C⦂ C)
                 → ⟦ subst (_⊢C⦂ C) e t ⟧ᶜᵗ ≈ᵐ ⟦ t ⟧ᶜᵗ ∘ᵐ ⟦ eq-ren e ⟧ʳ
subst-ctx-interp refl t = ≈ᵐ-sym (∘ᵐ-identityʳ _)

subst-clause-interp : ∀ {Δ Δ' D C} → (e : Δ ≡ Δ') → (t : Δ ++ᶜ D ⊢C⦂ C)
                    → ⟦ subst (λ Γ₀ → Γ₀ ++ᶜ D ⊢C⦂ C) e t ⟧ᶜᵗ
                    ≈ᵐ ⟦ t ⟧ᶜᵗ ∘ᵐ ⟦ eq-ren (cong (_++ᶜ D) e) ⟧ʳ
subst-clause-interp refl t = ≈ᵐ-sym (∘ᵐ-identityʳ _)

-- The interpretation of an equality renaming depends only on the endpoints of
-- the context equality (UIP), so any two proofs give the same transport.

eq-ren-irr : ∀ {Γ Γ'} → (e e' : Γ ≡ Γ') → ⟦ eq-ren e ⟧ʳ ≈ᵐ ⟦ eq-ren e' ⟧ʳ
eq-ren-irr e e' = ≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (uip {p = e} {q = e'}))

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
                        ∘ᵐ ⟦ eq-ren e ⟧ʳ
                      ≈ᵐ restrict-sub-env x W
eternal-bridge-core {A = A} et Hd W e with eternal? A
... | yes p =
  ≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-irr e refl))
  (≈ᵐ-trans (∘ᵐ-identityʳ _)
            (⟨ ≈ᵐ-refl
             , ≡→≈ᵐ (cong (λ q → ⟦ eternal-val-restrict q W ⟧ᵛᵗ)
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

  V-subst-nat : ∀ {Γ A B ρ} → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ ≈ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ sub-env x W
  V-subst-nat (var f y) x W = sub-var-nat y f x W
  V-subst-nat (const c) x W =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-subst-nat ⋆ x W = ≈ᵐ-sym terminalᵐ-unique
  V-subst-nat ⦉ V₁ , V₂ ⦊ x W =
    ≈ᵐ-trans (⟨ V-subst-nat V₁ x W , V-subst-nat V₂ x W ⟩ᵐ-cong)
             (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  V-subst-nat (lam M) x W =
    ≈ᵐ-trans (curryᵐ-cong (C-subst-nat M (Tl-∷ x) W))
             (curryᵐ-nat (sub-env x W) ⟦ M ⟧ᶜᵗ)

  C-subst-nat : ∀ {Γ A C ρ} → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ sub-env x W
  C-subst-nat (return V) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (M ⨟ N) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat (sub-env x W)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-subst-nat (V₁ · V₂) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-subst-nat V₁ x W , V-subst-nat V₂ x W ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (match V `in N) x W =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ (Tl-∷ x)) W))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
                   (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                    , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
  C-subst-nat (absurd V) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (perform op V M) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ
      (⟨ ≈ᵐ-trans (substᶜ-≈ (ty-gty (param op)) (V-subst-nat V x W))
                  (≡→≈ᵐ (sym (substᶜ-∘ (ty-gty (param op)) ⟦ V ⟧ᵛᵗ (sub-env x W))))
       , ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                    (≈ᵐ-trans (substᵈ-≈ (ty-gty (arity op))
                                (C-subst-nat M (Tl-∷ (Tl-⟨⟩ x)) W))
                              (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ
                                           (⟨ mapᵉ (op-grade op) ⟩ᶠ (sub-env x W)))))))))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-nat _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W)))
                   (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (delay τ M) x W =
    ≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (sub-env x W)))))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
                (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (C-subst-nat M (Tl-⟨⟩ x) W))))))))))
  -- The handle case mirrors `C-rename-nat`'s: the environment-threading second
  -- component commutes as for `⨟` (`seq-nat`), and the handler algebra is
  -- reindexed by `restrict-sub-env x W` (`alg-nat`, via `T-alg-of-handlerᵀ`'s
  -- congruence and naturality-in-P). The substitution splits on whether the
  -- variable is eternal; the two branches differ only in `⟦H'⟧ʰᵗ-nat`, which
  -- relates the substituted clause to the original reindexed clause — a pure
  -- reindexing transport when non-eternal (`restrict-transport`), and the
  -- restricted value placed at the split point when eternal (`eternal-bridge`).
  C-subst-nat {Γ = Γ} {A = A} (handle_`with_`in {A = Aₘ} {B = Bₘ} {ε} {ε'} M H N) x W
    with eternal? A
  ... | no ¬et =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-subst-nat x W) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
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
      seq-nat : Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ
              ≈ᵐ (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ) ∘ᵐ sub-env x W
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat (sub-env x W)
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W) ⟩ᵐ-cong)))
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
      step1 : ∀ op ε''
            → ⟦ H' op ε'' [] ⟧ᶜᵗ
            ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ ∘ᵐ mapˣᵐ (mapˣᵐ (restrict-sub-env x W) idᵐ) idᵐ
      step1 op ε'' =
        ≈ᵐ-trans (subst-clause-interp (ᴱ-drop-split ¬et x) (H op ε'' []))
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
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → ⟦_⟧ʰᵗ {Γ₀} H' op ε''
                 ≈ᵐ ⟦_⟧ʰᵗ {Γ} H op ε'' ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (step1 op ε''))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat : T-alg-of-handlerᵀ (eternalᵒ-boxCoalg (⟦ Γ₀ ⟧ᴱ-Eternalᵒ)) (⟦_⟧ʰᵗ {Γ₀} H')
              ≈ᵐ T-alg-of-handlerᵀ (eternalᵒ-boxCoalg (⟦ Γ ⟧ᴱ-Eternalᵒ)) (⟦_⟧ʰᵗ {Γ} H)
                  ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      alg-nat =
        ≈ᵐ-trans (T-alg-of-handlerᵀ-cong (eternalᵒ-boxCoalg (⟦ Γ₀ ⟧ᴱ-Eternalᵒ)) ⟦H'⟧ʰᵗ-nat)
                 (T-alg-of-handlerᵀ-natᴾ (eternalᵒ-boxCoalg (⟦ Γ ⟧ᴱ-Eternalᵒ))
                    (eternalᵒ-boxCoalg (⟦ Γ₀ ⟧ᴱ-Eternalᵒ))
                    (restrict-sub-env x W) (restrict-sub-env-necᵉ x W)
                    (⟦_⟧ʰᵗ {Γ} H))
  ... | yes et =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-subst-nat x W) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
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
      seq-nat : Tᶠ ⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ⟩ᵐ
              ≈ᵐ (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ) ∘ᵐ sub-env x W
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat (sub-env x W)
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W) ⟩ᵐ-cong)))
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
      step1 : ∀ op ε''
            → ⟦ H' op ε'' [] ⟧ᶜᵗ
            ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ ∘ᵐ mapˣᵐ (mapˣᵐ (restrict-sub-env x W) idᵐ) idᵐ
      step1 op ε'' =
        ≈ᵐ-trans (subst-ctx-interp ctxEq body)
        (≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat (H op ε'' []) (split→∈ s₀) Wᴱ₀))
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
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → ⟦_⟧ʰᵗ {Γ₀} H' op ε''
                 ≈ᵐ ⟦_⟧ʰᵗ {Γ} H op ε'' ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (step1 op ε''))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat : T-alg-of-handlerᵀ (eternalᵒ-boxCoalg (⟦ Γ₀ ⟧ᴱ-Eternalᵒ)) (⟦_⟧ʰᵗ {Γ₀} H')
              ≈ᵐ T-alg-of-handlerᵀ (eternalᵒ-boxCoalg (⟦ Γ ⟧ᴱ-Eternalᵒ)) (⟦_⟧ʰᵗ {Γ} H)
                  ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      alg-nat =
        ≈ᵐ-trans (T-alg-of-handlerᵀ-cong (eternalᵒ-boxCoalg (⟦ Γ₀ ⟧ᴱ-Eternalᵒ)) ⟦H'⟧ʰᵗ-nat)
                 (T-alg-of-handlerᵀ-natᴾ (eternalᵒ-boxCoalg (⟦ Γ ⟧ᴱ-Eternalᵒ))
                    (eternalᵒ-boxCoalg (⟦ Γ₀ ⟧ᴱ-Eternalᵒ))
                    (restrict-sub-env x W) (restrict-sub-env-necᵉ x W)
                    (⟦_⟧ʰᵗ {Γ} H))
  -- The substitution rebuilds the unboxing with `unbox-var`, so `unbox-var-nat`
  -- turns it back into a lookup; `unbox-step` then splits the goal into the
  -- continuation (the IH) and the lookup (`sub-lk`).
  C-subst-nat (unbox w V M) x W
    with grad-typ⇒var V | var-rename w (Tl-⟨⟩ (proj₁ (proj₂ (grad-typ⇒var V))))
  ... | _ , yv , f , refl | _ , b , y =
    unbox-subst-nat y
      (≾ᵣ-trans (b (λ ())) (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (f (λ ()))) (≾ᵣ-reflexive (·ᵣ-identityˡ _))))
      M x W (C-subst-nat M (Tl-∷ x) W)
  C-subst-nat (box V N) x W =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ x) W))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (V-subst-nat V (Tl-⟨⟩ x) W)))
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
                   (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W)))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-subst-nat (coerce rel M) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-subst-nat M x W)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
