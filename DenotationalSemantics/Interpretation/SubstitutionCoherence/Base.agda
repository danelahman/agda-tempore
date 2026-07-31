------------------------------------------------------------------------
-- Eternal values, resource lookups, and the one-variable environment.
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
open import Syntax.Renamings.Equivalence S using (Var)

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

sub-env : ∀ {Γ Γ₁ Γ₂ A} → (s : Γ₁ ∷ A , Γ₂ split Γ) → (W : Γ₁ ⊢V⦂ A) → Paramᵛ W
        → ⟦ Γ₁ ++ᶜ Γ₂ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
sub-env split-[]              W pW = ⟨ idᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
sub-env (split-∷ s)           W pW = mapˣᵐ (sub-env s W pW) idᵐ
sub-env (split-⟨⟩ {ρ = ρ} s)  W pW = ⟨ ρ ⟩ᶠ (sub-env s W pW)

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
-- so the variable case is exactly `eternal-mor`. This is what makes the
-- restricted substitution a coalgebra morphism at the head.

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
-- matched against `refl`)

split-lookup-e : ∀ {Γ Γ₁ Γ₂ A ρ} → (c : Γ₁ ∷ A , Γ₂ split Γ) → (e : ctx-grade Γ₂ ≡ ρ)
               → ⟨ ρ ⟩ᶠ sndᵐ
                   ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {Γ₁ ∷ A} {Γ₂} e ⟧ʳ
                   ∘ᵐ ⟦ eq-ren (split-≡ c) ⟧ʳ
                 ≈ᵐ var-proj (subst (A ∈[_] Γ) e (split-var c))
split-lookup-e c refl = split-lookup-gen c


-- The resource lookup morphism of an `unbox`.

lk : ∀ {Γ A ρ ρ'} → [ ρ ] A ∈[ ρ' ] Γ → ρ' ≾ᵣ ρ → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
lk z rel = ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj z

-- It depends on the cell alone, the bound being irrelevant.

lk-irr : ∀ {Γ A ρ} → {t t' : Var Γ ([ ρ ] A)} → t ≡ t'
       → (b : proj₁ t ≾ᵣ ρ) → (b' : proj₁ t' ≾ᵣ ρ)
       → lk (proj₂ t) b ≈ᵐ lk (proj₂ t') b'
lk-irr refl b b' rewrite ≾ᵣ-irrelevant b b' = ≈ᵐ-refl

-- Projecting the head variable through one lock and relaxing the redundant
-- `uᵣ ·ᵣ ρ` back to `ρ` is just the (locked) second projection.

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

-- Given that the continuation and the resource lookup each commute with the
-- substitution, so does the whole unboxing.

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
