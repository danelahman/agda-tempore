------------------------------------------------------------------------
-- Eternal values, resource lookups, and the one-variable environment.
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad
module MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Base
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

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts      S
open import MonomorphicCalculus.Syntax.Terms      S
open import MonomorphicCalculus.Syntax.Renaming      S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Substitution  S
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S using (Var)

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open GroundEternal GE
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE


-- The environment morphism realising the substitution of `W` for `x`:
-- rebuild a `Γ`-environment from one for `Γ` with `x` removed, by
-- computing the missing component with `⟦ W ⟧`.

-- `eternal-val-ext` builds only variables, constants, units, booleans,
-- numerals, pairs and injections, never a `fun`, so its result is
-- parametric outright.

eternal-val-extᴾ : ∀ {Γ A ρ} → (et : Et A) → (V : Γ ⊢V⦂ A)
                 → Paramᵛ (eternal-val-ext {ρ = ρ} et V)
eternal-val-extᴾ et (var _ x)                  = tt
eternal-val-extᴾ _  (const b)                  = tt
eternal-val-extᴾ _  ⋆                          = tt
eternal-val-extᴾ _  true                       = tt
eternal-val-extᴾ _  false                      = tt
eternal-val-extᴾ _  zero                       = tt
eternal-val-extᴾ et (succ V)                   = eternal-val-extᴾ et V
eternal-val-extᴾ _  nil                        = tt
eternal-val-extᴾ (listₑ et) (cons V W)         =
  eternal-val-extᴾ et V , eternal-val-extᴾ (listₑ et) W
eternal-val-extᴾ (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊    =
  eternal-val-extᴾ et₁ V₁ , eternal-val-extᴾ et₂ V₂
eternal-val-extᴾ (et₁ |+|ₑ _) (inl V)          = eternal-val-extᴾ et₁ V
eternal-val-extᴾ (_ |+|ₑ et₂) (inr V)          = eternal-val-extᴾ et₂ V
eternal-val-extᴾ et (subV V p)                 =
  eternal-val-extᴾ (<:ᵛ-eternalˡ p et) V

sub-env : ∀ {Γ Γ₁ Γ₂ A} → (s : Γ₁ ∷ A , Γ₂ split Γ) → (W : Γ₁ ⊢V⦂ A) → Paramᵛ W
        → ⟦ Γ₁ ++ᶜ Γ₂ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
sub-env split-[]              W pW = ⟨ idᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
sub-env (split-∷ s)           W pW = mapˣᵐ (sub-env s W pW) idᵐ
sub-env (split-⟨⟩ {ρ = ρ} s)  W pW = ⟨ ρ ⟩ᶠ (sub-env s W pW)

-- (`var-morphism-Tl-∷` lives in `Interpretation.Variables`.)

-- Weakening a value of eternal type under a lock: denotationally this is
-- the eternal extraction applied to the locked environment. Proved by
-- induction on the value (only the eternal formers can occur).

-- Extraction commutes with a coercion out of an eternal type: such a
-- coercion has equal endpoints, hence is the identity.

extᵉ-<: : ∀ {A B ρ} → (et : Et A) → (et' : Et B) → (p : A <:ᵛ B)
        → ⟦ p ⟧<:ᵛ ∘ᵐ eternalᵛ-extᵉ et {ρ} ≈ᵐ eternalᵛ-extᵉ et' ∘ᵐ ⟨ ρ ⟩ᶠ ⟦ p ⟧<:ᵛ
extᵉ-<: et et' p with <:ᵛ-eternal-≡ et p
... | refl =
  ≈ᵐ-trans (∘ᵐ-congˡ (⟦⟧<:ᵛ-id p))
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (eternalᵛ-extᵉ-irr et et')
  (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (⟨⟩-congᶠ (⟦⟧<:ᵛ-id p)) ⟨⟩-idᵐ))
                    (∘ᵐ-identityʳ _)))))

eternal-val-ext-nat : ∀ {Γ A ρ} → (et : Et A) → (V : Γ ⊢V⦂ A) → (pV : Paramᵛ V)
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
eternal-val-ext-nat (Baseₑ eb) (const c) _ =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (⟦⟧ᵇᶜ-eternal eb c))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat unitₑ ⋆ _ =
  ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique)
eternal-val-ext-nat boolₑ true _ =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ trueᵐ-eternal)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat boolₑ false _ =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ falseᵐ-eternal)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat natₑ zero _ =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ zeroᵐ-eternal)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat natₑ (succ V) pV =
  ≈ᵐ-trans (∘ᵐ-congʳ (eternal-val-ext-nat natₑ V pV))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym succᵐ-eternal))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))))
eternal-val-ext-nat (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ (p₁ , p₂) =
  ≈ᵐ-trans (⟨ eternal-val-ext-nat et₁ V₁ p₁ , eternal-val-ext-nat et₂ V₂ p₂ ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
             , ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))) ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) , ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) , ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong)
  (≈ᵐ-trans (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (×-eternalᵒ-extᵉ (eternalᵛ-Eternalᵒ et₁)
                                              (eternalᵛ-Eternalᵒ et₂))))))))
eternal-val-ext-nat (et₁ |+|ₑ et₂) (inl V) pV =
  ≈ᵐ-trans (∘ᵐ-congʳ (eternal-val-ext-nat et₁ V pV))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (+-eternalᵒ-inl (eternalᵛ-Eternalᵒ et₁)
                                               (eternalᵛ-Eternalᵒ et₂))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))))
eternal-val-ext-nat (et₁ |+|ₑ et₂) (inr V) pV =
  ≈ᵐ-trans (∘ᵐ-congʳ (eternal-val-ext-nat et₂ V pV))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (+-eternalᵒ-inr (eternalᵛ-Eternalᵒ et₁)
                                               (eternalᵛ-Eternalᵒ et₂))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))))
eternal-val-ext-nat (listₑ et) nil _ =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (List-eternalᵒ-nil (eternalᵛ-Eternalᵒ et)))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat (listₑ et) (cons V W) (pV , pW) =
  ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans
    (⟨ eternal-val-ext-nat et V pV , eternal-val-ext-nat (listₑ et) W pW ⟩ᵐ-cong)
    (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
               , ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))) ⟩ᵐ-cong)
    (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) , ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩ᵐ-cong)
    (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) , ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong)
              (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (List-eternalᵒ-cons (eternalᵛ-Eternalᵒ et))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))))
eternal-val-ext-nat et (subV V p) pV =
  ≈ᵐ-trans (∘ᵐ-congʳ (eternal-val-ext-nat (<:ᵛ-eternalˡ p et) V pV))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (extᵉ-<: (<:ᵛ-eternalˡ p et) et p))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))))

-- (`eq-ren-∷` / `eq-ren-⟨⟩` / `eq-ren-irr` live with the other renaming
-- denotation lemmas in `Interpretation.Renaming`.)

-- The resource lookup morphism of an `unbox`.

lk : ∀ {Γ A A₀ ρ ρ'} → [ ρ ] A₀ ∈[ ρ' ] Γ → ρ' ≾ᵣ ρ → A₀ <:ᵛ A
   → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
lk z rel w = ⟦ w ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj z

-- It depends on the cell alone, the bound and the payload witness being
-- irrelevant.

lk-irr : ∀ {Γ A A₀ ρ} → {t t' : Var Γ ([ ρ ] A₀)} → t ≡ t'
       → (b : proj₁ t ≾ᵣ ρ) → (b' : proj₁ t' ≾ᵣ ρ)
       → (w w' : A₀ <:ᵛ A)
       → lk (proj₂ t) b w ≈ᵐ lk (proj₂ t') b' w'
lk-irr refl b b' w w'
  rewrite ≾ᵣ-irrelevant b b' | <:ᵛ-irrelevant w w' = ≈ᵐ-refl

-- Projecting the head variable through one lock and relaxing the redundant
-- `𝟏ᵣ ·ᵣ ρ` back to `ρ` is the (locked) second projection.

hd-lookup : ∀ {Δ₀ B ρ} → (c : 𝟏ᵣ ·ᵣ ρ ≾ᵣ ρ)
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

var-morphism-et : ∀ {Γ B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Et B → ρ' ≾ᵣ 𝟏ᵣ)
                → (et : Et B)
                → var-morphism f y ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ var-proj y
var-morphism-et {B = B} y f et with eternal? B
... | yes et' = ∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et)
... | no ¬et' = ⊥-elim (¬et' et)

var-morphism-¬et : ∀ {Γ B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Et B → ρ' ≾ᵣ 𝟏ᵣ)
                 → (¬et : ¬ Et B)
                 → var-morphism f y ≈ᵐ εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj y
var-morphism-¬et {B = B} y f ¬et with eternal? B
... | yes et'  = ⊥-elim (¬et et')
... | no ¬et'' = ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))

-- A value of box type is an occurrence up to subsumption
-- (`grad-typ⇒var<:`); denotationally it is that occurrence's projection
-- followed by the coercion. Stated on the packed inversion so that it
-- reduces wherever `grad-typ⇒var<:` does.

boxed-proj : ∀ {Γ A ρ}
           → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Σ[ ρ' ∈ R ]
               (([ ρ₀ ] A₀ ∈[ ρ' ] Γ) × (([ ρ₀ ] A₀) <:ᵛ ([ ρ ] A)) × ρ' ≾ᵣ 𝟏ᵣ)
           → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟨ 𝟏ᵣ ⟩ᵒ ⟦ [ ρ ] A ⟧ᵛ
boxed-proj (_ , _ , _ , x , w , b) = ⟨ 𝟏ᵣ ⟩ᶠ ⟦ w ⟧<:ᵛ ∘ᵐ ⟨⟩-≤ b ∘ᵐ var-proj x

grad-typ-var-nat : ∀ {Γ A ρ} → (W : Γ ⊢V⦂ [ ρ ] A) → (pW : Paramᵛ W)
                 → boxed-proj (grad-typ⇒var<: W) ≈ᵐ η ∘ᵐ ⟦ W ⟧ᵛᵗ pW
grad-typ-var-nat {A = A} {ρ = ρ} (var f x) _ =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩-congᶠ (⟦⟧<:ᵛ-refl ([ ρ ] A))) ⟨⟩-idᵐ))
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-irr _ (f (λ ()))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (var-morphism-¬et x f (λ ())))))))))
grad-typ-var-nat (subV V p@([ _ ]ₛ _)) pV with grad-typ⇒var<: V | grad-typ-var-nat V pV
... | _ , _ , _ , x , q , b | ih =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩-congᶠ (⟦⟧<:ᵛ-trans q p)) (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ ih)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-η-nat _)) (∘ᵐ-assoc _ _ _)))))
