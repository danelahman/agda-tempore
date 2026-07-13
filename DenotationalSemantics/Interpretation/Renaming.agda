------------------------------------------------------------------------
-- Interpretation of context renamings.                                --
--                                                                    --
-- A renaming `Ren Γ Γ'` rewrites a `Γ`-typed term into a `Γ'`-typed    --
-- term (`V-rename`/`C-rename`), so on environments it runs             --
-- contravariantly, as a reindexing `⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ`. Each       --
-- constructor is a structural map of the model: weakening projects      --
-- (`fstᵐ`), a variable renaming contracts (`⟨ idᵐ , var-morphism … ⟩ᵐ`), --
-- and the lock (possibility) renamings are exactly the past modality's  --
-- unit `η`, counit `εᵘ`, multiplication `μ`, and monotonicity `⟨⟩-≤` —   --
-- all available at an *arbitrary* resource grade.                       --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Renaming
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

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)


open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (var-rename)

open Category Cat
open Past Pst

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE

-- The reindexing morphism of a renaming (contravariant in the context).

⟦_⟧ʳ : ∀ {Γ Γ'} → Ren Γ Γ' → ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
⟦ id-ren ⟧ʳ              = idᵐ
⟦ r₂ ∘ʳ r₁ ⟧ʳ            = ⟦ r₁ ⟧ʳ ∘ᵐ ⟦ r₂ ⟧ʳ
⟦ wk-ren ⟧ʳ              = fstᵐ
⟦ var-ren p x ⟧ʳ         = ⟨ idᵐ , var-morphism (λ _ → p) x ⟩ᵐ
⟦ ⟨⟩-η-ren ⟧ʳ            = η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ          = εᵘ
⟦ ⟨⟩-μ-ren {Γ} {ρ} {ρ'} ⟧ʳ = μ {⟦ Γ ⟧ᶜᵗˣ} {ρ'} {ρ}
⟦ ⟨⟩-≤-ren rel ⟧ʳ        = ⟨⟩-≤ rel
⟦ cong-∷-ren r ⟧ʳ        = mapˣᵐ ⟦ r ⟧ʳ idᵐ
⟦ cong-⟨⟩-ren {ρ = ρ} r ⟧ʳ = ⟨ ρ ⟩ᶠ ⟦ r ⟧ʳ

-- Naturality of `var-proj` under a renaming: projecting the renamed
-- variable (relaxed back to the original grade) equals projecting the
-- original variable and reindexing the environment by `⟦ r ⟧ʳ`.

var-proj-nat : ∀ {Γ Γ' A ρ} → (r : Ren Γ Γ') → (x : A ∈[ ρ ] Γ)
             → ⟨⟩-≤ (proj₁ (proj₂ (var-rename r x)))
                 ∘ᵐ var-proj (proj₂ (proj₂ (var-rename r x)))
               ≈ᵐ var-proj x ∘ᵐ ⟦ r ⟧ʳ
var-proj-nat id-ren x =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _)))
var-proj-nat (r₂ ∘ʳ r₁) x with var-rename r₁ x | var-proj-nat r₁ x | var-rename r₂ (proj₂ (proj₂ (var-rename r₁ x))) | var-proj-nat r₂ (proj₂ (proj₂ (var-rename r₁ x)))
... | ρ' , ρ'≾ρ , y | ih₁ | ρ'' , ρ''≾ρ' , z | ih₂ =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans ρ''≾ρ' ρ'≾ρ)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ ih₂)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih₁)
            (∘ᵐ-assoc _ _ _)))))
var-proj-nat wk-ren x =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl) (∘ᵐ-identityˡ _)
var-proj-nat {A = A} (var-ren p y) Hd with eternal? A
... | yes et =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-η-ext et p)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
... | no ¬et =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
var-proj-nat (var-ren p y) (Tl-∷ x) =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
var-proj-nat ⟨⟩-η-ren (Tl-⟨⟩ x) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-μ∘η≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-η-nat (var-proj x))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat ⟨⟩-η⁻¹-ren Hd =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))
var-proj-nat ⟨⟩-η⁻¹-ren (Tl-∷ x) =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))
var-proj-nat ⟨⟩-η⁻¹-ren (Tl-⟨⟩ x) =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))
var-proj-nat ⟨⟩-μ-ren (Tl-⟨⟩ x) =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-μ∘μ≡μ∘Tμ))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-μ-nat (var-proj x))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
var-proj-nat (⟨⟩-≤-ren ρ'≾ρ) (Tl-⟨⟩ x) =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (μ-≤ʳ ρ'≾ρ))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat (var-proj x) ρ'≾ρ)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
var-proj-nat (cong-∷-ren r) Hd =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat (cong-∷-ren r) (Tl-∷ x) with var-rename r x | var-proj-nat r x
... | (ρ' , ρ'≾ρ , y) | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
var-proj-nat (cong-⟨⟩-ren r) (Tl-⟨⟩ x) with var-rename r x | var-proj-nat r x
... | (ρ' , ρ'≾ρ , y) | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (μ-≤ˡ ρ'≾ρ))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ ih))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))

-- Naturality of the variable interpretation under a renaming (this is the
-- `var` case of the term-renaming coherence): from `var-proj-nat` plus the
-- eternal grade-independence `eternalᵛ-extᵉ-≤`.

var-morphism-nat : ∀ {Γ Γ' A ρ} → (r : Ren Γ Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ ] Γ)
                 → var-morphism (λ q → ≾ᵣ-trans (proj₁ (proj₂ (var-rename r x))) (f q))
                                (proj₂ (proj₂ (var-rename r x)))
                   ≈ᵐ var-morphism f x ∘ᵐ ⟦ r ⟧ʳ
var-morphism-nat {A = A} r f x with eternal? A | var-rename r x | var-proj-nat r x
... | yes et | ρ' , ρ'≾ρ , y | vpn =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et ρ'≾ρ)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ vpn)
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
... | no ¬et | ρ' , ρ'≾ρ , y | vpn =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans ρ'≾ρ (f ¬et)))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ vpn))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
