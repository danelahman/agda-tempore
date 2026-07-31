------------------------------------------------------------------------
-- Extending an environment morphism through a context suffix.
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
module DenotationalSemantics.Interpretation.Renaming.Extension
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

open import Data.Empty using (⊥-elim)
open import Util.Equality using (sym; trans; _≡_; refl; cong; subst; uip)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)


open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (var-rename)
open import Syntax.Renamings.Equivalence S using (eternal?-yes)

open Category Cat
open Past Pst
open GroundEternal GE
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming.Algebra S Cat Fut Pst Adj GTy Mon GE

-- EXTENDING AN ENVIRONMENT MORPHISM THROUGH A CONTEXT SUFFIX
--
-- `ext Γ Γ' Θ` weakens a morphism `⟦ Γ ⟧ → ⟦ Γ' ⟧` past everything a suffix
-- `Θ` binds. It is the semantic counterpart of the syntactic `cong-ren`,
-- generalised from renaming denotations to arbitrary
-- morphisms — which is what an environment *extension* (e.g. the one `box`
-- installs) needs, since that is not the denotation of any renaming. It is
-- also the same recursion as `sub-env`.
--
-- The two contexts are explicit: they only ever occur under `⟦_⟧ᶜᵗˣ`, which is
-- not injective, so leaving them implicit makes every use ambiguous.

ext : (Γ Γ' Θ : Ctx) → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ
    → ⟦ Γ ++ᶜ Θ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ++ᶜ Θ ⟧ᶜᵗˣ
ext Γ Γ' []        g = g
ext Γ Γ' (Θ ∷ A)   g = mapˣᵐ (ext Γ Γ' Θ g) idᵐ
ext Γ Γ' (Θ ⟨ ρ ⟩) g = ⟨ ρ ⟩ᶠ (ext Γ Γ' Θ g)

-- `ext` is natural in the suffix: a context equality of suffixes commutes
-- with the extension.

ext-eq : (Γ Γ' : Ctx) → {Θ Θ' : Ctx} → (g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ) → (e : Θ ≡ Θ')
       → ⟦ eq-ren (cong (Γ' ++ᶜ_) e) ⟧ʳ ∘ᵐ ext Γ Γ' Θ' g
       ≈ᵐ ext Γ Γ' Θ g ∘ᵐ ⟦ eq-ren (cong (Γ ++ᶜ_) e) ⟧ʳ
ext-eq Γ Γ' g refl = ≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _))

-- Extending through a concatenated suffix is extending twice (up to the
-- associativity coercion). Induction on the outer suffix, following
-- `++ᶜ-assoc`'s own `refl`/`cong` structure.

ext-++ᶜ : (Γ Γ' : Ctx) → (g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ) → (Θ Δ : Ctx)
        → ⟦ eq-ren (sym (++ᶜ-assoc Γ' Θ Δ)) ⟧ʳ
            ∘ᵐ ext (Γ ++ᶜ Θ) (Γ' ++ᶜ Θ) Δ (ext Γ Γ' Θ g)
        ≈ᵐ ext Γ Γ' (Θ ++ᶜ Δ) g ∘ᵐ ⟦ eq-ren (sym (++ᶜ-assoc Γ Θ Δ)) ⟧ʳ
ext-++ᶜ Γ Γ' g Θ [] =
  ≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _))
ext-++ᶜ Γ Γ' g Θ (Δ ∷ A) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (eq-ren-irr (sym (++ᶜ-assoc Γ' Θ (Δ ∷ A)))
                                           (cong (_∷ A) (sym (++ᶜ-assoc Γ' Θ Δ))))
                               (eq-ren-∷ (sym (++ᶜ-assoc Γ' Θ Δ)))))
  (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
  (≈ᵐ-trans (mapˣᵐ-cong (ext-++ᶜ Γ Γ' g Θ Δ) ≈ᵐ-refl)
  (≈ᵐ-trans (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))
            (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (eq-ren-∷ (sym (++ᶜ-assoc Γ Θ Δ))))
                                (eq-ren-irr (cong (_∷ A) (sym (++ᶜ-assoc Γ Θ Δ)))
                                            (sym (++ᶜ-assoc Γ Θ (Δ ∷ A)))))))))
ext-++ᶜ Γ Γ' g Θ (Δ ⟨ ρ ⟩) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (eq-ren-irr (sym (++ᶜ-assoc Γ' Θ (Δ ⟨ ρ ⟩)))
                                           (cong (_⟨ ρ ⟩) (sym (++ᶜ-assoc Γ' Θ Δ))))
                               (eq-ren-⟨⟩ (sym (++ᶜ-assoc Γ' Θ Δ)))))
  (≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (⟨⟩-congᶠ (ext-++ᶜ Γ Γ' g Θ Δ))
  (≈ᵐ-trans (⟨⟩-∘ᵐ _ _)
            (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (eq-ren-⟨⟩ (sym (++ᶜ-assoc Γ Θ Δ))))
                                (eq-ren-irr (cong (_⟨ ρ ⟩) (sym (++ᶜ-assoc Γ Θ Δ)))
                                            (sym (++ᶜ-assoc Γ Θ (Δ ⟨ ρ ⟩)))))))))


-- Reading a morphism of the `⟨ ρ ⟩X` factor back through the eternal strength:
-- `strᵉ` cancels against `⟨ ρ ⟩ᶠ fstᵐ`, leaving the plain first projection. The
-- shared core of the `⟨⟩-ext-ren` cases below (both wrap this with an extra
-- extraction / grade coercion on the left).

strᵉ-past-fstᵐ : ∀ {A} → (et : Eternal A) → ∀ {ρ X Z} → (g : ⟨ ρ ⟩ᵒ X →ᵐ Z)
              → (g ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ) ∘ᵐ eternalᵛ-strᵉ et {ρ} {X} ≈ᵐ g ∘ᵐ fstᵐ
strᵉ-past-fstᵐ et g =
  ≈ᵐ-trans (∘ᵐ-assoc g (⟨ _ ⟩ᶠ fstᵐ) (eternalᵛ-strᵉ et))
           (∘ᵐ-congʳ (eternalᵛ-strᵉ-fstᵐ et))

-- Naturality of `var-proj` under a renaming: projecting the renamed
-- variable (relaxed back to the original grade) equals projecting the
-- original variable and reindexing the environment by `⟦ r ⟧ʳ`.

var-proj-nat : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → (x : A ∈[ ρ ] Γ) → (¬et : ¬ Eternal A)
             → ⟨⟩-≤ (proj₁ (proj₂ (var-rename r x)) ¬et)
                 ∘ᵐ var-proj (proj₂ (proj₂ (var-rename r x)))
               ≈ᵐ var-proj x ∘ᵐ ⟦ r ⟧ʳ
var-proj-nat id-ren x ¬et =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _)))
var-proj-nat (r₁ ∘ʳ r₂) x ¬et with var-rename r₁ x | var-proj-nat r₁ x ¬et | var-rename r₂ (proj₂ (proj₂ (var-rename r₁ x))) | var-proj-nat r₂ (proj₂ (proj₂ (var-rename r₁ x))) ¬et
... | ρ' , ρ'≾ρ , y | ih₁ | ρ'' , ρ''≾ρ' , z | ih₂ =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans (ρ''≾ρ' ¬et) (ρ'≾ρ ¬et))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ ih₂)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih₁)
            (∘ᵐ-assoc _ _ _)))))
var-proj-nat wk-ren x ¬et =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl) (∘ᵐ-identityˡ _)
var-proj-nat {A = A} (var-ren p y) Hd ¬et with eternal? A
... | yes et = ⊥-elim (¬et et)
... | no ¬et' =
  ≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
var-proj-nat (var-ren p y) (Tl-∷ x) ¬et =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
-- every variable of an eternal ambient is eternal, so this case is vacuous
var-proj-nat (⟨⟩-ext-ctx _ ecΓ) x ¬et =
  ⊥-elim (¬et (ec-eternal ecΓ x))
var-proj-nat ⟨⟩-η-ren (Tl-⟨⟩ x) ¬et =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-μ∘η≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-η-nat (var-proj x))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat ⟨⟩-η⁻¹-ren Hd ¬et =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))
var-proj-nat ⟨⟩-η⁻¹-ren (Tl-∷ x) ¬et =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))
var-proj-nat ⟨⟩-η⁻¹-ren (Tl-⟨⟩ x) ¬et =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))
var-proj-nat ⟨⟩-μ-ren (Tl-⟨⟩ x) ¬et =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-μ∘μ≡μ∘Tμ))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-μ-nat (var-proj x))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
var-proj-nat (⟨⟩-≤-ren ρ'≾ρ) (Tl-⟨⟩ x) ¬et =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (μ-≤ʳ ρ'≾ρ))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat (var-proj x) ρ'≾ρ)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
var-proj-nat (cong-∷-ren r) Hd ¬et =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat (cong-∷-ren r) (Tl-∷ x) ¬et with var-rename r x | var-proj-nat r x ¬et
... | (ρ' , ρ'≾ρ , y) | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
var-proj-nat (cong-⟨⟩-ren r) (Tl-⟨⟩ x) ¬et with var-rename r x | var-proj-nat r x ¬et
... | (ρ' , ρ'≾ρ , y) | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (μ-≤ˡ (ρ'≾ρ ¬et)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ ih))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
var-proj-nat (⟨⟩-ext-ren et) (Tl-⟨⟩ Hd) ¬et = ⊥-elim (¬et et)
var-proj-nat (⟨⟩-ext-ren et) (Tl-⟨⟩ (Tl-∷ x)) ¬et =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (strᵉ-past-fstᵐ et (μ ∘ᵐ ⟨ _ ⟩ᶠ (var-proj x)))))))

-- Naturality of the variable interpretation under a renaming (this is the
-- `var` case of the term-renaming coherence): from `var-proj-nat` plus the
-- eternal grade-independence `eternalᵛ-extᵉ-≤`.

-- Naturality of the eternal variable interpretation, grade-free. For an
-- eternal type the extraction is uniform in the grade, so the coercion
-- `⟨⟩-≤` that `var-proj-nat` carries is absorbed; proved by induction on the
-- renaming using the eternal-extraction algebra laws.

var-proj-nat-eternal : ∀ {Γ Γ' A ρ} → (et : Eternal A) → (r : Ren [] Γ' Γ) → (x : A ∈[ ρ ] Γ)
    → eternalᵛ-extᵉ et {proj₁ (var-rename r x)} ∘ᵐ var-proj (proj₂ (proj₂ (var-rename r x)))
      ≈ᵐ (eternalᵛ-extᵉ et {ρ} ∘ᵐ var-proj x) ∘ᵐ ⟦ r ⟧ʳ
var-proj-nat-eternal et id-ren x =
  ≈ᵐ-sym (∘ᵐ-identityʳ _)
var-proj-nat-eternal et (r₁ ∘ʳ r₂) x
  with var-rename r₁ x | var-proj-nat-eternal et r₁ x
     | var-rename r₂ (proj₂ (proj₂ (var-rename r₁ x))) | var-proj-nat-eternal et r₂ (proj₂ (proj₂ (var-rename r₁ x)))
... | ρ₁' , _ , y₁ | ih₁ | ρ₂' , _ , y₂ | ih₂ =
  ≈ᵐ-trans ih₂
  (≈ᵐ-trans (∘ᵐ-congˡ ih₁)
            (∘ᵐ-assoc _ _ _))
var-proj-nat-eternal et wk-ren x =
  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
var-proj-nat-eternal et (var-ren p y) Hd =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (var-morphism-unfoldᵉ et p y)))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et)) ⟨⟩-εᵘ∘η≡id))
              (∘ᵐ-identityˡ _)))))))
var-proj-nat-eternal et (var-ren p y) (Tl-∷ x) =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-congʳ (∘ᵐ-identityʳ _)))))
var-proj-nat-eternal et ⟨⟩-η-ren (Tl-⟨⟩ x) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et (≾ᵣ-reflexive (sym (·ᵣ-identityʳ _))))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-μ∘η≡id))
                      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-η-nat (var-proj x))))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat-eternal et ⟨⟩-η⁻¹-ren Hd =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et (≾ᵣ-reflexive (·ᵣ-identityʳ uᵣ)))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat-eternal et ⟨⟩-η⁻¹-ren (Tl-∷ x) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et (≾ᵣ-reflexive (·ᵣ-identityʳ _)))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat-eternal et ⟨⟩-η⁻¹-ren (Tl-⟨⟩ x) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et (≾ᵣ-reflexive (·ᵣ-identityʳ (_ ·ᵣ _))))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      (≈ᵐ-trans (∘ᵐ-congˡ μ-εᵘ) (≈ᵐ-sym (εᵘ-nat _)))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat-eternal et ⟨⟩-μ-ren (Tl-⟨⟩ x) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et (≾ᵣ-reflexive (·ᵣ-assoc _ _ _)))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))
                      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-μ∘μ≡μ∘Tμ))
                      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-μ-nat (var-proj x))))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat-eternal et (⟨⟩-≤-ren ρ'≾ρ) (Tl-⟨⟩ x) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et (·ᵣ-monoʳ-≾ᵣ ρ'≾ρ))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      (≈ᵐ-trans (∘ᵐ-congˡ (μ-≤ʳ ρ'≾ρ))
                      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat (var-proj x) ρ'≾ρ)))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
var-proj-nat-eternal et (cong-∷-ren r) Hd =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))))
var-proj-nat-eternal et (cong-∷-ren r) (Tl-∷ x) with var-rename r x | var-proj-nat-eternal et r x
... | (ρ' , _ , y) | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))))))))
var-proj-nat-eternal et (cong-⟨⟩-ren r) (Tl-⟨⟩ x)
  with var-rename r x | var-proj-nat-eternal et r x
... | (ρ' , _ , y) | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ ih))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et)))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
              (∘ᵐ-assoc _ _ _)))))))))))
var-proj-nat-eternal {A = A} et' (⟨⟩-ext-ren et) (Tl-⟨⟩ Hd) =
  ≈ᵐ-trans (extᵉ-η _)
  (≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et')))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-congᶠ (extᵉ-η _))))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))
              (eternalᵛ-strᵉ-sndᵐ et)))))))))
  where
    -- `extᵉ` at `uᵣ` after `η` is the identity: `extᵉ{uᵣ}=εᵘ` and `εᵘ∘η≈id`.
    extᵉ-η : ∀ {W} → (s : W →ᵐ ⟦ A ⟧ᵛ) → eternalᵛ-extᵉ et' {uᵣ} ∘ᵐ (η ∘ᵐ s) ≈ᵐ s
    extᵉ-η s =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et')))
      (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id) (∘ᵐ-identityˡ s)))
var-proj-nat-eternal et' (⟨⟩-ext-ren et) (Tl-⟨⟩ (Tl-∷ x)) =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (strᵉ-past-fstᵐ et (eternalᵛ-extᵉ et' ∘ᵐ (μ ∘ᵐ ⟨ _ ⟩ᶠ (var-proj x))))
              (∘ᵐ-assoc _ _ _)))))
-- Introducing a lock: `extᵉ-μ` splits the extraction across the new lock, and
-- `ec-var-alg` absorbs the outer half into the ambient's own extraction. This is
-- the case the ambient index exists for.
var-proj-nat-eternal et (⟨⟩-ext-ctx _ ecΓ) x =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (ec-var-alg ecΓ et x))))

var-morphism-nat : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ ] Γ)
                 → var-morphism (λ q → ≾ᵣ-trans (proj₁ (proj₂ (var-rename r x)) q) (f q))
                                (proj₂ (proj₂ (var-rename r x)))
                   ≈ᵐ var-morphism f x ∘ᵐ ⟦ r ⟧ʳ
var-morphism-nat {A = A} r f x with eternal? A
... | yes et = var-proj-nat-eternal et r x
... | no ¬et with var-rename r x | var-proj-nat r x ¬et
...   | ρ' , ρ'≾ρ , y | vpn =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans (ρ'≾ρ ¬et) (f ¬et)))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ vpn))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

-- The interpretation of a *restricted* renaming is a morphism of eternal
-- objects: it commutes with the eternal extractions of its (eternal) source
-- and target restrictions. Proved by recursion on the renaming; the eternal
-- variable case is exactly `eternal-mor`.

restrict-ren-mor : ∀ {Γ Γ'} → (r : Ren [] Γ' Γ) → ∀ {ρ}
                 → projᴱ-extᵉ Γ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ ⟦ restrict-ren r ⟧ʳ
                 ≈ᵐ ⟦ restrict-ren r ⟧ʳ ∘ᵐ projᴱ-extᵉ Γ' {ρ}
restrict-ren-mor id-ren =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor (r₁ ∘ʳ r₂) =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (restrict-ren-mor r₁))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (restrict-ren-mor r₂))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
restrict-ren-mor {Γ} (wk-ren {A = A}) {ρ} with eternal? A
... | yes eA = ≈ᵐ-sym (projᴱ-extᵉ-fst {Γ} {A} eA {ρ})
... | no  _  =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor (var-ren {Δ = Γ₀} {A = A} p x) {ρ} with eternal? A
... | yes eA =
  prod-ext
    -- fstᵐ: extraction of `Γ ᴱ` on both sides (`idᵐ` component)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ₀} {A} eA {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
    (≈ᵐ-trans (∘ᵐ-identityʳ _)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-assoc _ _ _))))))))))
    -- sndᵐ: the variable morphism, via `var-morphism-∈ᴱ-mor`
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ₀} {A} eA {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (var-morphism-∈ᴱ-mor eA x)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)))
              (∘ᵐ-assoc _ _ _))))))))
... | no  _  =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor ⟨⟩-η-ren =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor ⟨⟩-η⁻¹-ren =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor ⟨⟩-μ-ren =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor (⟨⟩-≤-ren _) =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor (cong-∷-ren {Δ = Γ₀'} {Δ' = Γ₀} {A = A} r) {ρ} with eternal? A
... | yes eA =
  prod-ext
    -- fstᵐ: the sub-renaming, via `restrict-ren-mor r`
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ₀} {A} eA {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (restrict-ren-mor r))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (projᴱ-extᵉ-fst {Γ₀'} {A} eA {ρ})))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-assoc _ _ _)))))))))))))
    -- sndᵐ: `sndᵐ` passes through the `idᵐ` component on both sides
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ₀} {A} eA {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-identityˡ _)))
    (≈ᵐ-sym (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
            (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _))
                      (×-eternalᵒ-sndᵉ {Γ₀'} {A} eA {ρ})))))))))))
... | no  _  = restrict-ren-mor r
restrict-ren-mor (cong-⟨⟩-ren r) = restrict-ren-mor r
restrict-ren-mor (⟨⟩-ext-ren {A = A} et) with eternal? A
... | yes _  =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
... | no ¬et = ⊥-elim (¬et et)
-- the restriction drops the lock this introduces, so it restricts to `id-ren`
restrict-ren-mor (⟨⟩-ext-ctx _ _) =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))

-- Naturality of the eternal projection: it slides through a renaming, turning
-- into the restricted renaming. The variable case is `var-projᴱ`; the lock
-- case uses `restrict-ren-mor` to carry the restricted renaming past `extᵉ`.

projᴱ-nat : ∀ {Γ Γ'} → (r : Ren [] Γ' Γ)
          → projᴱ Γ ∘ᵐ ⟦ r ⟧ʳ ≈ᵐ ⟦ restrict-ren r ⟧ʳ ∘ᵐ projᴱ Γ'
projᴱ-nat id-ren =
  ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
projᴱ-nat (r₁ ∘ʳ r₂) =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-nat r₁))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (projᴱ-nat r₂))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
projᴱ-nat (wk-ren {A = A}) with eternal? A
... | yes _ = ≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)
... | no  _ = ≈ᵐ-sym (∘ᵐ-identityˡ _)
projᴱ-nat (var-ren {A = A} p x) with eternal? A
... | yes eA =
  ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
  (≈ᵐ-trans (⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _)
             , ≈ᵐ-trans (var-projᴱ eA x)
                        (∘ᵐ-congˡ (≈ᵐ-sym (var-morphism-unfoldᵉ eA (λ _ → ≾ᵣ-refl) (∈-ᴱ eA x)))) ⟩ᵐ-cong)
            (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))))
projᴱ-nat (⟨⟩-η-ren {Δ = Γ}) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-η-nat _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (Eternalᵒ.extᵉ-u (⟦ Γ ⟧ᴱ-Eternalᵒ))))
  (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id)
  (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))))))
projᴱ-nat (⟨⟩-η⁻¹-ren {Δ = Γ}) =
  ≈ᵐ-trans (εᵘ-nat _)
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.extᵉ-u (⟦ Γ ⟧ᴱ-Eternalᵒ))))
            (≈ᵐ-sym (∘ᵐ-identityˡ _)))
projᴱ-nat (⟨⟩-μ-ren {Γ} {ρ} {ρ'}) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-μ-nat _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (Eternalᵒ.extᵉ-μ (⟦ Γ ⟧ᴱ-Eternalᵒ)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-identityˡ _)))))))
projᴱ-nat (⟨⟩-≤-ren {Δ = Γ} rel) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-nat _ rel))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (Eternalᵒ.extᵉ-≤ (⟦ Γ ⟧ᴱ-Eternalᵒ) rel))
            (≈ᵐ-sym (∘ᵐ-identityˡ _)))))
projᴱ-nat (cong-∷-ren {A = A} r) with eternal? A
... | yes _ =
  ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
  (≈ᵐ-trans (mapˣᵐ-cong (projᴱ-nat r) ≈ᵐ-refl)
            (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-nat r))
            (∘ᵐ-assoc _ _ _))))
projᴱ-nat (cong-⟨⟩-ren {ρ = ρ} r) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (projᴱ-nat r)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (restrict-ren-mor r))
            (∘ᵐ-assoc _ _ _))))))
projᴱ-nat (⟨⟩-ext-ren {Γ} {A} et) with eternal? A
... | yes eA = ≈ᵐ-trans (prod-ext FST SND) (≈ᵐ-sym (∘ᵐ-identityˡ _))
  where
    -- fstᵐ: the `Γ`-projection factor, `strᵉ` cancelled against `⟨ρ⟩ᶠ fstᵐ`
    FST : fstᵐ ∘ᵐ ((Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eA))
                     ∘ᵐ ⟨ _ ⟩ᶠ (mapˣᵐ (projᴱ Γ) idᵐ)) ∘ᵐ eternalᵛ-strᵉ et)
        ≈ᵐ fstᵐ ∘ᵐ mapˣᵐ (projᴱ-extᵉ Γ ∘ᵐ ⟨ _ ⟩ᶠ (projᴱ Γ)) idᵐ
    FST =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ} {A} eA)))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _))))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))
      (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (strᵉ-past-fstᵐ et (projᴱ-extᵉ Γ ∘ᵐ ⟨ _ ⟩ᶠ (projᴱ Γ)))
                (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _))))))))))
    -- sndᵐ: the eternal factor, `strᵉ` cancelled against `⟨ρ⟩ᶠ sndᵐ` via extᵉ
    SND : sndᵐ ∘ᵐ ((Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eA))
                     ∘ᵐ ⟨ _ ⟩ᶠ (mapˣᵐ (projᴱ Γ) idᵐ)) ∘ᵐ eternalᵛ-strᵉ et)
        ≈ᵐ sndᵐ ∘ᵐ mapˣᵐ (projᴱ-extᵉ Γ ∘ᵐ ⟨ _ ⟩ᶠ (projᴱ Γ)) idᵐ
    SND =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ} {A} eA)))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _))))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-identityˡ _))))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr eA et))
      (≈ᵐ-trans (eternalᵛ-strᵉ-sndᵐ et)
                (≈ᵐ-sym (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))))))))))
... | no ¬et = ⊥-elim (¬et et)
-- the lock this introduces is dropped by the restriction, so the restricted
-- renaming is the identity and the square is `ec-projᴱ-extᵉ`
projᴱ-nat (⟨⟩-ext-ctx _ ecΓ) =
  ≈ᵐ-trans (ec-projᴱ-extᵉ ecΓ) (≈ᵐ-sym (∘ᵐ-identityˡ _))

