------------------------------------------------------------------------
-- Interpretation of context renamings.                                --
--                                                                    --
-- A renaming `Ren Γ Γ'` rewrites a `Γ`-typed term into a `Γ'`-typed    --
-- term (`V-rename`/`C-rename`), so on environments it runs             --
-- contravariantly, as a reindexing `⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ`. Each       --
-- constructor is a structural map of the model: weakening projects      --
-- (`fstᵐ`), a variable renaming contracts (`⟨ idᵐ , var-morphism … ⟩ᵐ`), --
-- and the lock renamings are exactly the context modality's             --
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

open Category Cat
open Past Pst
open GroundEternal GE
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE

-- The reindexing morphism of a renaming (contravariant in the context).

⟦_⟧ʳ : ∀ {Γ Γ'} → Ren Γ Γ' → ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
⟦ id-ren ⟧ʳ              = idᵐ
⟦ r₂ ∘ʳ r₁ ⟧ʳ            = ⟦ r₁ ⟧ʳ ∘ᵐ ⟦ r₂ ⟧ʳ
⟦ wk-ren ⟧ʳ              = fstᵐ
⟦ var-ren p x ⟧ʳ         = ⟨ idᵐ , var-morphism p x ⟩ᵐ
⟦ ⟨⟩-η-ren ⟧ʳ            = η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ          = εᵘ
⟦ ⟨⟩-μ-ren {Γ} {ρ} {ρ'} ⟧ʳ = μ {⟦ Γ ⟧ᶜᵗˣ} {ρ'} {ρ}
⟦ ⟨⟩-≤-ren rel ⟧ʳ        = ⟨⟩-≤ rel
⟦ cong-∷-ren r ⟧ʳ        = mapˣᵐ ⟦ r ⟧ʳ idᵐ
⟦ cong-⟨⟩-ren {ρ = ρ} r ⟧ʳ = ⟨ ρ ⟩ᶠ ⟦ r ⟧ʳ
⟦ ⟨⟩-ext-ren et ⟧ʳ       = Eternalᵒ.strᵉ (eternalᵛ-Eternalᵒ et)

-- Transport along an equality of *grades* is the grade relaxation at the
-- reflexive witness.

eq-ren-grade : ∀ {Γ ρ ρ'} → (g : ρ ≡ ρ')
             → ⟦ eq-ren (cong (Γ ⟨_⟩) g) ⟧ʳ ≈ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᶜᵗˣ} (≾ᵣ-reflexive (sym g))
eq-ren-grade refl =
  ≈ᵐ-sym (≈ᵐ-trans (⟨⟩-≤-irr _ ≾ᵣ-refl) ⟨⟩-≤-refl)

-- Transport renamings along a context equality commute with the context
-- formers, with each other, and with themselves (both sides are the identity
-- once the equality is `refl`; `eq-ren-irr` is UIP).

eq-ren-irr : ∀ {Γ Γ'} → (e e' : Γ ≡ Γ') → ⟦ eq-ren e ⟧ʳ ≈ᵐ ⟦ eq-ren e' ⟧ʳ
eq-ren-irr e e' = ≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (uip {p = e} {q = e'}))

eq-ren-∷ : ∀ {Γ Γ' B} → (e : Γ ≡ Γ')
         → ⟦ eq-ren (cong (_∷ B) e) ⟧ʳ ≈ᵐ mapˣᵐ ⟦ eq-ren e ⟧ʳ idᵐ
eq-ren-∷ refl = ≈ᵐ-sym mapˣᵐ-idᵐ

eq-ren-⟨⟩ : ∀ {Γ Γ' ρ} → (e : Γ ≡ Γ')
          → ⟦ eq-ren (cong (_⟨ ρ ⟩) e) ⟧ʳ ≈ᵐ ⟨ ρ ⟩ᶠ ⟦ eq-ren e ⟧ʳ
eq-ren-⟨⟩ refl = ≈ᵐ-sym ⟨⟩-idᵐ

eq-ren-trans : ∀ {Γ Γ' Γ''} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ'')
             → ⟦ eq-ren (trans e e') ⟧ʳ ≈ᵐ ⟦ eq-ren e ⟧ʳ ∘ᵐ ⟦ eq-ren e' ⟧ʳ
eq-ren-trans refl refl = ≈ᵐ-sym (∘ᵐ-identityˡ _)

-- EXTENDING AN ENVIRONMENT MORPHISM THROUGH A CONTEXT SUFFIX
--
-- `ext Γ Γ' Θ` weakens a morphism `⟦ Γ ⟧ → ⟦ Γ' ⟧` past everything a suffix
-- `Θ` binds. It is the semantic counterpart of the syntactic `cong-ren`
-- (`cong-ren-ext` below), generalised from renaming denotations to arbitrary
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

-- `ext` on a renaming's denotation is that renaming's `cong-ren`.

cong-ren-ext : ∀ {Γ Γ'} → (r : Ren Γ Γ') → (Θ : Ctx)
             → ⟦ cong-ren {Γ'' = Θ} r ⟧ʳ ≈ᵐ ext Γ' Γ Θ ⟦ r ⟧ʳ
cong-ren-ext r []        = ≈ᵐ-refl
cong-ren-ext r (Θ ∷ A)   = mapˣᵐ-cong (cong-ren-ext r Θ) ≈ᵐ-refl
cong-ren-ext r (Θ ⟨ ρ ⟩) = ⟨⟩-congᶠ (cong-ren-ext r Θ)

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

var-proj-nat : ∀ {Γ Γ' A ρ} → (r : Ren Γ Γ') → (x : A ∈[ ρ ] Γ) → (¬et : ¬ Eternal A)
             → ⟨⟩-≤ (proj₁ (proj₂ (var-rename r x)) ¬et)
                 ∘ᵐ var-proj (proj₂ (proj₂ (var-rename r x)))
               ≈ᵐ var-proj x ∘ᵐ ⟦ r ⟧ʳ
var-proj-nat id-ren x ¬et =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _)))
var-proj-nat (r₂ ∘ʳ r₁) x ¬et with var-rename r₁ x | var-proj-nat r₁ x ¬et | var-rename r₂ (proj₂ (proj₂ (var-rename r₁ x))) | var-proj-nat r₂ (proj₂ (proj₂ (var-rename r₁ x))) ¬et
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

var-proj-nat-eternal : ∀ {Γ Γ' A ρ} → (et : Eternal A) → (r : Ren Γ Γ') → (x : A ∈[ ρ ] Γ)
    → eternalᵛ-extᵉ et {proj₁ (var-rename r x)} ∘ᵐ var-proj (proj₂ (proj₂ (var-rename r x)))
      ≈ᵐ (eternalᵛ-extᵉ et {ρ} ∘ᵐ var-proj x) ∘ᵐ ⟦ r ⟧ʳ
var-proj-nat-eternal et id-ren x =
  ≈ᵐ-sym (∘ᵐ-identityʳ _)
var-proj-nat-eternal et (r₂ ∘ʳ r₁) x
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

var-morphism-nat : ∀ {Γ Γ' A ρ} → (r : Ren Γ Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ ] Γ)
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

-- Extensionality for maps into a product: agreeing on both projections.

prod-ext : ∀ {X A B} {h k : X →ᵐ A ×ᵐ B}
         → fstᵐ ∘ᵐ h ≈ᵐ fstᵐ ∘ᵐ k → sndᵐ ∘ᵐ h ≈ᵐ sndᵐ ∘ᵐ k → h ≈ᵐ k
prod-ext pf ps =
  ≈ᵐ-trans (⟨⟩ᵐ-unique _ _ _ ≈ᵐ-refl ≈ᵐ-refl)
           (≈ᵐ-sym (⟨⟩ᵐ-unique _ _ _ (≈ᵐ-sym pf) (≈ᵐ-sym ps)))

-- The interpretation of a *restricted* renaming is a morphism of eternal
-- objects: it commutes with the eternal extractions of its (eternal) source
-- and target restrictions. Proved by recursion on the renaming; the eternal
-- variable case is exactly `eternal-mor`.

restrict-ren-mor : ∀ {Γ Γ'} → (r : Ren Γ Γ') → ∀ {ρ}
                 → projᴱ-extᵉ Γ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ ⟦ restrict-ren r ⟧ʳ
                 ≈ᵐ ⟦ restrict-ren r ⟧ʳ ∘ᵐ projᴱ-extᵉ Γ' {ρ}
restrict-ren-mor id-ren =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-ren-mor (r₂ ∘ʳ r₁) =
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
restrict-ren-mor (var-ren {Γ = Γ₀} {A = A} p x) {ρ} with eternal? A
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
restrict-ren-mor (cong-∷-ren {Γ = Γ₀} {Γ' = Γ₀'} {A = A} r) {ρ} with eternal? A
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

-- Naturality of `splitᴱ` under an ambient renaming: the renaming acts on the
-- eternal base (`restrict-ren`) while the split isolates it, so the two commute.
-- Recursion on the extension; the lock case is `costrᵉ-nat` fed by the eternal
-- morphism `restrict-ren-mor`, the `∷` case is `swap₂₃-nat`.

-- `splitᴱ` slides through a renaming — the renaming instance of `splitᴰ-nat-gen`
-- with base map `⟦ restrict-ren r ⟧ʳ` (its morphism law is `restrict-ren-mor`)
-- and lift `⟦ cong-ren (restrict-ren r) ⟧ʳ`, whose recursion holds definitionally
-- (`⟦ cong-ren {[]} ⟧ = ⟦ − ⟧`, `⟦ cong-∷-ren ⟧ = mapˣᵐ _ idᵐ`, `⟦ cong-⟨⟩-ren ⟧ = ⟨_⟩ᶠ`).
splitᴱ-nat : ∀ {Γ Γ'} → (r : Ren Γ Γ') → (Γ'x : Ctx)
           → splitᴱ Γ Γ'x ∘ᵐ ⟦ cong-ren {Γ'' = Γ'x} (restrict-ren r) ⟧ʳ
           ≈ᵐ mapˣᵐ idᵐ ⟦ restrict-ren r ⟧ʳ ∘ᵐ splitᴱ Γ' Γ'x
splitᴱ-nat {Γ} {Γ'} r =
  splitᴰ-nat-gen (⟦ Γ ⟧ᴱ-Eternalᵒ) (⟦ Γ' ⟧ᴱ-Eternalᵒ)
    ⟦ restrict-ren r ⟧ʳ (restrict-ren-mor r)
    (λ Γ'x → ⟦ cong-ren {Γ'' = Γ'x} (restrict-ren r) ⟧ʳ)
    ≈ᵐ-refl (λ _ _ → ≈ᵐ-refl) (λ _ _ → ≈ᵐ-refl)

splitᴱ⁻¹-nat : ∀ {Γ Γ'} → (r : Ren Γ Γ') → (Γ'x : Ctx)
             → ⟦ cong-ren {Γ'' = Γ'x} (restrict-ren r) ⟧ʳ ∘ᵐ splitᴱ⁻¹ Γ' Γ'x
             ≈ᵐ splitᴱ⁻¹ Γ Γ'x ∘ᵐ mapˣᵐ idᵐ ⟦ restrict-ren r ⟧ʳ
splitᴱ⁻¹-nat {Γ} {Γ'} r Γ'x =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (splitᴱ⁻¹-iso Γ Γ'x)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (splitᴱ-nat r Γ'x)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (splitᴱ-iso Γ' Γ'x)))
            (∘ᵐ-congʳ (∘ᵐ-identityʳ _))))))))

-- The lift `_⋉_` commutes with an ambient renaming: it acts on the extension,
-- the renaming on the base, so they pass each other. This is what carries
-- `CtxUniformʰ` through `renᶜ`.

⋉-ren : ∀ {Γ Γ' Γ'a Γ'b} → (r : Ren Γ Γ') → (ρ : ⟦ Γ'a ⟧ᶜᵗˣ →ᵐ ⟦ Γ'b ⟧ᶜᵗˣ)
      → ⟦ cong-ren {Γ'' = Γ'b} (restrict-ren r) ⟧ʳ ∘ᵐ _⋉_ Γ' {Γ'a} {Γ'b} ρ
      ≈ᵐ _⋉_ Γ {Γ'a} {Γ'b} ρ ∘ᵐ ⟦ cong-ren {Γ'' = Γ'a} (restrict-ren r) ⟧ʳ
⋉-ren {Γ} {Γ'} {Γ'a} {Γ'b} r ρ =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (splitᴱ⁻¹-nat r Γ'b))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ mid-comm))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (splitᴱ-nat r Γ'a))))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))
  where
    mid-comm = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
               (≈ᵐ-trans (mapˣᵐ-cong (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _)))
                                     (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))))
                         (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)))

-- `⋉-ren` lifted through the clause-context shape `mapˣᵐ (mapˣᵐ _ idᵐ) idᵐ`
-- (parameter and continuation factors ride along untouched). This is the form
-- `ren-clauses-ctxuniform` consumes.
-- A commutation of two maps lifted through the clause-context shape
-- `mapˣᵐ (mapˣᵐ _ idᵐ) idᵐ` (parameter and continuation factors ride along).
-- Used to carry both the renaming and the substitution base-commutations up to
-- the shape `CtxUniformʰ`/`ren-clauses-ctxuniform`/`subst-clauses-ctxuniform` consume.
mapˣ²-comm : ∀ {A B C D P Q} {g : C →ᵐ D} {f : A →ᵐ C} {f' : B →ᵐ D} {g' : A →ᵐ B}
           → g ∘ᵐ f ≈ᵐ f' ∘ᵐ g'
           → mapˣᵐ (mapˣᵐ g (idᵐ {P})) (idᵐ {Q}) ∘ᵐ mapˣᵐ (mapˣᵐ f idᵐ) idᵐ
           ≈ᵐ mapˣᵐ (mapˣᵐ f' idᵐ) idᵐ ∘ᵐ mapˣᵐ (mapˣᵐ g' idᵐ) idᵐ
mapˣ²-comm comm =
  ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
  (≈ᵐ-trans (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong comm (∘ᵐ-identityˡ _)))
                        (∘ᵐ-identityˡ _))
  (≈ᵐ-sym (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
          (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                (mapˣᵐ-cong ≈ᵐ-refl (∘ᵐ-identityˡ _)))
                      (∘ᵐ-identityˡ _)))))

⋉-ren² : ∀ {Γ Γ' Γ'a Γ'b} {P Q : Obj} → (r : Ren Γ Γ') → (ρ : ⟦ Γ'a ⟧ᶜᵗˣ →ᵐ ⟦ Γ'b ⟧ᶜᵗˣ)
       → mapˣᵐ (mapˣᵐ ⟦ cong-ren {Γ'' = Γ'b} (restrict-ren r) ⟧ʳ (idᵐ {P})) (idᵐ {Q})
           ∘ᵐ mapˣᵐ (mapˣᵐ (_⋉_ Γ' {Γ'a} {Γ'b} ρ) idᵐ) idᵐ
       ≈ᵐ mapˣᵐ (mapˣᵐ (_⋉_ Γ {Γ'a} {Γ'b} ρ) idᵐ) idᵐ
           ∘ᵐ mapˣᵐ (mapˣᵐ ⟦ cong-ren {Γ'' = Γ'a} (restrict-ren r) ⟧ʳ idᵐ) idᵐ
⋉-ren² {Γ'a = Γ'a} {Γ'b = Γ'b} r ρ = mapˣ²-comm (⋉-ren {Γ'a = Γ'a} {Γ'b = Γ'b} r ρ)

-- The lift `⋉ᴰ` transported along a base equality `e : Δ ≡ Δ'` (with the two
-- eternal structures related by `e`, supplied by `Eternalᵒ-coh`): reindexing the
-- base by `eq-ren` commutes with the lift, since the lift is identity on the
-- base. A clean `J` on `e` — this is what carries `CtxUniformʰ` through a
-- non-eternal substitution, which retypes the ambient base along `Γ ᴱ ≡ Γ₀ ᴱ`.
⋉ᴰ-eq : (Δ Δ' : Ctx) → (eΔ : Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ) → (eΔ' : Eternalᵒ ⟦ Δ' ⟧ᶜᵗˣ)
      → (e : Δ ≡ Δ') → subst (λ Θ → Eternalᵒ ⟦ Θ ⟧ᶜᵗˣ) e eΔ ≡ eΔ'
      → (Γ'a Γ'b : Ctx) → (ρ : ⟦ Γ'a ⟧ᶜᵗˣ →ᵐ ⟦ Γ'b ⟧ᶜᵗˣ)
      → ⟦ eq-ren (cong (_++ᶜ Γ'b) e) ⟧ʳ ∘ᵐ ⋉ᴰ Δ' eΔ' {Γ'a} {Γ'b} ρ
      ≈ᵐ ⋉ᴰ Δ eΔ {Γ'a} {Γ'b} ρ ∘ᵐ ⟦ eq-ren (cong (_++ᶜ Γ'a) e) ⟧ʳ
⋉ᴰ-eq Δ .Δ eΔ .eΔ refl refl Γ'a Γ'b ρ =
  ≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _))

-- Naturality of the eternal projection: it slides through a renaming, turning
-- into the restricted renaming. The variable case is `var-projᴱ`; the lock
-- case uses `restrict-ren-mor` to carry the restricted renaming past `extᵉ`.

projᴱ-nat : ∀ {Γ Γ'} → (r : Ren Γ Γ')
          → projᴱ Γ ∘ᵐ ⟦ r ⟧ʳ ≈ᵐ ⟦ restrict-ren r ⟧ʳ ∘ᵐ projᴱ Γ'
projᴱ-nat id-ren =
  ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
projᴱ-nat (r₂ ∘ʳ r₁) =
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
projᴱ-nat (⟨⟩-η-ren {Γ = Γ}) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-η-nat _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (Eternalᵒ.extᵉ-u (⟦ Γ ⟧ᴱ-Eternalᵒ))))
  (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id)
  (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))))))
projᴱ-nat (⟨⟩-η⁻¹-ren {Γ = Γ}) =
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
projᴱ-nat (⟨⟩-≤-ren {Γ = Γ} rel) =
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


-- ───────────────────────────────────────────────────────────────────────────
-- DENOTATIONS OF THE STRUCTURAL RENAMINGS
--
-- `exch-ren` (swap the two topmost variables), `bring-up` (extrude an eternal
-- variable out from under a suffix) and `contract` (fold the eternal prefix
-- `Γ ᴱ` back into `Γ`'s own variables).
-- ───────────────────────────────────────────────────────────────────────────

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- The exchange renaming swaps the two topmost variables.

exch-ren-mor : ∀ {Γ X Y}
             → ⟦ exch-ren {Γ} {X} {Y} ⟧ʳ ≈ᵐ ⟨ mapˣᵐ fstᵐ idᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ
exch-ren-mor {Γ} {X} {Y} =
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   var-morphism-Tl-∷ {Γ ∷ Y} {X} {Y} Hd _
                ∙ ∘ᵐ-congˡ (var-morphism-Hd {Γ} {Y} _) ⟩ᵐ-cong)
  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong

-- denotation of `bring-up`: split the extension off the eternal base, keep the
-- head `A`, and re-glue with `A` adjoined to the base.
bring-up-mor : ∀ {Δ A} → (eA : Eternal A) → (eΔ : Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ) → (Θ : Ctx)
  → ⟦ bring-up {Δ} {A} eA Θ ⟧ʳ
  ≈ᵐ splitᴰ⁻¹ (Δ ∷ A) (×-eternalᵒ eΔ (eternalᵛ-Eternalᵒ eA)) Θ
      ∘ᵐ ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ
         , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
bring-up-mor eA eΔ [] =
    ≈ᵐ-sym (
        ⟨⟩ᵐ-sndᵐ _ _
      ∙ ⟨   ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _) ∙ ∘ᵐ-identityˡ _
          , ≈ᵐ-refl ⟩ᵐ-cong
      ∙ ≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))
bring-up-mor {Δ} {A} eA eΔ (Θ ∷ B) =
    ∘ᵐ-congʳ (  exch-ren-mor {Δ ++ᶜ Θ} {A} {B}
              ∙ ⟨ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ ∘ᵐ-congˡ (mapˣᵐ-cong (bring-up-mor eA eΔ Θ) ≈ᵐ-refl)
  ∙ ∘ᵐ-congˡ (  mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym (∘ᵐ-identityˡ idᵐ))
              ∙ ≈ᵐ-sym (mapˣᵐ-∘ T idᵐ Pθ idᵐ))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ swapP
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    sd = splitᴰ Δ eΔ Θ
    T  = splitᴰ⁻¹ (Δ ∷ A) (×-eternalᵒ eΔ (eternalᵛ-Eternalᵒ eA)) Θ
    Pθ = ⟨ fstᵐ ∘ᵐ sd ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ sd ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    -- the two components of `splitᴰ Δ eΔ (Θ ∷ B)` = `swap₂₃ ∘ᵐ mapˣᵐ S idᵐ`
    sB-fst : fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ≈ᵐ ⟨ fstᵐ ∘ᵐ sd ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ
    sB-fst =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
      ∙ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
          , ⟨⟩ᵐ-sndᵐ _ _ ∙ ∘ᵐ-identityˡ _ ⟩ᵐ-cong
    sB-snd : sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ≈ᵐ sndᵐ ∘ᵐ sd ∘ᵐ fstᵐ
    sB-snd =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
    PΘB = ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ∘ᵐ fstᵐ
          , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    -- LHS → common form C = ⟨ ⟨ fstᵐ∘sd∘(fstᵐ∘fstᵐ) , ⟨ sndᵐ∘sd∘(fstᵐ∘fstᵐ) , sndᵐ ⟩ ⟩ , sndᵐ∘fstᵐ ⟩
    swapP-lhs : mapˣᵐ Pθ idᵐ ∘ᵐ swap₂₃
              ≈ᵐ ⟨ ⟨ fstᵐ ∘ᵐ sd ∘ᵐ fstᵐ ∘ᵐ fstᵐ
                   , ⟨ sndᵐ ∘ᵐ sd ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
                 , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ
    swapP-lhs =
        mapˣᵐ-∘⟨⟩ _ _ _ _
      ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
              , ⟨⟩ᵐ-∘ _ _ _
                ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                    , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong ⟩ᵐ-cong
        , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
    swapP : mapˣᵐ Pθ idᵐ ∘ᵐ swap₂₃ ≈ᵐ swap₂₃ ∘ᵐ PΘB
    swapP = swapP-lhs ∙ ≈ᵐ-sym
      (  ⟨⟩ᵐ-∘ _ _ _
       ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
           ∙ ⟨   -- (fstᵐ ∘ᵐ fstᵐ) ∘ᵐ PΘB → fstᵐ ∘ᵐ sd ∘ᵐ (fstᵐ ∘ᵐ fstᵐ)
                 ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
               ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ sB-fst)
               ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
               ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
               -- sndᵐ ∘ᵐ PΘB → ⟨ sndᵐ ∘ᵐ sd ∘ᵐ (fstᵐ ∘ᵐ fstᵐ) , sndᵐ ⟩
             , ⟨⟩ᵐ-sndᵐ _ _
               ∙ ⟨   ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ sB-snd
                   ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                 , ≈ᵐ-refl ⟩ᵐ-cong ⟩ᵐ-cong
           -- (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ PΘB → sndᵐ ∘ᵐ fstᵐ
         , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
           ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ sB-fst)
           ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _) ⟩ᵐ-cong)
bring-up-mor {Δ} {A} eA eΔ (Θ ⟨ ρ ⟩) =
    ∘ᵐ-congˡ (⟨⟩-congᶠ (bring-up-mor eA eΔ Θ))
  ∙ ∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ strP
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    eA' = eternalᵛ-Eternalᵒ eA
    Pθ  = ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ
          , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    PρΘ = ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ
          , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    refold1 : ⟨ ρ ⟩ᶠ (fstᵐ ∘ᵐ splitᴰ Δ eΔ Θ) ≈ᵐ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩)
    refold1 =
        ⟨⟩-∘ᵐ _ _
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _))
      ∙ ∘ᵐ-assoc _ _ _
    refold2 : Eternalᵒ.extᵉ eΔ ∘ᵐ ⟨ ρ ⟩ᶠ (sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ)
            ≈ᵐ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩)
    refold2 =
        ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))
      ∙ ∘ᵐ-assoc _ _ _
    comp1 : ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ (⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA')
          ≈ᵐ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ
    comp1 =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _))
      ∙ ∘ᵐ-congˡ (⟨⟩-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (Eternalᵒ.strᵉ-fstᵐ eA')
      ∙ ∘ᵐ-congˡ refold1
      ∙ ∘ᵐ-assoc _ _ _
    c2a : (Eternalᵒ.extᵉ eΔ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ)
            ∘ᵐ (⟨ ρ ⟩ᶠ ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ∘ᵐ Eternalᵒ.strᵉ eA')
        ≈ᵐ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ
    c2a =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (Eternalᵒ.strᵉ-fstᵐ eA'))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ refold2
      ∙ ∘ᵐ-assoc _ _ _
    c2b : (Eternalᵒ.extᵉ eA' ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ)
            ∘ᵐ (⟨ ρ ⟩ᶠ ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ∘ᵐ Eternalᵒ.strᵉ eA')
        ≈ᵐ sndᵐ
    c2b =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
      ∙ Eternalᵒ.strᵉ-sndᵐ eA'
    comp2 : (Eternalᵒ.extᵉ (×-eternalᵒ eΔ eA') ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ)
              ∘ᵐ (⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA')
          ≈ᵐ ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ
    comp2 =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
      ∙ ∘ᵐ-congˡ (×-eternalᵒ-extᵉ eΔ eA')
      ∙ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ c2a , c2b ⟩ᵐ-cong
    costrP : Eternalᵒ.costrᵉ (×-eternalᵒ eΔ eA') ∘ᵐ (⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA')
           ≈ᵐ PρΘ
    costrP = ⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ comp1 , comp2 ⟩ᵐ-cong
    strP : ⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA'
         ≈ᵐ Eternalᵒ.strᵉ (×-eternalᵒ eΔ eA') ∘ᵐ PρΘ
    strP =
        ≈ᵐ-sym (∘ᵐ-identityˡ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.costrᵉ-strᵉ (×-eternalᵒ eΔ eA')))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ costrP

-- The denotation of the eternal-prefix contraction `contract Γ : Ren (Γ ᴱ ++ᶜ Γ) Γ`:
-- pair the identity with `projᴱ Γ`, then `splitᴱ⁻¹` glues the eternal base back on.

-- the pure-cartesian reshuffle used in the non-eternal `∷` case
private
  cart-∷ : ∀ {Y B C} → (p : Y →ᵐ B)
         → mapˣᵐ ⟨ idᵐ , p ⟩ᵐ (idᵐ {C}) ≈ᵐ swap₂₃ ∘ᵐ ⟨ idᵐ , p ∘ᵐ fstᵐ ⟩ᵐ
  cart-∷ p =
      ⟨ ⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
    ∙ ≈ᵐ-sym
        (  ⟨⟩ᵐ-∘ _ _ _
         ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
             ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _
               , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong
           , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)

contract-mor : (Γ : Ctx) → ⟦ contract Γ ⟧ʳ ≈ᵐ splitᴱ⁻¹ Γ Γ ∘ᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ
contract-mor []        = ≈ᵐ-sym (⟨⟩ᵐ-sndᵐ idᵐ idᵐ)
contract-mor (Γ ∷ A) with eternal? A
-- TODO: the eternal head grows the base `Γ ᴱ → Γ ᴱ ∷ A`; needs a `bring-up`
-- denotation lemma (induction through `exch-ren` = `exch-ren-mor` and
-- `⟨⟩-ext-ren` = `strᵉ`) relating `splitᴰ⁻¹ (Γ ᴱ ∷ A) _ Γ` to `splitᴱ⁻¹ Γ Γ`.
... | yes eA =
    ∘ᵐ-congˡ (  ∘ᵐ-congˡ (mapˣᵐ-cong (bring-up-mor {Γ ᴱ} {A} eA (⟦ Γ ⟧ᴱ-Eternalᵒ) Γ) ≈ᵐ-refl)
              ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , var-morphism-Hd {Γ ᴱ ++ᶜ Γ} {A} _ ⟩ᵐ-cong))
  ∙ ∘ᵐ-congʳ (mapˣᵐ-cong (contract-mor Γ) ≈ᵐ-refl)
  ∙ rem-eternal
  where
    e' = ×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eA)
    T' = splitᴰ⁻¹ (Γ ᴱ ∷ A) e' Γ
    sg = splitᴱ Γ Γ
    K  = splitᴱ⁻¹ Γ Γ ∘ᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ
    P  = mapˣᵐ (projᴱ Γ) (idᵐ {⟦ A ⟧ᵛ})
    mK = mapˣᵐ K (idᵐ {⟦ A ⟧ᵛ})
    Pγ = ⟨ fstᵐ ∘ᵐ sg ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ sg ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ

    splitM : mapˣᵐ (T' ∘ᵐ Pγ) (idᵐ {⟦ A ⟧ᵛ})
           ≈ᵐ mapˣᵐ T' (idᵐ {⟦ A ⟧ᵛ}) ∘ᵐ mapˣᵐ Pγ (idᵐ {⟦ A ⟧ᵛ})
    splitM =
        mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym (∘ᵐ-identityˡ idᵐ))
      ∙ ≈ᵐ-sym (mapˣᵐ-∘ T' idᵐ Pγ idᵐ)

    -- the split/re-glue round trip collapses (`splitᴱ-iso`)
    sgK : sg ∘ᵐ K ≈ᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ
    sgK = ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (splitᴱ-iso Γ Γ) ∙ ∘ᵐ-identityˡ _

    fstK : fstᵐ ∘ᵐ mK ≈ᵐ K ∘ᵐ fstᵐ
    fstK = ⟨⟩ᵐ-fstᵐ _ _

    sndK : sndᵐ ∘ᵐ mK ≈ᵐ sndᵐ
    sndK = ⟨⟩ᵐ-sndᵐ _ _ ∙ ∘ᵐ-identityˡ _

    legA : (fstᵐ ∘ᵐ sg ∘ᵐ fstᵐ) ∘ᵐ mK ≈ᵐ fstᵐ
    legA =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ fstK)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ sgK)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
      ∙ ∘ᵐ-identityˡ _

    legB : (sndᵐ ∘ᵐ sg ∘ᵐ fstᵐ) ∘ᵐ mK ≈ᵐ projᴱ Γ ∘ᵐ fstᵐ
    legB =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ fstK)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ sgK)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)

    pgEq : Pγ ∘ᵐ mK ≈ᵐ ⟨ fstᵐ , P ⟩ᵐ
    pgEq =
        ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ legA
        ,   ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨ legB , sndK ⟩ᵐ-cong
          ∙ ≈ᵐ-sym (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong) ⟩ᵐ-cong

    wEq : (mapˣᵐ Pγ (idᵐ {⟦ A ⟧ᵛ}) ∘ᵐ ⟨ idᵐ , sndᵐ ⟩ᵐ) ∘ᵐ mK
        ≈ᵐ swap₂₃ ∘ᵐ ⟨ idᵐ , P ⟩ᵐ
    wEq =
        ∘ᵐ-congˡ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
      ∙ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ pgEq , sndK ⟩ᵐ-cong
      ∙ ≈ᵐ-sym
          (  ⟨⟩ᵐ-∘ _ _ _
           ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
               ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _
                   , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong
             , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)

    rem-eternal =
        ∘ᵐ-congˡ (∘ᵐ-congˡ splitM)
      ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ wEq
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
... | no ¬eA =
    mapˣᵐ-cong (contract-mor Γ) ≈ᵐ-refl
  ∙ mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym (∘ᵐ-identityˡ idᵐ))
  ∙ ≈ᵐ-sym (mapˣᵐ-∘ (splitᴱ⁻¹ Γ Γ) idᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ idᵐ)
  ∙ ∘ᵐ-congʳ (cart-∷ {C = ⟦ A ⟧ᵛ} (projᴱ Γ))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
contract-mor (Γ ⟨ ρ ⟩) =
    ⟨⟩-congᶠ (contract-mor Γ)
  ∙ ⟨⟩-∘ᵐ _ _
  ∙ ∘ᵐ-congʳ strident
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    e = ⟦ Γ ⟧ᴱ-Eternalᵒ
    q = projᴱ Γ
    costr-comp : Eternalᵒ.costrᵉ e {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ ⟨ idᵐ , q ⟩ᵐ
               ≈ᵐ ⟨ idᵐ , Eternalᵒ.extᵉ e ∘ᵐ ⟨ ρ ⟩ᶠ q ⟩ᵐ
    costr-comp =
        ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨   ≈ᵐ-sym (⟨⟩-∘ᵐ _ _) ∙ ⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩-idᵐ
          , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _) ∙ ⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)) ⟩ᵐ-cong
    strident : ⟨ ρ ⟩ᶠ ⟨ idᵐ , q ⟩ᵐ
             ≈ᵐ Eternalᵒ.strᵉ e {ρ} ∘ᵐ ⟨ idᵐ , Eternalᵒ.extᵉ e ∘ᵐ ⟨ ρ ⟩ᶠ q ⟩ᵐ
    strident =
        ≈ᵐ-sym (∘ᵐ-identityˡ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.costrᵉ-strᵉ e))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ costr-comp
