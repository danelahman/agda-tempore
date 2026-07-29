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
open import Syntax.Renamings.Equivalence S using (eternal?-yes)

open Category Cat
open Past Pst
open GroundEternal GE
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE

-- The reindexing morphism of a renaming (contravariant in the context).

-- An eternal context interprets to a graded `⟨_⟩`-algebra: `𝟙ᵐ` and `×ᵐ` are
-- eternal objects, and the entries are eternal by assumption. This is what a
-- lock-introducing renaming needs of the context standing to its left, and why
-- `⟨⟩-ext-ctx` alone constrains it.

ec-Eternalᵒ : ∀ {Γ} → EternalCtx Γ → Eternalᵒ ⟦ Γ ⟧ᶜᵗˣ
ec-Eternalᵒ ec-[]        = 𝟙-eternalᵒ
ec-Eternalᵒ (ec-∷ ec et) = ×-eternalᵒ (ec-Eternalᵒ ec) (eternalᵛ-Eternalᵒ et)

ec-extᵉ : ∀ {Γ} → EternalCtx Γ → ∀ {ρ} → ⟨ ρ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
ec-extᵉ ec = Eternalᵒ.extᵉ (ec-Eternalᵒ ec)

-- The extraction's two components, read off the product structure.

ec-extᵉ-fstᵐ : ∀ {Γ A} → (ec : EternalCtx Γ) → (et : Eternal A) → ∀ {ρ}
             → fstᵐ ∘ᵐ ec-extᵉ (ec-∷ ec et) {ρ} ≈ᵐ ec-extᵉ ec ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
ec-extᵉ-fstᵐ ec et =
  ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (ec-Eternalᵒ ec) (eternalᵛ-Eternalᵒ et)))
           (⟨⟩ᵐ-fstᵐ _ _)

ec-extᵉ-sndᵐ : ∀ {Γ A} → (ec : EternalCtx Γ) → (et : Eternal A) → ∀ {ρ}
             → sndᵐ ∘ᵐ ec-extᵉ (ec-∷ ec et) {ρ} ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ
ec-extᵉ-sndᵐ ec et =
  ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (ec-Eternalᵒ ec) (eternalᵛ-Eternalᵒ et)))
           (⟨⟩ᵐ-sndᵐ _ _)

-- Extraction undoes `η`, so an eternal variable at the head is the projection.

evar-Hd : ∀ {Γ A} → (et : Eternal A)
        → eternalᵛ-extᵉ et ∘ᵐ var-proj (Hd {A} {Γ}) ≈ᵐ sndᵐ
evar-Hd et =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et)) ⟨⟩-εᵘ∘η≡id))
            (∘ᵐ-identityˡ sndᵐ))

-- Extensionality for maps into a product: agreeing on both projections.

prod-ext : ∀ {X A B} {h k : X →ᵐ A ×ᵐ B}
         → fstᵐ ∘ᵐ h ≈ᵐ fstᵐ ∘ᵐ k → sndᵐ ∘ᵐ h ≈ᵐ sndᵐ ∘ᵐ k → h ≈ᵐ k
prod-ext pf ps =
  ≈ᵐ-trans (⟨⟩ᵐ-unique _ _ _ ≈ᵐ-refl ≈ᵐ-refl)
           (≈ᵐ-sym (⟨⟩ᵐ-unique _ _ _ (≈ᵐ-sym pf) (≈ᵐ-sym ps)))

-- THE ETERNAL PROJECTION OF AN ETERNAL CONTEXT IS AN ALGEBRA MORPHISM
--
-- `projᴱ Γ` carries the context's own `⟨_⟩`-algebra to that of its restriction.
-- Needed because `⟨⟩-ext-ctx` interprets to the former, and `restrict-ren` sends
-- it to the identity, so `projᴱ`-naturality at that rule is exactly this.

ec-projᴱ-extᵉ : ∀ {Γ} → (ec : EternalCtx Γ) → ∀ {ρ}
              → projᴱ Γ ∘ᵐ ec-extᵉ ec {ρ}
              ≈ᵐ projᴱ-extᵉ Γ ∘ᵐ ⟨ ρ ⟩ᶠ (projᴱ Γ)

ec-projᴱ-extᵉ ec-[] =
  ≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _)) (∘ᵐ-congʳ (≈ᵐ-sym ⟨⟩-idᵐ)))

ec-projᴱ-extᵉ (ec-∷ {Δ = Γ₀} {A = A} ec et) {ρ} rewrite eternal?-yes et =
  prod-ext
    -- both sides reach `projᴱ-extᵉ Γ₀ ∘ᵐ ⟨ ρ ⟩ᶠ (projᴱ Γ₀ ∘ᵐ fstᵐ)`
    (≈ᵐ-trans
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (ec-extᵉ-fstᵐ ec et))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (ec-projᴱ-extᵉ ec))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))))))))
      (≈ᵐ-sym
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ₀} {A} et))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
                  (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))))))))
    -- and both reach `eternalᵛ-extᵉ et ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ`
    (≈ᵐ-trans
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _)))
                (ec-extᵉ-sndᵐ ec et)))
      (≈ᵐ-sym
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ₀} {A} et))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
                  (∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))))))))

-- AN ETERNAL VARIABLE'S MORPHISM IS AN ALGEBRA MORPHISM
--
-- `extᵉ ∘ᵐ var-proj y`, which is `var-morphism` at an eternal type, carries the
-- context's `⟨_⟩`-algebra to the type's. This is what `⟨⟩-ext-ctx` needs of its
-- ambient: `extᵉ` has no naturality law, so only algebra morphisms commute with
-- it. Two cases, `EternalCtx` being lock-free.

ec-var-alg : ∀ {Γ A ρ σ} → (ec : EternalCtx Γ) → (et : Eternal A) → (y : A ∈[ ρ ] Γ)
           → eternalᵛ-extᵉ et ∘ᵐ ⟨ σ ⟩ᶠ (eternalᵛ-extᵉ et ∘ᵐ var-proj y)
           ≈ᵐ (eternalᵛ-extᵉ et ∘ᵐ var-proj y) ∘ᵐ ec-extᵉ ec {σ}

ec-var-alg (ec-∷ {Δ = Γ₀} ec et') et Hd =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (evar-Hd {Γ = Γ₀} et)))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))
  (≈ᵐ-trans (≈ᵐ-sym (ec-extᵉ-sndᵐ ec et'))
            (∘ᵐ-congˡ (≈ᵐ-sym (evar-Hd {Γ = Γ₀} et)))))

ec-var-alg (ec-∷ ec et') et (Tl-∷ y) =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (ec-var-alg ec et y))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (ec-extᵉ-fstᵐ ec et')))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))))

-- Renamings are interpreted at the empty ambient: that is where the language's
-- own renamings (`unbox`'s certificate) and every derived one live, `[] ᴱ`,
-- `cong-ren`, `restrict-ren` and `contract` all preserving it. An
-- ambient-indexed renaming reaches the semantics through `expose-ren-[]`.

⟦_⟧ʳ : ∀ {Γ Γ'} → Ren [] Γ Γ' → ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
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
⟦ ⟨⟩-ext-ctx _ ecΓ ⟧ʳ    = Eternalᵒ.extᵉ (ec-Eternalᵒ ecΓ)

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

cong-ren-ext : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (Θ : Ctx)
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

var-proj-nat : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (x : A ∈[ ρ ] Γ) → (¬et : ¬ Eternal A)
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

var-proj-nat-eternal : ∀ {Γ Γ' A ρ} → (et : Eternal A) → (r : Ren [] Γ Γ') → (x : A ∈[ ρ ] Γ)
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
-- Introducing a lock: `extᵉ-μ` splits the extraction across the new lock, and
-- `ec-var-alg` absorbs the outer half into the ambient's own extraction. This is
-- the case the ambient index exists for.
var-proj-nat-eternal et (⟨⟩-ext-ctx _ ecΓ) x =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (ec-var-alg ecΓ et x))))

var-morphism-nat : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ ] Γ)
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

restrict-ren-mor : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → ∀ {ρ}
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
restrict-ren-mor (cong-∷-ren {Δ = Γ₀} {Δ' = Γ₀'} {A = A} r) {ρ} with eternal? A
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

projᴱ-nat : ∀ {Γ Γ'} → (r : Ren [] Γ Γ')
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

-- The denotation of the eternal inclusion `ᴱ-ren Γ : Ren [] (Γ ᴱ) Γ` is the
-- eternal projection: the two are defined by the same `eternal?` recursion, the
-- lock case matching `extᵉ` against `⟨⟩-ext-ctx`. That case needs the two
-- eternal structures on `⟦ Γ ᴱ ⟧` — the one read off the `EternalCtx` witness
-- and the one `projᴱ` uses — to agree, which they do, by the same recursion.

ec-Eternalᵒ-ᴱ : (Γ : Ctx) → ec-Eternalᵒ (ᴱ-EternalCtx Γ) ≡ ⟦ Γ ⟧ᴱ-Eternalᵒ
ec-Eternalᵒ-ᴱ []        = refl
ec-Eternalᵒ-ᴱ (Γ ∷ A)   with eternal? A
... | yes et = cong (λ z → ×-eternalᵒ z (eternalᵛ-Eternalᵒ et)) (ec-Eternalᵒ-ᴱ Γ)
... | no  _  = ec-Eternalᵒ-ᴱ Γ
ec-Eternalᵒ-ᴱ (Γ ⟨ ρ ⟩) = ec-Eternalᵒ-ᴱ Γ

ᴱ-ren-mor : (Γ : Ctx) → ⟦ ᴱ-ren Γ ⟧ʳ ≈ᵐ projᴱ Γ
ᴱ-ren-mor []        = ≈ᵐ-refl
ᴱ-ren-mor (Γ ∷ A)   with eternal? A
... | yes _ = mapˣᵐ-cong (ᴱ-ren-mor Γ) ≈ᵐ-refl
... | no  _ = ∘ᵐ-congˡ (ᴱ-ren-mor Γ)
ᴱ-ren-mor (Γ ⟨ ρ ⟩) =
    ∘ᵐ-cong (≡→≈ᵐ (cong (λ eΓ → Eternalᵒ.extᵉ eΓ {ρ}) (ec-Eternalᵒ-ᴱ Γ)))
            (⟨⟩-congᶠ (ᴱ-ren-mor Γ))

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
-- an eternal head grows the base `Γ ᴱ → Γ ᴱ ∷ A`, which `bring-up-mor` carries
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
