------------------------------------------------------------------------
-- Eternal contexts as graded algebras, and eternal variables' morphisms.
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
module DenotationalSemantics.Interpretation.Renaming.Algebra
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
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨u≈⟩-unit; ⟨u≈⟩-counit; ⟨u≈⟩-counit-unit;
              ⟨u≈⟩-eternalᵒ; ⟨u≈⟩-eternalᵒ-extᵉ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE


-- The reindexing morphism of a renaming (covariant in the context).

-- An eternal context interprets to a graded `⟨_⟩`-algebra: `𝟙ᵐ` and `×ᵐ` are
-- eternal objects, and the entries are eternal by assumption. This is what a
-- lock-introducing renaming needs of the context standing to its left, and why
-- `⟨⟩-ext-ctx` alone constrains it.

ec-Eternalᵒ : ∀ {Γ} → EternalCtx Γ → Eternalᵒ ⟦ Γ ⟧ᶜᵗˣ
ec-Eternalᵒ ec-[]          = 𝟙-eternalᵒ
ec-Eternalᵒ (ec-∷ ec et)   = ×-eternalᵒ (ec-Eternalᵒ ec) (eternalᵛ-Eternalᵒ et)
ec-Eternalᵒ (ec-⟨⟩ q p ec) = ⟨u≈⟩-eternalᵒ q p (ec-Eternalᵒ ec)

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

-- A UNIT-EQUIVALENT LOCK IS INVISIBLE TO THE ETERNAL PROJECTION
--
-- `Γ ᴱ` drops the lock, so `projᴱ (Γ ⟨ ρ₀ ⟩)` and `projᴱ Γ` have the same
-- target, and the lock's unit/counit carry one to the other. Both directions
-- use that `⟦ Γ ᴱ ⟧`'s own extraction is `εᵘ` at the unit grade.

ec-projᴱ-unit : ∀ {ρ₀} → (Γ : Ctx) → (q : uᵣ ≾ᵣ ρ₀)
              → projᴱ (Γ ⟨ ρ₀ ⟩) ∘ᵐ ⟨u≈⟩-unit q ≈ᵐ projᴱ Γ
ec-projᴱ-unit Γ q =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-nat _ q)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-η-nat _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (Eternalᵒ.extᵉ-≤ (⟦ Γ ⟧ᴱ-Eternalᵒ) q))
  (≈ᵐ-trans (∘ᵐ-congˡ (Eternalᵒ.extᵉ-u (⟦ Γ ⟧ᴱ-Eternalᵒ)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id)
            (∘ᵐ-identityˡ _))))))))))

ec-projᴱ-counit : ∀ {ρ₀} → (Γ : Ctx) → (p : ρ₀ ≾ᵣ uᵣ)
                → projᴱ Γ ∘ᵐ ⟨u≈⟩-counit p ≈ᵐ projᴱ (Γ ⟨ ρ₀ ⟩)
ec-projᴱ-counit Γ p =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (εᵘ-nat _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-nat _ p))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.extᵉ-u (⟦ Γ ⟧ᴱ-Eternalᵒ))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (Eternalᵒ.extᵉ-≤ (⟦ Γ ⟧ᴱ-Eternalᵒ) p)))))))

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

ec-projᴱ-extᵉ (ec-⟨⟩ {Δ = Γ₀} q p ec) =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨u≈⟩-eternalᵒ-extᵉ q p (ec-Eternalᵒ ec)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (ec-projᴱ-unit Γ₀ q))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (ec-projᴱ-extᵉ ec))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (∘ᵐ-congʳ (⟨⟩-congᶠ (ec-projᴱ-counit Γ₀ p)))))))))

-- Crossing a unit-equivalent lock: the morphism of a variable under the lock is
-- the one below it, precomposed with the lock's counit.

ec-var-lock : ∀ {Γ A ρ' ρ₀} → (p : ρ₀ ≾ᵣ uᵣ) → (et : Eternal A)
            → (y : A ∈[ ρ' ] Γ)
            → eternalᵛ-extᵉ et ∘ᵐ var-proj (Tl-⟨⟩ {ρ = ρ₀} y)
            ≈ᵐ (eternalᵛ-extᵉ et ∘ᵐ var-proj y) ∘ᵐ ⟨u≈⟩-counit p
ec-var-lock p et y =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (≈ᵐ-sym (eternalᵛ-extᵉ-≤ et p))
                                  (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat _ p)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (εᵘ-nat _)))
            (∘ᵐ-assoc _ _ _)))))))))

-- AN ETERNAL VARIABLE'S MORPHISM IS AN ALGEBRA MORPHISM
--
-- `extᵉ ∘ᵐ var-proj y`, which is `var-morphism` at an eternal type, carries the
-- context's `⟨_⟩`-algebra to the type's. This is what `⟨⟩-ext-ctx` needs of its
-- ambient: `extᵉ` has no naturality law, so only algebra morphisms commute with
-- it. One case per `EternalCtx` former; the lock case crosses the lock with
-- its counit (`ec-var-lock`).

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

ec-var-alg (ec-⟨⟩ q p ec) et (Tl-⟨⟩ y) =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (ec-var-lock p et y)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (ec-var-alg ec et y))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨u≈⟩-eternalᵒ-extᵉ q p (ec-Eternalᵒ ec)))
      (≈ᵐ-trans (∘ᵐ-congˡ (ec-var-lock p et y))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨u≈⟩-counit-unit q p)))
                (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))))))))

-- Renamings are interpreted at the empty ambient: that is where the language's
-- own renamings (`unbox`'s certificate) and every derived one live, `[] ᴱ`,
-- `cong-ren` and `restrict-ren` all preserving it. An ambient-indexed renaming
-- reaches the semantics through `expose-ren-[]`.

⟦_⟧ʳ : ∀ {Γ Γ'} → Ren [] Γ Γ' → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ
⟦ id-ren ⟧ʳ              = idᵐ
⟦ r₂ ∘ʳ r₁ ⟧ʳ            = ⟦ r₂ ⟧ʳ ∘ᵐ ⟦ r₁ ⟧ʳ
⟦ wk-ren ⟧ʳ              = fstᵐ
⟦ var-ren p x ⟧ʳ         = ⟨ idᵐ , var-morphism p x ⟩ᵐ
⟦ ⟨⟩-η-ren ⟧ʳ            = η
⟦ ⟨⟩-η⁻¹-ren ⟧ʳ          = εᵘ
⟦ ⟨⟩-μ-ren {Γ} {ρ} {ρ'} ⟧ʳ = μ {⟦ Γ ⟧ᶜᵗˣ} {ρ'} {ρ}
⟦ ⟨⟩-≤-ren rel ⟧ʳ        = ⟨⟩-≤ rel
⟦ cong-∷-ren r ⟧ʳ        = mapˣᵐ ⟦ r ⟧ʳ idᵐ
⟦ cong-⟨⟩-ren {ρ = ρ} r ⟧ʳ = ⟨ ρ ⟩ᶠ ⟦ r ⟧ʳ
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

