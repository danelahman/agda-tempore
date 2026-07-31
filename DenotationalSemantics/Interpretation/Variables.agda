------------------------------------------------------------------------
-- Interpretation of variables.                                         --
--                                                                    --
-- A variable `x : A ∈[ ρ ] Γ` is projected through the context to the  --
-- context modality at its accumulated grade, `var-proj x :              --
-- ⟦ Γ ⟧ →ᵐ ⟨ ρ ⟩ᵒ ⟦ A ⟧`. It is then extracted to `⟦ A ⟧`: for a        --
-- non-eternal type this needs `ρ ≾ uᵣ` and uses the unit-graded counit   --
-- `εᵘ`; for an eternal type it uses the eternal extraction `extᵉ` at     --
-- the arbitrary grade `ρ`.                                              --
--                                                                    --
-- The `Eternalᵒ` structure of an eternal type is assembled by recursion   --
-- on the eternality witness from the per-former structure supplied by     --
-- `GroundEternal` (base types, `Unit`, `Empty`, and products). Landing in --
-- `Eternalᵒ` means the eternal laws — grade-uniformity `extᵉ-≤`, the unit --
-- grade `extᵉ-u`, and the `⟨_⟩`-algebra law `extᵉ-μ` — are inherited      --
-- rather than re-proved for each former.                                  --
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Variables
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

open import Syntax.Types S
open import Syntax.Contexts S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; ε)
open Past Pst
open Adjunction Adj using (ε⊣; ε⊣-≤; ε⊣-u)
open GroundEternal GE
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon

-- Project a variable through the context to the context modality.

var-proj : ∀ {A ρ Γ} → A ∈[ ρ ] Γ → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟨ ρ ⟩ᵒ ⟦ A ⟧ᵛ
var-proj Hd                    = η ∘ᵐ sndᵐ
var-proj (Tl-∷ x)              = var-proj x ∘ᵐ fstᵐ
var-proj (Tl-⟨⟩ {ρ = ρ} x)     = μ ∘ᵐ ⟨ ρ ⟩ᶠ (var-proj x)

-- The eternal structure of an eternal type's interpretation, assembled by
-- recursion on the eternality witness from the structure supplied for each
-- former by `GroundEternal`. Because this lands in `Eternalᵒ`, all the
-- eternal laws below are `Eternalᵒ` fields (or derived there), rather than
-- being re-proved by induction for each former.

eternalᵛ-Eternalᵒ : ∀ {A} → Eternal A → Eternalᵒ ⟦ A ⟧ᵛ
eternalᵛ-Eternalᵒ (Baseₑ b eb)   = ⟦ b ⟧ᵇᵉ eb
eternalᵛ-Eternalᵒ Unitₑ          = 𝟙-eternalᵒ
eternalᵛ-Eternalᵒ Emptyₑ         = 𝟘-eternalᵒ
eternalᵛ-Eternalᵒ (et₁ |×|ₑ et₂) =
  ×-eternalᵒ (eternalᵛ-Eternalᵒ et₁) (eternalᵛ-Eternalᵒ et₂)

-- Eternal extraction at an arbitrary grade.

eternalᵛ-extᵉ : ∀ {A} → Eternal A → ∀ {ρ} → ⟨ ρ ⟩ᵒ ⟦ A ⟧ᵛ →ᵐ ⟦ A ⟧ᵛ
eternalᵛ-extᵉ et = Eternalᵒ.extᵉ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction is uniform in the grade, is the possibility counit
-- `εᵘ` at the unit grade, and is a graded `⟨_⟩`-algebra.

eternalᵛ-extᵉ-≤ : ∀ {A} → (et : Eternal A) → ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ᵣ ρ₂)
                → eternalᵛ-extᵉ et {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ eternalᵛ-extᵉ et {ρ₁}
eternalᵛ-extᵉ-≤ et = Eternalᵒ.extᵉ-≤ (eternalᵛ-Eternalᵒ et)

eternalᵛ-extᵉ-u : ∀ {A} → (et : Eternal A) → eternalᵛ-extᵉ et {uᵣ} ≈ᵐ εᵘ
eternalᵛ-extᵉ-u et = Eternalᵒ.extᵉ-u (eternalᵛ-Eternalᵒ et)

eternalᵛ-extᵉ-μ : ∀ {A} → (et : Eternal A) → ∀ {ρ₁ ρ₂}
                → eternalᵛ-extᵉ et {ρ₂ ·ᵣ ρ₁} ∘ᵐ μ {⟦ A ⟧ᵛ} {ρ₁} {ρ₂}
                ≈ᵐ eternalᵛ-extᵉ et {ρ₁} ∘ᵐ ⟨ ρ₁ ⟩ᶠ (eternalᵛ-extᵉ et {ρ₂})
eternalᵛ-extᵉ-μ et = Eternalᵒ.extᵉ-μ (eternalᵛ-Eternalᵒ et)

-- The eternal `⟨_⟩`-strength at an arbitrary grade, and its β-rules reading
-- back the two factors. Used to interpret `⟨⟩-ext-ren` (extruding an eternal
-- variable past a lock).

eternalᵛ-strᵉ : ∀ {A} → (et : Eternal A) → ∀ {ρ X} → ⟨ ρ ⟩ᵒ X ×ᵐ ⟦ A ⟧ᵛ →ᵐ ⟨ ρ ⟩ᵒ (X ×ᵐ ⟦ A ⟧ᵛ)
eternalᵛ-strᵉ et = Eternalᵒ.strᵉ (eternalᵛ-Eternalᵒ et)

eternalᵛ-strᵉ-fstᵐ : ∀ {A} → (et : Eternal A) → ∀ {ρ X}
                   → ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ eternalᵛ-strᵉ et {ρ} {X} ≈ᵐ fstᵐ
eternalᵛ-strᵉ-fstᵐ et = Eternalᵒ.strᵉ-fstᵐ (eternalᵛ-Eternalᵒ et)

eternalᵛ-strᵉ-sndᵐ : ∀ {A} → (et : Eternal A) → ∀ {ρ X}
                   → eternalᵛ-extᵉ et ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ eternalᵛ-strᵉ et {ρ} {X} ≈ᵐ sndᵐ
eternalᵛ-strᵉ-sndᵐ et = Eternalᵒ.strᵉ-sndᵐ (eternalᵛ-Eternalᵒ et)

-- Eternal extraction does not depend on how eternality was established
-- (`Eternal` is a property — see `Syntax.Types.eternal-irrelevant`).

eternalᵛ-extᵉ-irr : ∀ {A} → (et et' : Eternal A) → ∀ {ρ}
                  → eternalᵛ-extᵉ et {ρ} ≈ᵐ eternalᵛ-extᵉ et' {ρ}
eternalᵛ-extᵉ-irr et et' with eternal-irrelevant et et'
... | refl = ≈ᵐ-refl

-- The morphism interpreting a variable: project, then extract.

var-morphism : ∀ {Γ A ρ} → (¬ Eternal A → ρ ≾ᵣ uᵣ) → A ∈[ ρ ] Γ
             → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
var-morphism {A = A} f x with eternal? A
... | yes et = eternalᵛ-extᵉ et ∘ᵐ var-proj x
... | no ¬et = εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj x

-- The eternal restriction of a context interprets to an *eternal* object,
-- assembled by recursion following `_ᴱ`: `[]` and locks give `𝟙`/nothing, an
-- eternal variable a factor with its own eternal structure, a non-eternal
-- variable nothing. This is what a handler's eternal parameter `⟦ Γ ᴱ ⟧` is.

⟦_⟧ᴱ-Eternalᵒ : (Γ : Ctx) → Eternalᵒ ⟦ Γ ᴱ ⟧ᶜᵗˣ
⟦ [] ⟧ᴱ-Eternalᵒ      = 𝟙-eternalᵒ
⟦ Γ ∷ A ⟧ᴱ-Eternalᵒ   with eternal? A
... | yes et = ×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)
... | no  _  = ⟦ Γ ⟧ᴱ-Eternalᵒ
⟦ Γ ⟨ ρ ⟩ ⟧ᴱ-Eternalᵒ = ⟦ Γ ⟧ᴱ-Eternalᵒ

-- The eternal structure depends only on `Γ ᴱ`: restricting the context again
-- (`ᴱ-idem`) does not change it. Proved at the `≡` level by pushing `subst`
-- through the shared constructor `×-eternalᵒ` (`push-∷`), so the `≈ᵐ`-valued law
-- fields are never inspected — no setoid equality of `Eternalᵒ` records needed.
-- This is what bridges `⟦ Γ ⟧ᴱ` and `⟦ Γ₀ ⟧ᴱ` when a non-eternal substitution
-- retypes a handler along `Γ ᴱ ≡ Γ₀ ᴱ`.

private
  -- Homogeneous unfold of the eternal structure at an eternal `∷` (shares the
  -- internal `eternal?`, so no transport); the witness irrelevance is `eternal-
  -- irrelevant`.
  ⟦∷⟧ᴱ-yes : ∀ {Δ A} → (et : Eternal A)
           → subst (λ Θ → Eternalᵒ ⟦ Θ ⟧ᶜᵗˣ) (ᴱ-∷-keep {Δ} et) (⟦ Δ ∷ A ⟧ᴱ-Eternalᵒ)
           ≡ ×-eternalᵒ (⟦ Δ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)
  ⟦∷⟧ᴱ-yes {Δ} {A} et with eternal? A
  ... | yes et' = cong (λ q → ×-eternalᵒ (⟦ Δ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ q))
                       (eternal-irrelevant et' et)
  ... | no ¬et  = ⊥-elim (¬et et)

  -- `subst` past the `×-eternalᵒ` constructor on the first factor.
  push-∷ : ∀ {Δ Δ' A} → (et : Eternal A) → (e : Δ ≡ Δ') → (p : Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ)
         → subst (λ Θ → Eternalᵒ ⟦ Θ ⟧ᶜᵗˣ) (cong (_∷ A) e) (×-eternalᵒ p (eternalᵛ-Eternalᵒ et))
         ≡ ×-eternalᵒ (subst (λ Θ → Eternalᵒ ⟦ Θ ⟧ᶜᵗˣ) e p) (eternalᵛ-Eternalᵒ et)
  push-∷ et refl p = refl

⟦⟧ᴱ-idem : (Γ : Ctx) → (e : (Γ ᴱ) ᴱ ≡ Γ ᴱ)
         → subst (λ Δ → Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ) e (⟦ Γ ᴱ ⟧ᴱ-Eternalᵒ) ≡ ⟦ Γ ⟧ᴱ-Eternalᵒ
⟦⟧ᴱ-idem [] e rewrite uip {p = e} {q = refl} = refl
⟦⟧ᴱ-idem (Γ ∷ A) e with eternal? A
... | yes et =
  let m  = λ Δ → Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ
      k  = ᴱ-∷-keep {Γ ᴱ} et
      c  = cong (_∷ A) (ᴱ-idem Γ)
  in
  trans (cong (λ ee → subst m ee (⟦ Γ ᴱ ∷ A ⟧ᴱ-Eternalᵒ)) (uip {p = e} {q = trans k c}))
   (trans (sym (subst-subst k {y≡z = c}))
   (trans (cong (subst m c) (⟦∷⟧ᴱ-yes {Γ ᴱ} et))
   (trans (push-∷ et (ᴱ-idem Γ) (⟦ Γ ᴱ ⟧ᴱ-Eternalᵒ))
          (cong (λ z → ×-eternalᵒ z (eternalᵛ-Eternalᵒ et)) (⟦⟧ᴱ-idem Γ (ᴱ-idem Γ))))))
... | no  _ = ⟦⟧ᴱ-idem Γ e
⟦⟧ᴱ-idem (Γ ⟨ ρ ⟩) e = ⟦⟧ᴱ-idem Γ e

private
  subst-cong : ∀ {ℓ ℓ'} {A B : Set ℓ} → (P : B → Set ℓ') → (f : A → B)
             → {x y : A} → (e : x ≡ y) → (p : P (f x))
             → subst P (cong f e) p ≡ subst (λ a → P (f a)) e p
  subst-cong P f refl p = refl

-- The eternal projection: discard the non-eternal / time-passed part of the
-- context, keeping the eternal skeleton. Under a lock it uses the eternal
-- extraction `extᵉ` of the (eternal) restricted context.

projᴱ : (Γ : Ctx) → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
projᴱ []        = idᵐ
projᴱ (Γ ∷ A)   with eternal? A
... | yes _ = mapˣᵐ (projᴱ Γ) idᵐ
... | no  _ = projᴱ Γ ∘ᵐ fstᵐ
projᴱ (Γ ⟨ ρ ⟩) = Eternalᵒ.extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) ∘ᵐ ⟨ ρ ⟩ᶠ (projᴱ Γ)

-- The eternal extraction of a restricted context (its `Eternalᵒ` structure).

projᴱ-extᵉ : (Γ : Ctx) → ∀ {ρ} → ⟨ ρ ⟩ᵒ ⟦ Γ ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
projᴱ-extᵉ Γ {ρ} = Eternalᵒ.extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) {ρ}

-- `fstᵐ`/`sndᵐ` intertwine the extraction of an eternal `∷`-extension with the
-- extractions of the two factors (from `×-eternalᵒ-extᵉ`).

projᴱ-extᵉ-fst : ∀ {Γ A} → (et : Eternal A) → ∀ {ρ}
               → fstᵐ ∘ᵐ Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)) {ρ}
               ≈ᵐ projᴱ-extᵉ Γ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
projᴱ-extᵉ-fst {Γ} et =
  ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)))
           (⟨⟩ᵐ-fstᵐ _ _)

×-eternalᵒ-sndᵉ : ∀ {Γ A} → (et : Eternal A) → ∀ {ρ}
                → sndᵐ ∘ᵐ Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)) {ρ}
                ≈ᵐ eternalᵛ-extᵉ et {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ
×-eternalᵒ-sndᵉ {Γ} et =
  ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ et)))
           (⟨⟩ᵐ-sndᵐ _ _)


-- The interpretation of an eternal variable (projected into `Γ ᴱ`) is a
-- morphism of eternal objects: it commutes with the eternal extractions. This
-- is what carries the eternal parameter across a lock in `var-projᴱ` below.
-- Proved by recursion on the variable; `Γ ᴱ` is lock-free, so only the `∷`
-- structure is traversed (the `⟨⟩` case just drops the lock).

eternal-mor : ∀ {Γ A ρ₀} → (et : Eternal A) → (x : A ∈[ ρ₀ ] Γ) → ∀ {ρ}
            → eternalᵛ-extᵉ et {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (eternalᵛ-extᵉ et {uᵣ} ∘ᵐ var-proj (∈-ᴱ et x))
            ≈ᵐ (eternalᵛ-extᵉ et {uᵣ} ∘ᵐ var-proj (∈-ᴱ et x)) ∘ᵐ projᴱ-extᵉ Γ
eternal-mor {Γ ∷ A} et Hd {ρ} with eternal? A
... | yes eA =
  -- g = extᵉ{uᵣ} ∘ η ∘ sndᵐ ≈ sndᵐ; both sides reduce to the 2nd projection
  -- of the product extraction (`×-eternalᵒ-extᵉ`), up to `extᵉ` irrelevance.
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ g≈snd))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et eA))
  (≈ᵐ-trans (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eA))))
            (∘ᵐ-congˡ (≈ᵐ-sym g≈snd)))))
  where
    g≈snd : eternalᵛ-extᵉ et {uᵣ} ∘ᵐ (η ∘ᵐ sndᵐ) ≈ᵐ sndᵐ
    g≈snd =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et)))
      (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id)
                (∘ᵐ-identityˡ sndᵐ)))
... | no ¬eA = ⊥-elim (¬eA et)
eternal-mor {Γ ∷ B} et (Tl-∷ x) {ρ} with eternal? B
... | yes eB =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternal-mor et x))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (×-fstᵐ-extᵉ B eB)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))))
  where
    -- fstᵐ intertwines the product extraction with the sub-context extraction
    ×-fstᵐ-extᵉ : (B : VType) → (eB : Eternal B)
                → fstᵐ ∘ᵐ Eternalᵒ.extᵉ (×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eB)) {ρ}
                ≈ᵐ projᴱ-extᵉ Γ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
    ×-fstᵐ-extᵉ B eB =
      ≈ᵐ-trans (∘ᵐ-congʳ (×-eternalᵒ-extᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eB)))
               (⟨⟩ᵐ-fstᵐ _ _)
... | no ¬eB = eternal-mor et x
eternal-mor {Γ ⟨ ρ' ⟩} et (Tl-⟨⟩ x) = eternal-mor et x

-- The interpretation of an eternal variable factors through the eternal
-- projection `projᴱ Γ`: interpreting it in `Γ` equals interpreting its image
-- `∈-ᴱ et x` in `Γ ᴱ`, precomposed with the projection. This is the variable
-- case of `projᴱ`-naturality. The lock case uses `eternalᵛ-extᵉ-μ` (to split
-- the extraction across the lock) and `eternal-mor` (to carry it under `⟨ ρ ⟩`).

var-projᴱ : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
          → eternalᵛ-extᵉ et {ρ} ∘ᵐ var-proj x
          ≈ᵐ (eternalᵛ-extᵉ et {uᵣ} ∘ᵐ var-proj (∈-ᴱ et x)) ∘ᵐ projᴱ Γ
var-projᴱ {Γ ∷ A} et Hd with eternal? A
... | yes eA =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))
              (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))
... | no ¬eA = ⊥-elim (¬eA et)
var-projᴱ {Γ ∷ B} et (Tl-∷ x) with eternal? B
... | yes eB =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (var-projᴱ et x))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))
... | no ¬eB =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (var-projᴱ et x))
            (∘ᵐ-assoc _ _ _))
var-projᴱ {Γ ⟨ ρ' ⟩} et (Tl-⟨⟩ {ρ = ρ'} x) =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (var-projᴱ et x)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternal-mor et x))
            (∘ᵐ-assoc _ _ _))))))))

-- `var-morphism` of an eternal variable in `Γ ᴱ` is a morphism of eternal
-- objects (it commutes with the extractions). Unfolds `var-morphism` and
-- applies `eternal-mor`. Used by `restrict-ren`'s variable case.

var-morphism-∈ᴱ-mor : ∀ {Γ A ρ₀} → (et : Eternal A) → (x : A ∈[ ρ₀ ] Γ) → ∀ {ρ}
                    → eternalᵛ-extᵉ et {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (var-morphism (λ _ → ≾ᵣ-refl) (∈-ᴱ et x))
                    ≈ᵐ var-morphism (λ _ → ≾ᵣ-refl) (∈-ᴱ et x) ∘ᵐ projᴱ-extᵉ Γ
var-morphism-∈ᴱ-mor {A = A} et x with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))))
  (≈ᵐ-trans (eternal-mor et x)
            (∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))
... | no ¬et = ⊥-elim (¬et et)

-- Unfold `var-morphism` at an eternal type (handles the internal `eternal?`).

var-morphism-unfoldᵉ : ∀ {Γ A ρ} → (et : Eternal A) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
                     → (y : A ∈[ ρ ] Γ)
                     → var-morphism f y ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ var-proj y
var-morphism-unfoldᵉ {A = A} et f y with eternal? A
... | yes et' = ∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et)
... | no ¬et = ⊥-elim (¬et et)

-- ═══════════════════════════════════════════════════════════════════════════
-- SPLITTING AN EXTENDED CONTEXT ALONG ITS ETERNAL BASE
--
-- The eternal base `⟦ Γ ᴱ ⟧` is an `Eternalᵒ` object, so it distributes out of
-- every lock in an extension `Γ'` (via `strᵉ`/`costrᵉ`) and hence splits off as
-- a product factor:  `⟦ Γ ᴱ ++ᶜ Γ' ⟧ ≅ ⟦ Γ' ⟧ ×ᵐ ⟦ Γ ᴱ ⟧`  — eternal on the
-- right, matching the strength's orientation. This is what makes the eternal
-- base act functorially in the extension `Γ'`.
-- ═══════════════════════════════════════════════════════════════════════════

-- Swap the last two factors of a left-nested triple (its own inverse).
swap₂₃ : ∀ {Y A B} → (Y ×ᵐ A) ×ᵐ B →ᵐ (Y ×ᵐ B) ×ᵐ A
swap₂₃ = ⟨ ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ

swap₂₃-iso : ∀ {Y A B} → swap₂₃ {Y} {B} {A} ∘ᵐ swap₂₃ {Y} {A} {B} ≈ᵐ idᵐ
swap₂₃-iso =
  ≈ᵐ-trans (⟨⟩ᵐ-unique fstᵐ sndᵐ (swap₂₃ ∘ᵐ swap₂₃) fst-eq snd-eq)
           (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))
  where
    fst-eq : fstᵐ ∘ᵐ (swap₂₃ ∘ᵐ swap₂₃) ≈ᵐ fstᵐ
    fst-eq =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ swap₂₃ swap₂₃))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ swap₂₃)
      (≈ᵐ-trans (⟨ ≈ᵐ-trans (∘ᵐ-assoc fstᵐ fstᵐ swap₂₃)
                            (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _))
                 , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
                (≈ᵐ-sym (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ fstᵐ) (sndᵐ ∘ᵐ fstᵐ) fstᵐ ≈ᵐ-refl ≈ᵐ-refl)))))
    snd-eq : sndᵐ ∘ᵐ (swap₂₃ ∘ᵐ swap₂₃) ≈ᵐ sndᵐ
    snd-eq =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ swap₂₃ swap₂₃))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
      (≈ᵐ-trans (∘ᵐ-assoc sndᵐ fstᵐ swap₂₃)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                (⟨⟩ᵐ-sndᵐ _ _))))

-- The forward split, over an ABSTRACT eternal base `(Δ , eΔ)`:
-- `⟦ Δ ++ᶜ Γ' ⟧ →ᵐ ⟦ Γ' ⟧ ×ᵐ ⟦ Δ ⟧`, by recursion on the extension. The lock
-- case is exactly the eternal costrength of `eΔ`. Taking the base explicitly
-- (rather than deriving `Δ = Γ ᴱ`, `eΔ = ⟦ Γ ⟧ᴱ-Eternalᵒ`) is what lets the
-- substitution transports relate two bases by `J` on a base equality.
splitᴰ : (Δ : Ctx) → Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ → (Γ' : Ctx)
       → ⟦ Δ ++ᶜ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ ×ᵐ ⟦ Δ ⟧ᶜᵗˣ
splitᴰ Δ eΔ []         = ⟨ terminalᵐ , idᵐ ⟩ᵐ
splitᴰ Δ eΔ (Γ' ∷ A)   = swap₂₃ ∘ᵐ mapˣᵐ (splitᴰ Δ eΔ Γ') idᵐ
splitᴰ Δ eΔ (Γ' ⟨ ρ ⟩) = Eternalᵒ.costrᵉ eΔ ∘ᵐ ⟨ ρ ⟩ᶠ (splitᴰ Δ eΔ Γ')

-- Its inverse (the eternal strength in the lock case).
splitᴰ⁻¹ : (Δ : Ctx) → Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ → (Γ' : Ctx)
         → ⟦ Γ' ⟧ᶜᵗˣ ×ᵐ ⟦ Δ ⟧ᶜᵗˣ →ᵐ ⟦ Δ ++ᶜ Γ' ⟧ᶜᵗˣ
splitᴰ⁻¹ Δ eΔ []         = sndᵐ
splitᴰ⁻¹ Δ eΔ (Γ' ∷ A)   = mapˣᵐ (splitᴰ⁻¹ Δ eΔ Γ') idᵐ ∘ᵐ swap₂₃
splitᴰ⁻¹ Δ eΔ (Γ' ⟨ ρ ⟩) = ⟨ ρ ⟩ᶠ (splitᴰ⁻¹ Δ eΔ Γ') ∘ᵐ Eternalᵒ.strᵉ eΔ

splitᴰ-iso : (Δ : Ctx) → (eΔ : Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ) → (Γ' : Ctx)
           → splitᴰ Δ eΔ Γ' ∘ᵐ splitᴰ⁻¹ Δ eΔ Γ' ≈ᵐ idᵐ
splitᴰ-iso Δ eΔ [] =
  ≈ᵐ-trans (⟨⟩ᵐ-∘ terminalᵐ idᵐ sndᵐ)
  (≈ᵐ-trans (⟨ ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique)
             , ∘ᵐ-identityˡ sndᵐ ⟩ᵐ-cong)
            (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _))))
splitᴰ-iso Δ eΔ (Γ' ∷ A) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ MM⁻≈id))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) swap₂₃-iso)))
  where
    MM⁻≈id = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
             (≈ᵐ-trans (mapˣᵐ-cong (splitᴰ-iso Δ eΔ Γ') (∘ᵐ-identityˡ _)) mapˣᵐ-idᵐ)
splitᴰ-iso Δ eΔ (Γ' ⟨ ρ ⟩) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ bc≈id))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
            (Eternalᵒ.strᵉ-costrᵉ eΔ))))
  where
    bc≈id = ≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-trans (⟨⟩-congᶠ (splitᴰ-iso Δ eΔ Γ')) ⟨⟩-idᵐ)

splitᴰ⁻¹-iso : (Δ : Ctx) → (eΔ : Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ) → (Γ' : Ctx)
             → splitᴰ⁻¹ Δ eΔ Γ' ∘ᵐ splitᴰ Δ eΔ Γ' ≈ᵐ idᵐ
splitᴰ⁻¹-iso Δ eΔ []         = ⟨⟩ᵐ-sndᵐ terminalᵐ idᵐ
splitᴰ⁻¹-iso Δ eΔ (Γ' ∷ A) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ swap₂₃-iso))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) M⁻M≈id)))
  where
    M⁻M≈id = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
             (≈ᵐ-trans (mapˣᵐ-cong (splitᴰ⁻¹-iso Δ eΔ Γ') (∘ᵐ-identityˡ _)) mapˣᵐ-idᵐ)
splitᴰ⁻¹-iso Δ eΔ (Γ' ⟨ ρ ⟩) =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (Eternalᵒ.costrᵉ-strᵉ eΔ)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) cb≈id)))
  where
    cb≈id = ≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-trans (⟨⟩-congᶠ (splitᴰ⁻¹-iso Δ eΔ Γ')) ⟨⟩-idᵐ)

-- The `Γ`-form wrappers: instantiate the base at `Δ = Γ ᴱ`, `eΔ = ⟦ Γ ⟧ᴱ`.
-- Everything downstream (`Renaming`, `CtxUniformʰ`) is stated against these.
splitᴱ : (Γ Γ' : Ctx) → ⟦ Γ ᴱ ++ᶜ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ ×ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
splitᴱ Γ = splitᴰ (Γ ᴱ) (⟦ Γ ⟧ᴱ-Eternalᵒ)

splitᴱ⁻¹ : (Γ Γ' : Ctx) → ⟦ Γ' ⟧ᶜᵗˣ ×ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ++ᶜ Γ' ⟧ᶜᵗˣ
splitᴱ⁻¹ Γ = splitᴰ⁻¹ (Γ ᴱ) (⟦ Γ ⟧ᴱ-Eternalᵒ)

splitᴱ-iso : (Γ Γ' : Ctx) → splitᴱ Γ Γ' ∘ᵐ splitᴱ⁻¹ Γ Γ' ≈ᵐ idᵐ
splitᴱ-iso Γ = splitᴰ-iso (Γ ᴱ) (⟦ Γ ⟧ᴱ-Eternalᵒ)

-- ───────────────────────────────────────────────────────────────────────────
-- READING THE TOPMOST VARIABLES
--
-- Two facts about `var-morphism` at the top of a context, used wherever a
-- renaming's denotation has to be computed. Both split on `eternal?` of the
-- variable's type, and both sides of each equation reduce simultaneously.
-- ───────────────────────────────────────────────────────────────────────────

private
  infixr 3 _∙ᵛ_
  _∙ᵛ_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙ᵛ_ = ≈ᵐ-trans

-- The head variable denotes the second projection: at a non-eternal type the
-- grade bound is reflexive and the possibility counit cancels `η`; at an
-- eternal one the extraction cancels it.
var-morphism-Hd : ∀ {Γ A} → (f : ¬ Eternal A → uᵣ ≾ᵣ uᵣ)
                → var-morphism {Γ ∷ A} f Hd ≈ᵐ sndᵐ
var-morphism-Hd {A = A} f with eternal? A
... | yes et =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵛ ∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et) ∙ᵛ ⟨⟩-εᵘ∘η≡id)
  ∙ᵛ ∘ᵐ-identityˡ _
... | no ¬et =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr (f ¬et) ≾ᵣ-refl ∙ᵛ ⟨⟩-≤-refl) ∙ᵛ ∘ᵐ-identityˡ _)
  ∙ᵛ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵛ ∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id
  ∙ᵛ ∘ᵐ-identityˡ _

-- Weakening a variable past a `∷` projects the environment.
var-morphism-Tl-∷ : ∀ {Γ A B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                  → var-morphism {Γ ∷ A} f (Tl-∷ y) ≈ᵐ var-morphism f y ∘ᵐ fstᵐ
var-morphism-Tl-∷ {B = B} y f with eternal? B
... | yes et = ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
... | no ¬et = ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
