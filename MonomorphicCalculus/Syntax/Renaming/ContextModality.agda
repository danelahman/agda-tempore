--------------------------------------------------------------------------
-- The context modality as a functor on renamings, and its adjoints.    --
--                                                                      --
-- Contexts and renamings `Ren [] Γ Δ` up to `_≐ʳ_` form a category     --
-- (`Renaming/Category`), on which the context modality `L_ρ = _⟨ ρ ⟩`, --
-- the lock of Fitch-style calculi, acts by `cong-⟨⟩-ren`. Adjoints are --
-- stated in hom-set form, with Agda types as the hom-sets.             --
--                                                                      --
-- Left adjoint. An adjunction `E ⊣ L_ρ` is a bijection                 --
-- `Hom(E Γ, Δ) ≅ Hom(Γ, L_ρ Δ)` natural in `Γ` and `Δ`. It is given by --
-- a representation of each functor `Hom(Γ, L_ρ -)`: a context `E` and  --
-- a bijection `Ren [] E Δ ≅ Ren [] Γ (Δ ⟨ ρ ⟩)` up to `_≐ʳ_`, natural  --
-- in `Δ` (`HomIso`). The representations determine `E` on renamings,   --
-- functorially, and the bijections are then natural in `Γ`             --
-- (`adjunction`). See S. Mac Lane, Categories for the Working          --
-- Mathematician, 2nd ed., Springer 1998, Chapter IV.1, Theorem 2.      --
--                                                                      --
-- Parametric right adjoint. Over a terminal object `1`, `L` is a       --
-- parametric right adjoint when                                        --
--   Hom(Γ, L Δ) ≅ Σ (s : Γ → L 1) Hom(E s, Δ)                          --
-- naturally in `Δ`. See R. Street, The petit topos of globular sets,   --
-- J. Pure Appl. Algebra 154 (2000) 299-315; M. Weber, Generic          --
-- morphisms, parametric representations and weakly cartesian monads,   --
-- Theory Appl. Categ. 13 (2004) 191-234; M. Weber, Familial            --
-- 2-functors and parametric right adjoints, Theory Appl. Categ. 18     --
-- (2007) 665-732.                                                      --
--                                                                      --
-- Here `1 = []`. There is at most one `s : Ren [] Γ ([] ⟨ ρ ⟩)`        --
-- (`into-[]⟨⟩-≐ʳ`), and every `f : Ren [] Γ (Δ ⟨ ρ ⟩)` lies over it,   --
-- as `cong-⟨⟩-ren (!ʳ Δ) ∘ʳ f`. The sum has one summand when such an   --
-- `s` exists and none otherwise, so the form reads: for each `s`, a    --
-- representation `E s` (`PRA`). A left adjoint gives one               --
-- (`LeftAdjoint⇒PRA`). With `𝟏 ≾ ρ`, for the unit `𝟏` of the grades,   --
-- every `Γ` has an `s`, `Γ → Γ ⟨ 𝟏 ⟩ → Γ ⟨ ρ ⟩ → [] ⟨ ρ ⟩`, and the    --
-- two coincide (`PRA⇒LeftAdjoint`).                                    --
--                                                                      --
-- Results, at an arbitrary grade system:                               --
--   `left-adjoint-at-𝟏`: at `ρ ≃ 𝟏`, `L_ρ` has the left adjoint        --
--      `E Γ = Γ`;                                                      --
--   `no-representation-at-[]`: without `𝟏 ≾ ρ` there is no renaming    --
--      `[] → Δ ⟨ ρ ⟩`, so no representation at `[]`;                   --
--   `Counterexample.no-representation`: for `σ ⋦ 𝟏`, `σ' ≾ ρ` and      --
--      `σ · σ' ≾ ρ`, none at `[] ∷ B ⟨ σ ⟩ ∷ A ⟨ σ' ⟩`, which has an   --
--      `s`, so `L_ρ` is not a parametric right adjoint (`not-PRA`);    --
--   `left-adjoint⇔ρ≃𝟏`: `L_ρ` has a left adjoint iff `ρ ≃ 𝟏`;          --
--   `PRA⇒factor≾𝟏`: if `L_ρ` is a parametric right adjoint, `σ' ≾ ρ`   --
--      and `σ · σ' ≾ ρ`, then `σ ≾ 𝟏`;                                 --
--   `PRA-above-𝟏⇒ρ≾𝟏`: if `L_ρ` is one and `𝟏 ≾ ρ`, then `ρ ≾ 𝟏`;      --
--   `PRA-⊤⇒⊤≾𝟏`: if `L_⊤` is one, `𝟏` is the greatest grade.           --
-- The negative results use a Kripke model (`ContextModality/Model`).   --
--------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt) renaming (⊤ to Unit)

open import Relation.Nullary using (¬_; yes; no)

open import Grades.Base
open import Language.Spec

open import Util.Equality

module MonomorphicCalculus.Syntax.Renaming.ContextModality (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Contexts             S
open import MonomorphicCalculus.Syntax.Types                S
open import MonomorphicCalculus.Syntax.Renaming             S
open import MonomorphicCalculus.Syntax.Renaming.Equivalence S
open import MonomorphicCalculus.Syntax.Renaming.ContextModality.Model  S

------------------------------------------------------------------------
-- Representations

-- a bijection `Ren [] E Δ ≅ Ren [] Γ (Δ ⟨ ρ ⟩)`, natural in `Δ`: `E`
-- represents `Ren [] Γ (_ ⟨ ρ ⟩)`

record HomIso (ρ : R) (Γ E : Ctx) : Set where
  field
    φ      : ∀ {Δ} → Ren [] E Δ → Ren [] Γ (Δ ⟨ ρ ⟩)
    ψ      : ∀ {Δ} → Ren [] Γ (Δ ⟨ ρ ⟩) → Ren [] E Δ
    φ-cong : ∀ {Δ} {g g' : Ren [] E Δ} → g ≐ʳ g' → φ g ≐ʳ φ g'
    ψ-cong : ∀ {Δ} {f f' : Ren [] Γ (Δ ⟨ ρ ⟩)} → f ≐ʳ f' → ψ f ≐ʳ ψ f'
    ψ∘φ    : ∀ {Δ} → (g : Ren [] E Δ) → ψ (φ g) ≐ʳ g
    φ∘ψ    : ∀ {Δ} → (f : Ren [] Γ (Δ ⟨ ρ ⟩)) → φ (ψ f) ≐ʳ f
    φ-nat  : ∀ {Δ Δ'} → (h : Ren [] Δ Δ') → (g : Ren [] E Δ)
           → φ (h ∘ʳ g) ≐ʳ (cong-⟨⟩-ren h ∘ʳ φ g)

------------------------------------------------------------------------
-- Left adjoint

LeftAdjoint : R → Set
LeftAdjoint ρ = (Γ : Ctx) → Σ[ E ∈ Ctx ] HomIso ρ Γ E

-- an adjunction `E ⊣ L_ρ`: `E` on contexts (`E-ctx`) and on renamings
-- (`E-ren`), functorial, with bijections natural in `Δ` (`hom-iso`) and in
-- `Γ` (`φ-natᴳ`)

record Adjunction (ρ : R) : Set where
  field
    E-ctx    : Ctx → Ctx
    hom-iso  : (Γ : Ctx) → HomIso ρ Γ (E-ctx Γ)
    E-ren    : ∀ {Γ Γ'} → Ren [] Γ Γ' → Ren [] (E-ctx Γ) (E-ctx Γ')
    E-ren-id : ∀ {Γ} → E-ren (id-ren {Δ = Γ}) ≐ʳ id-ren
    E-ren-∘  : ∀ {Γ Γ' Γ''} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → E-ren (r₂ ∘ʳ r₁) ≐ʳ (E-ren r₂ ∘ʳ E-ren r₁)
    φ-natᴳ   : ∀ {Γ Γ' Δ} → (r : Ren [] Γ Γ') → (g : Ren [] (E-ctx Γ') Δ)
             → HomIso.φ (hom-iso Γ) (g ∘ʳ E-ren r) ≐ʳ (HomIso.φ (hom-iso Γ') g ∘ʳ r)

-- the representations determine the adjunction, with
-- `E-ren r = ψ_Γ (φ_Γ' id ∘ r)`

adjunction : ∀ {ρ} → LeftAdjoint ρ → Adjunction ρ
adjunction {ρ} la = record
  { E-ctx    = E-ctx
  ; hom-iso  = H
  ; E-ren    = E-ren
  ; E-ren-id = E-ren-id
  ; E-ren-∘  = E-ren-∘
  ; φ-natᴳ   = φ-natᴳ
  }
  where
  E-ctx : Ctx → Ctx
  E-ctx Γ = proj₁ (la Γ)

  H : (Γ : Ctx) → HomIso ρ Γ (E-ctx Γ)
  H Γ = proj₂ (la Γ)

  module H Γ = HomIso (H Γ)

  E-ren : ∀ {Γ Γ'} → Ren [] Γ Γ' → Ren [] (E-ctx Γ) (E-ctx Γ')
  E-ren {Γ} {Γ'} r = H.ψ Γ (H.φ Γ' id-ren ∘ʳ r)

  φ-E-ren : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → H.φ Γ (E-ren r) ≐ʳ (H.φ Γ' id-ren ∘ʳ r)
  φ-E-ren {Γ} {Γ'} r = H.φ∘ψ Γ (H.φ Γ' id-ren ∘ʳ r)

  φ-inj : ∀ {Γ Δ} {g g' : Ren [] (E-ctx Γ) Δ} → H.φ Γ g ≐ʳ H.φ Γ g' → g ≐ʳ g'
  φ-inj {Γ} {g = g} {g'} e =
    ≐ʳ-trans (≐ʳ-sym (H.ψ∘φ Γ g)) (≐ʳ-trans (H.ψ-cong Γ e) (H.ψ∘φ Γ g'))

  φ-natᴳ : ∀ {Γ Γ' Δ} → (r : Ren [] Γ Γ') → (g : Ren [] (E-ctx Γ') Δ)
         → H.φ Γ (g ∘ʳ E-ren r) ≐ʳ (H.φ Γ' g ∘ʳ r)
  φ-natᴳ {Γ} {Γ'} r g =
    ≐ʳ-trans (H.φ-nat Γ g (E-ren r))
      (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (φ-E-ren r))
        (≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ʳ _ _ _))
          (∘ʳ-≐ʳ (≐ʳ-trans (≐ʳ-sym (H.φ-nat Γ' g id-ren))
                           (H.φ-cong Γ' (∘ʳ-identityʳ-≐ʳ g)))
                 ≐ʳ-refl)))

  E-ren-id : ∀ {Γ} → E-ren (id-ren {Δ = Γ}) ≐ʳ id-ren
  E-ren-id {Γ} = ≐ʳ-trans (H.ψ-cong Γ (∘ʳ-identityʳ-≐ʳ _)) (H.ψ∘φ Γ id-ren)

  E-ren-∘ : ∀ {Γ Γ' Γ''} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
          → E-ren (r₂ ∘ʳ r₁) ≐ʳ (E-ren r₂ ∘ʳ E-ren r₁)
  E-ren-∘ r₂ r₁ =
    φ-inj
      (≐ʳ-trans (φ-E-ren (r₂ ∘ʳ r₁))
        (≐ʳ-sym
          (≐ʳ-trans (φ-natᴳ r₁ (E-ren r₂))
            (≐ʳ-trans (∘ʳ-≐ʳ (φ-E-ren r₂) ≐ʳ-refl) (∘ʳ-assoc-≐ʳ _ _ _)))))

------------------------------------------------------------------------
-- Parametric right adjoint

!ʳ : (Γ : Ctx) → Ren [] Γ []
!ʳ Γ = wk-ctx-ren ec-[] Γ

into-[]-≐ʳ : ∀ {Γ} → (r r' : Ren [] Γ []) → r ≐ʳ r'
into-[]-≐ʳ r r' = mk≐ʳ (λ ())

into-[]⟨⟩-≐ʳ : ∀ {Γ ρ} → (r r' : Ren [] Γ ([] ⟨ ρ ⟩)) → r ≐ʳ r'
into-[]⟨⟩-≐ʳ r r' = mk≐ʳ (λ { (Tl-⟨⟩ ()) })

-- for each `s : Γ → [] ⟨ ρ ⟩`, a representation

PRA : R → Set
PRA ρ = (Γ : Ctx) → Ren [] Γ ([] ⟨ ρ ⟩) → Σ[ E ∈ Ctx ] HomIso ρ Γ E

LeftAdjoint⇒PRA : ∀ {ρ} → LeftAdjoint ρ → PRA ρ
LeftAdjoint⇒PRA la Γ _ = la Γ

-- with `𝟏 ≾ ρ`, every `Γ` has an `s`

into-⟨⟩-ren : ∀ {ρ} → 𝟏ᵣ ≾ᵣ ρ → (Γ : Ctx) → Ren [] Γ (Γ ⟨ ρ ⟩)
into-⟨⟩-ren q Γ = ⟨⟩-≤-ren q ∘ʳ ⟨⟩-η-ren

PRA⇒LeftAdjoint : ∀ {ρ} → PRA ρ → 𝟏ᵣ ≾ᵣ ρ → LeftAdjoint ρ
PRA⇒LeftAdjoint pra q Γ = pra Γ (cong-⟨⟩-ren (!ʳ Γ) ∘ʳ into-⟨⟩-ren q Γ)

------------------------------------------------------------------------
-- At a grade equivalent to the unit `𝟏` of the grades, the context
-- modality has a left adjoint, the identity

left-adjoint-at-𝟏 : ∀ {ρ} → ρ ≃ᵣ 𝟏ᵣ → LeftAdjoint ρ
left-adjoint-at-𝟏 {ρ} (p , q) Γ = Γ , record
  { φ      = φ
  ; ψ      = ψ
  ; φ-cong = λ e → ∘ʳ-≐ʳ (cong-⟨⟩-ren-≐ʳ e) ≐ʳ-refl
  ; ψ-cong = λ e → ∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl e)
  ; ψ∘φ    = λ g → mk≐ʳ (λ y → refl)
  ; φ∘ψ    = λ f → mk≐ʳ (λ { (Tl-⟨⟩ y) → refl })
  ; φ-nat  = λ h g →
      ≐ʳ-trans (∘ʳ-≐ʳ (cong-⟨⟩-ren-∘-≐ʳ h g) ≐ʳ-refl) (∘ʳ-assoc-≐ʳ _ _ _)
  }
  where
  φ : ∀ {Δ} → Ren [] Γ Δ → Ren [] Γ (Δ ⟨ ρ ⟩)
  φ g = cong-⟨⟩-ren g ∘ʳ into-⟨⟩-ren q Γ

  ψ : ∀ {Δ} → Ren [] Γ (Δ ⟨ ρ ⟩) → Ren [] Γ Δ
  ψ f = ⟨⟩-η⁻¹-ren ∘ʳ (⟨⟩-≤-ren p ∘ʳ f)

------------------------------------------------------------------------
-- Without `𝟏 ≾ ρ`, no renaming `[] → Δ ⟨ ρ ⟩`, and no representation at
-- `[]`

no-renaming-into-⟨⟩ : ∀ {ρ Δ} → ¬ (𝟏ᵣ ≾ᵣ ρ) → Ren [] [] (Δ ⟨ ρ ⟩) → ⊥
no-renaming-into-⟨⟩ {ρ} {Δ} n f = go (sound {w = 𝟏ᵣ} ≾ᵣ-refl f tt)
  where
  open KripkeModel (λ w → w ≾ᵣ 𝟏ᵣ)

  go : ⟦ Δ ⟨ ρ ⟩ ⟧ᶜᵗˣ 𝟏ᵣ → ⊥
  go (w₀ , w₀≾𝟏 , step τ τ≾ρ e , _) =
    n (≾ᵣ-trans (≃ᵣ⇒≾ᵣ e)
        (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ w₀≾𝟏)
          (≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ τ)) τ≾ρ)))

no-representation-at-[] : ∀ {ρ E} → ¬ (𝟏ᵣ ≾ᵣ ρ) → HomIso ρ [] E → ⊥
no-representation-at-[] n H = no-renaming-into-⟨⟩ n (HomIso.φ H id-ren)

------------------------------------------------------------------------
-- No representation at `Γᶜ = [] ∷ B ⟨ σ ⟩ ∷ A ⟨ σ' ⟩`
--
-- `B = [ 𝟏 ] unit` and `A = [ σ ] unit`. `f₁` cuts both modalities and
-- `A` (`σ · σ' ≾ ρ`), `f₂` the last modality (`σ' ≾ ρ`). A context `I`
-- with a renaming `Γᶜ → I ⟨ ρ ⟩` and renamings into both targets holds `B`
-- within `𝟏` and `A` behind the modality `⟨ σ ⟩` at one world, which
-- `σ ⋦ 𝟏` rules out.

module Counterexample {σ σ' ρ : R}
  (σ≰𝟏 : ¬ (σ ≾ᵣ 𝟏ᵣ)) (σ'≾ρ : σ' ≾ᵣ ρ) (σσ'≾ρ : σ ·ᵣ σ' ≾ᵣ ρ) where

  B A : VType
  B = [ 𝟏ᵣ ] unit
  A = [ σ ] unit

  Γᶜ : Ctx
  Γᶜ = (([] ∷ B) ⟨ σ ⟩ ∷ A) ⟨ σ' ⟩

  Δ₁ Δ₂ : Ctx
  Δ₁ = [] ∷ B
  Δ₂ = ([] ∷ B) ⟨ σ ⟩ ∷ A

  f₁ : Ren [] Γᶜ (Δ₁ ⟨ ρ ⟩)
  f₁ = ⟨⟩-≤-ren σσ'≾ρ ∘ʳ (⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren wk-ren)

  f₂ : Ren [] Γᶜ (Δ₂ ⟨ ρ ⟩)
  f₂ = ⟨⟩-≤-ren σ'≾ρ

  no-common-source : (I : Ctx) → Ren [] Γᶜ (I ⟨ ρ ⟩)
                   → Ren [] I Δ₁ → Ren [] I Δ₂ → ⊥
  no-common-source I η g₁ g₂ = go (sound {w = σ ·ᵣ σ'} tt η γ)
    where
    open KripkeModel (λ _ → Unit)

    γ : ⟦ Γᶜ ⟧ᶜᵗˣ (σ ·ᵣ σ')
    γ =   σ , tt , step σ' ≾ᵣ-refl ≃ᵣ-refl
        , ( (𝟏ᵣ , tt , step σ ≾ᵣ-refl (≃ᵣ-sym (·ᵣ-identityˡ σ))
                 , (tt , at-unit 𝟏ᵣ ≾ᵣ-refl (≃ᵣ-sym (·ᵣ-identityʳ 𝟏ᵣ))))
          , at-unit 𝟏ᵣ ≾ᵣ-refl (≃ᵣ-sym (·ᵣ-identityʳ σ)) )

    go : ⟦ I ⟨ ρ ⟩ ⟧ᶜᵗˣ (σ ·ᵣ σ') → ⊥
    go (w'' , _ , _ , dI) with sound tt g₁ dI | sound tt g₂ dI
    ... | _ , at-unit τ₁ τ₁≾𝟏 e₁ | (_ , at-unit τ₀ _ e₀) =
      σ≰𝟏 (≾ᵣ-zero-productˡ
             (≾ᵣ-trans (≃ᵣ⇒≿ᵣ e₀)
               (≾ᵣ-trans (≃ᵣ⇒≾ᵣ e₁)
                 (≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ τ₁)) τ₁≾𝟏))))

  -- a representation `E` gives `φ id : Γᶜ → E ⟨ ρ ⟩` and `ψ fᵢ : E → Δᵢ`

  no-representation : (E : Ctx) → HomIso ρ Γᶜ E → ⊥
  no-representation E H = no-common-source E (φ id-ren) (ψ f₁) (ψ f₂)
    where open HomIso H

  -- `Γᶜ` has an `s`, and no representation over it

  not-PRA : ¬ PRA ρ
  not-PRA pra = no-representation (proj₁ (pra Γᶜ s)) (proj₂ (pra Γᶜ s))
    where
    s : Ren [] Γᶜ ([] ⟨ ρ ⟩)
    s = cong-⟨⟩-ren (!ʳ Δ₂) ∘ʳ f₂

  no-left-adjoint : ¬ LeftAdjoint ρ
  no-left-adjoint la = no-representation (proj₁ (la Γᶜ)) (proj₂ (la Γᶜ))

------------------------------------------------------------------------
-- Consequences

-- a left adjoint exactly at the grades equivalent to `𝟏`

left-adjoint⇒ρ≃𝟏 : ∀ {ρ} → LeftAdjoint ρ → ρ ≃ᵣ 𝟏ᵣ
left-adjoint⇒ρ≃𝟏 {ρ} la with 𝟏ᵣ ≾ᵣ? ρ
... | no n  = ⊥-elim (no-representation-at-[] n (proj₂ (la [])))
... | yes q with ρ ≾ᵣ? 𝟏ᵣ
...   | yes p = p , q
...   | no n  =
  ⊥-elim (Counterexample.no-left-adjoint {σ = ρ} {σ' = 𝟏ᵣ} n q (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ)) la)

left-adjoint⇔ρ≃𝟏 : ∀ {ρ} → (LeftAdjoint ρ → ρ ≃ᵣ 𝟏ᵣ) × (ρ ≃ᵣ 𝟏ᵣ → LeftAdjoint ρ)
left-adjoint⇔ρ≃𝟏 = left-adjoint⇒ρ≃𝟏 , left-adjoint-at-𝟏

-- a parametric right adjoint admits no factor `σ ⋦ 𝟏` in front of a
-- grade `σ' ≾ ρ` that keeps the product below `ρ`

PRA⇒factor≾𝟏 : ∀ {ρ σ σ'} → PRA ρ → σ' ≾ᵣ ρ → σ ·ᵣ σ' ≾ᵣ ρ → σ ≾ᵣ 𝟏ᵣ
PRA⇒factor≾𝟏 {ρ} {σ} pra q q' with σ ≾ᵣ? 𝟏ᵣ
... | yes p = p
... | no n  = ⊥-elim (Counterexample.not-PRA n q q' pra)

-- in particular a parametric right adjoint above `𝟏` is equivalent to `𝟏`

PRA-above-𝟏⇒ρ≾𝟏 : ∀ {ρ} → PRA ρ → 𝟏ᵣ ≾ᵣ ρ → ρ ≾ᵣ 𝟏ᵣ
PRA-above-𝟏⇒ρ≾𝟏 {ρ} pra q = PRA⇒factor≾𝟏 {σ = ρ} {σ' = 𝟏ᵣ} pra q (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ))

-- so the context modality is a parametric right adjoint at every grade only
-- if the unit `𝟏` of the grades is the greatest grade

PRA-⊤⇒⊤≾𝟏 : PRA ⊤ᵣ → ⊤ᵣ ≾ᵣ 𝟏ᵣ
PRA-⊤⇒⊤≾𝟏 pra = PRA-above-𝟏⇒ρ≾𝟏 pra (≾-⊤ᵣ 𝟏ᵣ)
