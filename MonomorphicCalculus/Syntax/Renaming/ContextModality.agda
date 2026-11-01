--------------------------------------------------------------------------
-- The context modality as a functor on renamings, and its adjoints.    --
--                                                                      --
-- Contexts and renamings `Ren [] Γ Δ` up to `_≐ʳ_` form a category     --
-- (`Renaming/Category`), on which the context modality `L_ρ = _⟨ ρ ⟩`, --
-- the lock of Fitch-style calculi, acts by `cong-⟨⟩-ren`. The comma    --
-- category `(Γ ↓ L_ρ)` has objects `(Δ , f)` with                      --
-- `f : Ren [] Γ (Δ ⟨ ρ ⟩)` (`Comma ρ Γ`), and morphisms                --
-- `g : Ren [] Δ Δ'` with `L_ρ g ∘ f ≐ʳ f'` (`CommaHom`).               --
--                                                                      --
-- Left adjoint. A functor `L` has a left adjoint iff every `(Γ ↓ L)`   --
-- has an initial object `(E Γ , η_Γ)`. Given one, `g ↦ L g ∘ η_Γ` is a --
-- bijection `Hom(E Γ, Δ) ≅ Hom(Γ, L Δ)`, onto by existence and         --
-- one-to-one by uniqueness, natural in `Δ`, and `E` is a functor by    --
-- uniqueness. Conversely the unit of an adjunction is initial. See     --
-- S. Mac Lane, Categories for the Working Mathematician, 2nd ed.,      --
-- Springer 1998, Chapter IV.1, Theorem 2.                              --
--                                                                      --
-- Parametric right adjoint. Over a terminal object `1` (here `[]`),    --
-- `L` is a parametric right adjoint when `L₁ : Δ ↦ (L Δ , L !)`, into  --
-- the slice over `L 1`, has a left adjoint; equivalently               --
-- `Hom(Γ, L Δ) ≅ Σ (s : Γ → L 1) Hom(E s, Δ)`, naturally in `Δ`. See   --
-- R. Street, The petit topos of globular sets, J. Pure Appl. Algebra   --
-- 154 (2000) 299-315; M. Weber, Generic morphisms, parametric          --
-- representations and weakly cartesian monads, Theory Appl. Categ. 13  --
-- (2004) 191-234; M. Weber, Familial 2-functors and parametric right   --
-- adjoints, Theory Appl. Categ. 18 (2007) 665-732.                     --
--                                                                      --
-- By the first, `L₁` has a left adjoint iff every `((Γ , s) ↓ L₁)`     --
-- has an initial object, and `((Γ , s) ↓ L₁)` is the full subcategory  --
-- of `(Γ ↓ L)` on the `(Δ , f)` with `L ! ∘ f = s`. These are the      --
-- connected components of `(Γ ↓ L)`: a morphism `g` preserves          --
-- `L ! ∘ f`, as `! ∘ g = !`, and every `(Δ , f)` has the morphism `!`  --
-- to `(1 , L ! ∘ f)`. So `L` is a parametric right adjoint iff every   --
-- connected component of every `(Γ ↓ L)` has an initial object         --
-- (`PRA`).                                                             --
-- `ContextModality/Adjunction` proves both equivalent to their hom-set --
-- forms.                                                               --
--                                                                      --
-- Here `[] ⟨ ρ ⟩` has no variables, so there is at most one renaming   --
-- `Γ → [] ⟨ ρ ⟩` (`into-[]⟨⟩-≐ʳ`), and `(Γ ↓ L_ρ)` has at most one     --
-- component (`connected`). `PRA ρ` asks for an initial object of each  --
-- nonempty `(Γ ↓ L_ρ)`, `LeftAdjoint ρ` besides that none be empty.    --
-- With `𝟏 ≾ ρ` none is empty (`Γ → Γ ⟨ 𝟏 ⟩ → Γ ⟨ ρ ⟩ → [] ⟨ ρ ⟩`), so  --
-- the two coincide; without it `([] ↓ L_ρ)` is empty.                  --
--                                                                      --
-- Results, at an arbitrary grade system:                               --
--   `connected`: a nonempty `(Γ ↓ L_ρ)` is connected;                  --
--   `left-adjoint⇔unit`: `L_ρ` has a left adjoint iff `ρ ≃ 𝟏`;         --
--   `Counterexample.no-common-source`: for `σ ⋦ 𝟏`, `σ' ≾ ρ` and       --
--      `σ · σ' ≾ ρ`, two objects over `[] ∷ B ⟨ σ ⟩ ∷ A ⟨ σ' ⟩` with   --
--      no common source, so `L_ρ` is not a parametric right adjoint;   --
--   `PRA⇒no-factor`: if `L_ρ` is a parametric right adjoint,           --
--      `σ' ≾ ρ` and `σ · σ' ≾ ρ`, then `σ ≾ 𝟏`;                        --
--   `PRA⇒unit-maximal`: if `L_ρ` is one and `𝟏 ≾ ρ`, then `ρ ≾ 𝟏`;     --
--   `PRA-⊤⇒⊤≾𝟏`: if `L_⊤` is one, the unit is the greatest grade.      --
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
-- The comma category (Γ ↓ L_ρ)

record Comma (ρ : R) (Γ : Ctx) : Set where
  constructor _,ᵒ_
  field
    ctx : Ctx
    str : Ren [] Γ (ctx ⟨ ρ ⟩)

open Comma public

record CommaHom {ρ Γ} (X Y : Comma ρ Γ) : Set where
  constructor _,ʰ_
  field
    map : Ren [] (ctx X) (ctx Y)
    tri : (cong-⟨⟩-ren map ∘ʳ str X) ≐ʳ str Y

open CommaHom public

Initial : ∀ {ρ Γ} → Comma ρ Γ → Set
Initial {ρ} {Γ} I =
  (X : Comma ρ Γ) → Σ[ h ∈ CommaHom I X ] ((h' : CommaHom I X) → map h' ≐ʳ map h)

Terminal : ∀ {ρ Γ} → Comma ρ Γ → Set
Terminal {ρ} {Γ} T =
  (X : Comma ρ Γ) → Σ[ h ∈ CommaHom X T ] ((h' : CommaHom X T) → map h' ≐ʳ map h)

-- zig-zags of morphisms: being in the same connected component

data Zigzag {ρ Γ} : Comma ρ Γ → Comma ρ Γ → Set where
  here : ∀ {X} → Zigzag X X
  fwd  : ∀ {X Y Z} → CommaHom X Y → Zigzag Y Z → Zigzag X Z
  bwd  : ∀ {X Y Z} → CommaHom Y X → Zigzag Y Z → Zigzag X Z

zz-trans : ∀ {ρ Γ} {X Y Z : Comma ρ Γ} → Zigzag X Y → Zigzag Y Z → Zigzag X Z
zz-trans here      q = q
zz-trans (fwd h p) q = fwd h (zz-trans p q)
zz-trans (bwd h p) q = bwd h (zz-trans p q)

InitialInComponent : ∀ {ρ Γ} → Comma ρ Γ → Set
InitialInComponent {ρ} {Γ} I =
  (X : Comma ρ Γ) → Zigzag I X
  → Σ[ h ∈ CommaHom I X ] ((h' : CommaHom I X) → map h' ≐ʳ map h)

LeftAdjoint : R → Set
LeftAdjoint ρ = (Γ : Ctx) → Σ[ I ∈ Comma ρ Γ ] Initial I

PRA : R → Set
PRA ρ = (Γ : Ctx) → (X : Comma ρ Γ)
      → Σ[ I ∈ Comma ρ Γ ] (Zigzag I X × InitialInComponent I)

LeftAdjoint⇒PRA : ∀ {ρ} → LeftAdjoint ρ → PRA ρ
LeftAdjoint⇒PRA la Γ X =
  proj₁ (la Γ) , fwd (proj₁ (proj₂ (la Γ) X)) here , λ Y _ → proj₂ (la Γ) Y

------------------------------------------------------------------------
-- `[]` is terminal, so every nonempty comma category is connected

!ʳ : (Γ : Ctx) → Ren [] Γ []
!ʳ Γ = wk-ctx-ren ec-[] Γ

into-[]-≐ʳ : ∀ {Γ} → (r r' : Ren [] Γ []) → r ≐ʳ r'
into-[]-≐ʳ r r' = mk≐ʳ (λ ())

into-[]⟨⟩-≐ʳ : ∀ {Γ ρ} → (r r' : Ren [] Γ ([] ⟨ ρ ⟩)) → r ≐ʳ r'
into-[]⟨⟩-≐ʳ r r' = mk≐ʳ (λ { (Tl-⟨⟩ ()) })

[]-terminal : ∀ {Γ} → (r : Ren [] Γ []) → r ≐ʳ !ʳ Γ
[]-terminal r = into-[]-≐ʳ r _

terminal : ∀ {ρ Γ} → Comma ρ Γ → Σ[ T ∈ Comma ρ Γ ] Terminal T
terminal X =
    ([] ,ᵒ (cong-⟨⟩-ren (!ʳ (ctx X)) ∘ʳ str X))
  , λ Y → (!ʳ (ctx Y) ,ʰ into-[]⟨⟩-≐ʳ _ _) , λ h' → into-[]-≐ʳ _ _

connected : ∀ {ρ Γ} → (X Y : Comma ρ Γ) → Zigzag X Y
connected X Y =
  fwd (proj₁ (proj₂ (terminal X) X)) (bwd (proj₁ (proj₂ (terminal X) Y)) here)

------------------------------------------------------------------------
-- At a unit-equivalent grade the context modality has a left adjoint, the
-- identity

unit-comma : ∀ {ρ} → 𝟏ᵣ ≾ᵣ ρ → (Γ : Ctx) → Comma ρ Γ
unit-comma q Γ = Γ ,ᵒ (⟨⟩-≤-ren q ∘ʳ ⟨⟩-η-ren)

left-adjoint-at-unit : ∀ {ρ} → ρ ≃ᵣ 𝟏ᵣ → LeftAdjoint ρ
left-adjoint-at-unit {ρ} (p , q) Γ = unit-comma q Γ , init
  where
  init : Initial (unit-comma q Γ)
  init X = (g ,ʰ mk≐ʳ tri') , uniq
    where
    g : Ren [] Γ (ctx X)
    g = ⟨⟩-η⁻¹-ren ∘ʳ (⟨⟩-≤-ren p ∘ʳ str X)

    tri' : ∀ {A σ} → (x : A ∈[ σ ] (ctx X ⟨ ρ ⟩))
         → var-img (cong-⟨⟩-ren g ∘ʳ (⟨⟩-≤-ren q ∘ʳ ⟨⟩-η-ren)) x
         ≡ var-img (str X) x
    tri' (Tl-⟨⟩ y) = refl

    uniq : (h' : CommaHom (unit-comma q Γ) X) → map h' ≐ʳ g
    uniq h' = mk≐ʳ (λ y → at (tri h') (Tl-⟨⟩ y))

------------------------------------------------------------------------
-- Without `𝟏 ≾ ρ`, `([] ↓ L_ρ)` is empty

no-object-at-[] : ∀ {ρ} → ¬ (𝟏ᵣ ≾ᵣ ρ) → Comma ρ [] → ⊥
no-object-at-[] {ρ} n X = go (sound {w = 𝟏ᵣ} ≾ᵣ-refl (str X) tt)
  where
  open KripkeModel (λ w → w ≾ᵣ 𝟏ᵣ)

  go : ⟦ ctx X ⟨ ρ ⟩ ⟧ᶜᵗˣ 𝟏ᵣ → ⊥
  go (w₀ , w₀≾𝟏 , step τ τ≾ρ e , _) =
    n (≾ᵣ-trans (≃ᵣ⇒≾ᵣ e)
        (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ w₀≾𝟏)
          (≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ τ)) τ≾ρ)))

------------------------------------------------------------------------
-- Two objects with no common source
--
-- `Γᶜ = [] ∷ B ⟨ σ ⟩ ∷ A ⟨ σ' ⟩`, with `B = [ 𝟏 ] unit` and
-- `A = [ σ ] unit`. `X₁` cuts both modalities and `A` (`σ · σ' ≾ ρ`), `X₂`
-- the last modality (`σ' ≾ ρ`). A source of both holds `B` within the unit
-- and `A` behind the modality `⟨ σ ⟩` at one world, which `σ ⋦ 𝟏` rules out.

module Counterexample {σ σ' ρ : R}
  (σ≰𝟏 : ¬ (σ ≾ᵣ 𝟏ᵣ)) (σ'≾ρ : σ' ≾ᵣ ρ) (σσ'≾ρ : σ ·ᵣ σ' ≾ᵣ ρ) where

  B A : VType
  B = [ 𝟏ᵣ ] unit
  A = [ σ ] unit

  Γᶜ : Ctx
  Γᶜ = (([] ∷ B) ⟨ σ ⟩ ∷ A) ⟨ σ' ⟩

  X₁ X₂ : Comma ρ Γᶜ
  X₁ = ([] ∷ B) ,ᵒ (⟨⟩-≤-ren σσ'≾ρ ∘ʳ (⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren wk-ren))
  X₂ = (([] ∷ B) ⟨ σ ⟩ ∷ A) ,ᵒ ⟨⟩-≤-ren σ'≾ρ

  no-common-source : (I : Comma ρ Γᶜ) → CommaHom I X₁ → CommaHom I X₂ → ⊥
  no-common-source I h₁ h₂ = go (sound {w = σ ·ᵣ σ'} tt (str I) γ)
    where
    open KripkeModel (λ _ → Unit)

    γ : ⟦ Γᶜ ⟧ᶜᵗˣ (σ ·ᵣ σ')
    γ =   σ , tt , step σ' ≾ᵣ-refl ≃ᵣ-refl
        , ( (𝟏ᵣ , tt , step σ ≾ᵣ-refl (≃ᵣ-sym (·ᵣ-identityˡ σ))
                 , (tt , at-unit 𝟏ᵣ ≾ᵣ-refl (≃ᵣ-sym (·ᵣ-identityʳ 𝟏ᵣ))))
          , at-unit 𝟏ᵣ ≾ᵣ-refl (≃ᵣ-sym (·ᵣ-identityʳ σ)) )

    go : ⟦ ctx I ⟨ ρ ⟩ ⟧ᶜᵗˣ (σ ·ᵣ σ') → ⊥
    go (w'' , _ , _ , dI) with sound tt (map h₁) dI | sound tt (map h₂) dI
    ... | _ , at-unit τ₁ τ₁≾𝟏 e₁ | (_ , at-unit τ₀ _ e₀) =
      σ≰𝟏 (≾ᵣ-zero-productˡ
             (≾ᵣ-trans (≃ᵣ⇒≿ᵣ e₀)
               (≾ᵣ-trans (≃ᵣ⇒≾ᵣ e₁)
                 (≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ τ₁)) τ₁≾𝟏))))

  no-initial : (I : Comma ρ Γᶜ) → ¬ Initial I
  no-initial I init = no-common-source I (proj₁ (init X₁)) (proj₁ (init X₂))

  -- the comma category is nonempty and connected, and has no initial
  -- object

  not-PRA : ¬ PRA ρ
  not-PRA pra with pra Γᶜ X₂
  ... | I , zz , init =
    no-common-source I
      (proj₁ (init X₁ (zz-trans zz (connected X₂ X₁))))
      (proj₁ (init X₂ zz))

------------------------------------------------------------------------
-- Consequences

-- a left adjoint exactly at the unit-equivalent grades

left-adjoint⇒unit : ∀ {ρ} → LeftAdjoint ρ → ρ ≃ᵣ 𝟏ᵣ
left-adjoint⇒unit {ρ} la with 𝟏ᵣ ≾ᵣ? ρ
... | no n  = ⊥-elim (no-object-at-[] n (proj₁ (la [])))
... | yes q with ρ ≾ᵣ? 𝟏ᵣ
...   | yes p = p , q
...   | no n  =
  ⊥-elim (C.no-initial (proj₁ (la C.Γᶜ)) (proj₂ (la C.Γᶜ)))
  where
  module C = Counterexample {σ = ρ} {σ' = 𝟏ᵣ} n q (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ))

left-adjoint⇔unit : ∀ {ρ} → (LeftAdjoint ρ → ρ ≃ᵣ 𝟏ᵣ) × (ρ ≃ᵣ 𝟏ᵣ → LeftAdjoint ρ)
left-adjoint⇔unit = left-adjoint⇒unit , left-adjoint-at-unit

-- a parametric right adjoint admits no factor `σ ⋦ 𝟏` in front of a
-- grade `σ' ≾ ρ` that keeps the product below `ρ`

PRA⇒no-factor : ∀ {ρ σ σ'} → PRA ρ → σ' ≾ᵣ ρ → σ ·ᵣ σ' ≾ᵣ ρ → σ ≾ᵣ 𝟏ᵣ
PRA⇒no-factor {ρ} {σ} pra q q' with σ ≾ᵣ? 𝟏ᵣ
... | yes p = p
... | no n  = ⊥-elim (Counterexample.not-PRA n q q' pra)

-- in particular a parametric right adjoint above the unit is
-- unit-equivalent

PRA⇒unit-maximal : ∀ {ρ} → PRA ρ → 𝟏ᵣ ≾ᵣ ρ → ρ ≾ᵣ 𝟏ᵣ
PRA⇒unit-maximal {ρ} pra q = PRA⇒no-factor {σ = ρ} {σ' = 𝟏ᵣ} pra q (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ))

-- so the context modality is a parametric right adjoint at every grade only
-- if the unit is the greatest grade

PRA-⊤⇒⊤≾𝟏 : PRA ⊤ᵣ → ⊤ᵣ ≾ᵣ 𝟏ᵣ
PRA-⊤⇒⊤≾𝟏 pra = PRA⇒unit-maximal pra (≾-⊤ᵣ 𝟏ᵣ)
