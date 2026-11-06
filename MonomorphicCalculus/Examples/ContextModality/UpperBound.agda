------------------------------------------------------------------------
-- The context modality at upper bounds on time                       --
--                                                                    --
-- The example                                                        --
--   `ρ = [0,2]` and `Γ = Γ₀ ⟨ [0,1] ⟩ ∷ A ⟨ [0,1] ⟩` with            --
--   `Γ₀ = [] ∷ B`, where `B = [ [0,0] ] unit` and                    --
--   `A = [ [0,1] ] unit` (both non-eternal). Four objects of         --
--   `(Γ ↓ L_[0,2])`, by what they cut:                               --
--                                                                    --
--     Δ₁ = Γ₀                  both modalities and `A`               --
--     Δ₂ = Γ₀ ⟨ [0,1] ⟩ ∷ A    the last modality                     --
--     Δ₃ = Γ                   nothing (`⟨⟩-η-ren`, `⟨⟩-≤-ren`)      --
--     Δ₄ = Γ₀ ⟨ [0,1] ⟩        the last modality and `A`             --
--                                                                    --
-- What it shows                                                      --
--   The zig-zag `Δ₁ → Δ₄ ← Δ₂ → Δ₃` commutes with the structure maps --
--   up to `_≐ʳ_` (`zigzag`), and `Δ₁` and `Δ₂` have no common        --
--   source. So the comma category has no initial object, and         --
--   `L_[0,2]` is not a parametric right adjoint (`not-PRA-[0,2]`).   --
--                                                                    --
--   With `Γ₀ = []` (eternal) the same shape has the initial object   --
--   `[] ∷ A` (`initial-at-eternal-Γ₀`): the obstruction needs a      --
--   non-eternal variable behind the cut modality.                    --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (¬_)

open import Grades.Base
open import Grades.Examples.Time.UpperBound
open import Grades.Examples.System.Identity using (identityGradeSystem)
open import Language.BaseTypes using (noBaseTypes)
open import Language.Spec
import Language.Operations as Ops

open import Util.Equality

module MonomorphicCalculus.Examples.ContextModality.UpperBound where

G : GradeSystem
G = identityGradeSystem upper-bounds

ops : Ops.Operations G noBaseTypes
ops = record
  { Op = ⊥ ; _≟ₒ_ = λ () ; param = λ () ; arity = λ () ; op-grade = λ () }

spec : LanguageSpec
spec = withoutBaseTypes G ops

open GradeSystemInterface G

open import MonomorphicCalculus.Syntax.Contexts             spec
open import MonomorphicCalculus.Syntax.Types                spec
open import MonomorphicCalculus.Syntax.Renaming             spec
open import MonomorphicCalculus.Syntax.Renaming.Equivalence spec
open import MonomorphicCalculus.Syntax.Renaming.ContextModality        spec

[0,_]ⁿ : _ → R
[0, n ]ⁿ = [0, ↑ n ]

ρ : R
ρ = [0, 2 ]ⁿ

-- the grade's own order decides the side conditions

[0,1]≰𝟏 : ¬ ([0, 1 ]ⁿ ≾ᵣ 𝟏ᵣ)
[0,1]≰𝟏 ()

open Counterexample {σ = [0, 1 ]ⁿ} {σ' = [0, 1 ]ⁿ} {ρ = ρ} [0,1]≰𝟏 (s≤s z≤n) ≾ᵣ-refl public

Γ₀ : Ctx
Γ₀ = [] ∷ B

-- `Γᶜ` of the counterexample is the example's `Γ`

Γ-is : Γᶜ ≡ ((Γ₀ ⟨ [0, 1 ]ⁿ ⟩) ∷ A) ⟨ [0, 1 ]ⁿ ⟩
Γ-is = refl

X₃ X₄ : Comma ρ Γᶜ
X₃ = Γᶜ ,ᵒ (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η-ren)
X₄ = (Γ₀ ⟨ [0, 1 ]ⁿ ⟩) ,ᵒ (⟨⟩-≤-ren (s≤s z≤n) ∘ʳ cong-⟨⟩-ren wk-ren)

-- Δ₁ → Δ₄: add a modality (`[0,0] ≾ [0,1]`)

h₁₄ : CommaHom X₁ X₄
h₁₄ = (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η-ren) ,ʰ mk≐ʳ tri'
  where
  tri' : ∀ {C σ} → (x : C ∈[ σ ] (ctx X₄ ⟨ ρ ⟩)) → _
  tri' (Tl-⟨⟩ (Tl-⟨⟩ Hd))         = refl
  tri' (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ ())))

-- Δ₂ → Δ₄: weakening

h₂₄ : CommaHom X₂ X₄
h₂₄ = wk-ren ,ʰ mk≐ʳ tri'
  where
  tri' : ∀ {C σ} → (x : C ∈[ σ ] (ctx X₄ ⟨ ρ ⟩)) → _
  tri' (Tl-⟨⟩ (Tl-⟨⟩ Hd))         = refl
  tri' (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ ())))

-- Δ₂ → Δ₃: add a modality (`[0,0] ≾ [0,1]`)

h₂₃ : CommaHom X₂ X₃
h₂₃ = (⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η-ren) ,ʰ mk≐ʳ tri'
  where
  tri' : ∀ {C σ} → (x : C ∈[ σ ] (ctx X₃ ⟨ ρ ⟩)) → _
  tri' (Tl-⟨⟩ (Tl-⟨⟩ Hd))                        = refl
  tri' (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))         = refl
  tri' (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ ())))))

zigzag : Zigzag X₁ X₃
zigzag = fwd h₁₄ (bwd h₂₄ (fwd h₂₃ here))

not-PRA-[0,2] : ¬ PRA ρ
not-PRA-[0,2] = not-PRA

------------------------------------------------------------------------
-- With `Γ₀ = []` the same shape has an initial object `[] ∷ A`

module EternalPrefix where

  Γᵉ : Ctx
  Γᵉ = (([] ⟨ [0, 1 ]ⁿ ⟩) ∷ A) ⟨ [0, 1 ]ⁿ ⟩

  Iᵉ : Comma ρ Γᵉ
  Iᵉ = ([] ∷ A) ,ᵒ (⟨⟩-≤-ren (s≤s z≤n) ∘ʳ cong-⟨⟩-ren (cong-∷-ren (⟨⟩-ext-ctx ec-[] ec-[])))

  only-A : ∀ {C σ} → C ∈[ σ ] Γᵉ → C ≡ A
  only-A (Tl-⟨⟩ Hd)                 = refl
  only-A (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ ())))

  pos-unique : ∀ {C} → (p q : Var Γᵉ C) → p ≡ q
  pos-unique (_ , Tl-⟨⟩ Hd) (_ , Tl-⟨⟩ Hd)    = refl
  pos-unique (_ , Tl-⟨⟩ Hd) (_ , Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ ())))
  pos-unique (_ , Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ ()))) _

  pos-unique-A : ∀ {C} → (p q : Var ([] ∷ A) C) → p ≡ q
  pos-unique-A (_ , Hd) (_ , Hd)   = refl
  pos-unique-A (_ , Hd) (_ , Tl-∷ ())
  pos-unique-A (_ , Tl-∷ ()) _

  -- every context whose variables all have type `A` is reached from `[] ∷ A`

  build : (Δ : Ctx) → (∀ {C σ} → C ∈[ σ ] Δ → C ≡ A) → Ren [] ([] ∷ A) Δ
  build []        _  = wk-ctx-ren ec-[] _
  build (Δ ∷ C)   ok with ok Hd
  ... | refl = extend-ren (build Δ (λ x → ok (Tl-∷ x))) Hd (≾ᵘ-ok ≾ᵣ-refl)
  build (Δ ⟨ σ ⟩) ok =
    ⟨⟩-≤-ren (𝟏ₒ-least σ) ∘ʳ (⟨⟩-η-ren ∘ʳ build Δ (λ x → ok (Tl-⟨⟩ x)))

  initial-at-eternal-Γ₀ : Initial Iᵉ
  initial-at-eternal-Γ₀ X =
      (g ,ʰ mk≐ʳ (λ x → pos-unique _ _))
    , λ h' → mk≐ʳ (λ x → pos-unique-A _ _)
    where
    g : Ren [] ([] ∷ A) (ctx X)
    g = build (ctx X) (λ x → only-A (proj₂ (var-img (str X) (Tl-⟨⟩ x))))
