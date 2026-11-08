------------------------------------------------------------------------
-- The context modality at upper bounds on time                       --
--                                                                    --
-- The example                                                        --
--   `ρ = [0,2]` and `Γ = Γ₀ ⟨ [0,1] ⟩ ∷ A ⟨ [0,1] ⟩` with            --
--   `Γ₀ = [] ∷ B`, where `B = [ [0,0] ] unit` and                    --
--   `A = [ [0,1] ] unit` (both noneternal). Four renamings           --
--   `fᵢ : Γ → Δᵢ ⟨ [0,2] ⟩`, by what they cut:                       --
--                                                                    --
--     Δ₁ = Γ₀                  both modalities and `A`               --
--     Δ₂ = Γ₀ ⟨ [0,1] ⟩ ∷ A    the last modality                     --
--     Δ₃ = Γ                   nothing (`⟨⟩-η-ren`, `⟨⟩-≤-ren`)      --
--     Δ₄ = Γ₀ ⟨ [0,1] ⟩        the last modality and `A`             --
--                                                                    --
-- What it shows                                                      --
--   The renamings `h₁₄ : Δ₁ → Δ₄`, `h₂₄ : Δ₂ → Δ₄` and               --
--   `h₂₃ : Δ₂ → Δ₃` satisfy `L_[0,2] h ∘ fᵢ ≐ʳ fⱼ` (`tri₁₄`,         --
--   `tri₂₄`, `tri₂₃`). No context `I` with a renaming                --
--   `Γ → I ⟨ [0,2] ⟩` has renamings into both `Δ₁` and `Δ₂`          --
--   (`no-common-source`). So `Ren [] Γ (_ ⟨ [0,2] ⟩)` has no         --
--   representation, although there is an `s : Γ → [] ⟨ [0,2] ⟩`,     --
--   and `L_[0,2]` is not a parametric right adjoint                  --
--   (`not-PRA-[0,2]`).                                               --
--                                                                    --
--   With `Γ₀ = []` (eternal) the same shape is represented by        --
--   `[] ∷ A` (`representation-at-eternal-Γ₀`): the obstruction needs --
--   a noneternal variable behind the cut modality.                   --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (¬_)

open import Grades.Base
open import Grades.Examples.Time.UpperBound
open import Grades.Examples.System.Identity using (identity-grade-system)
open import Language.BaseTypes using (noBaseTypes)
open import Language.Spec
import Language.Operations as Ops

open import Util.Equality

module MonomorphicCalculus.Examples.ContextModality.UpperBound where

G : GradeSystem
G = identity-grade-system upper-bound

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

Δ₃ Δ₄ : Ctx
Δ₃ = Γᶜ
Δ₄ = Γ₀ ⟨ [0, 1 ]ⁿ ⟩

f₃ : Ren [] Γᶜ (Δ₃ ⟨ ρ ⟩)
f₃ = ⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η-ren

f₄ : Ren [] Γᶜ (Δ₄ ⟨ ρ ⟩)
f₄ = ⟨⟩-≤-ren (s≤s z≤n) ∘ʳ cong-⟨⟩-ren wk-ren

-- Δ₁ → Δ₄: add a modality (`[0,0] ≾ [0,1]`)

h₁₄ : Ren [] Δ₁ Δ₄
h₁₄ = ⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η-ren

tri₁₄ : (cong-⟨⟩-ren h₁₄ ∘ʳ f₁) ≐ʳ f₄
tri₁₄ = mk≐ʳ go
  where
  go : ∀ {C σ} → (x : C ∈[ σ ] (Δ₄ ⟨ ρ ⟩))
     → var-img (cong-⟨⟩-ren h₁₄ ∘ʳ f₁) x ≡ var-img f₄ x
  go (Tl-⟨⟩ (Tl-⟨⟩ Hd))         = refl
  go (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ ())))

-- Δ₂ → Δ₄: weakening

h₂₄ : Ren [] Δ₂ Δ₄
h₂₄ = wk-ren

tri₂₄ : (cong-⟨⟩-ren h₂₄ ∘ʳ f₂) ≐ʳ f₄
tri₂₄ = mk≐ʳ go
  where
  go : ∀ {C σ} → (x : C ∈[ σ ] (Δ₄ ⟨ ρ ⟩))
     → var-img (cong-⟨⟩-ren h₂₄ ∘ʳ f₂) x ≡ var-img f₄ x
  go (Tl-⟨⟩ (Tl-⟨⟩ Hd))         = refl
  go (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ ())))

-- Δ₂ → Δ₃: add a modality (`[0,0] ≾ [0,1]`)

h₂₃ : Ren [] Δ₂ Δ₃
h₂₃ = ⟨⟩-≤-ren z≤n ∘ʳ ⟨⟩-η-ren

tri₂₃ : (cong-⟨⟩-ren h₂₃ ∘ʳ f₂) ≐ʳ f₃
tri₂₃ = mk≐ʳ go
  where
  go : ∀ {C σ} → (x : C ∈[ σ ] (Δ₃ ⟨ ρ ⟩))
     → var-img (cong-⟨⟩-ren h₂₃ ∘ʳ f₂) x ≡ var-img f₃ x
  go (Tl-⟨⟩ (Tl-⟨⟩ Hd))                        = refl
  go (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))         = refl
  go (Tl-⟨⟩ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ ())))))

not-PRA-[0,2] : ¬ PRA ρ
not-PRA-[0,2] = not-PRA

------------------------------------------------------------------------
-- With `Γ₀ = []` the same shape is represented by `[] ∷ A`

module EternalPrefix where

  Γᵉ : Ctx
  Γᵉ = (([] ⟨ [0, 1 ]ⁿ ⟩) ∷ A) ⟨ [0, 1 ]ⁿ ⟩

  ηᵉ : Ren [] Γᵉ (([] ∷ A) ⟨ ρ ⟩)
  ηᵉ = ⟨⟩-≤-ren (s≤s z≤n) ∘ʳ cong-⟨⟩-ren (cong-∷-ren (⟨⟩-ext-ctx ec-[] ec-[]))

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

  -- any two renamings out of `Γᵉ`, or out of `[] ∷ A`, agree

  representation-at-eternal-Γ₀ : HomIso ρ Γᵉ ([] ∷ A)
  representation-at-eternal-Γ₀ = record
    { φ      = λ g → cong-⟨⟩-ren g ∘ʳ ηᵉ
    ; ψ      = λ {Δ} f → build Δ (λ x → only-A (proj₂ (var-img f (Tl-⟨⟩ x))))
    ; φ-cong = λ _ → mk≐ʳ (λ _ → pos-unique _ _)
    ; ψ-cong = λ _ → mk≐ʳ (λ _ → pos-unique-A _ _)
    ; ψ∘φ    = λ _ → mk≐ʳ (λ _ → pos-unique-A _ _)
    ; φ∘ψ    = λ _ → mk≐ʳ (λ _ → pos-unique _ _)
    ; φ-nat  = λ _ _ → mk≐ʳ (λ _ → pos-unique _ _)
    }
