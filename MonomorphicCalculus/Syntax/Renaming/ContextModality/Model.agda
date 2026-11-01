-----------------------------------------------------------------------
-- A Kripke model of contexts over the grades, preserved by every    --
-- renaming, used in showing when the ctx. modality is not a PRA.    --
--                                                                   --
-- Worlds are the grades satisfying `W`, and `w' ⊑[ σ ] w` when      --
-- `w ≃ w' · τ` for some `τ ≾ σ`: the exact form of the action frame --
-- (`DenotationalSemantics/Model/World/Action`), which relates `w'`  --
-- to everything below `w' · σ`. Types are predicates on worlds,     --
-- closed along steps within the unit. A box type `[ σ ] A` holds at --
-- the worlds `σ · τ` with `τ ≾ 𝟏` (`AtUnit`), every other type      --
-- holds everywhere, so eternal types are constant. The context      --
-- modality is possibility: `Γ ⟨ ρ ⟩` holds at `w` when `Γ` holds at --
-- some world `w' ⊑[ ρ ] w`.                                         --
--                                                                   --
-- Every renaming maps a point of its source to a point of its       --
-- target at the same world (`sound`), so a world where the source   --
-- holds and the target fails refutes a renaming.                    --
-----------------------------------------------------------------------

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)

open import Relation.Nullary using (yes; no)

open import Grades.Base
open import Language.Spec

module MonomorphicCalculus.Syntax.Renaming.ContextModality.Model (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Types    S
open import MonomorphicCalculus.Syntax.Renaming S

module KripkeModel (W : R → Set) where

  record _⊑[_]_ (w' σ w : R) : Set where
    constructor step
    field
      τ     : R
      bound : τ ≾ᵣ σ
      eq    : w ≃ᵣ w' ·ᵣ τ

  ⊑-refl : ∀ {w} → w ⊑[ 𝟏ᵣ ] w
  ⊑-refl {w} = step 𝟏ᵣ ≾ᵣ-refl (≃ᵣ-sym (·ᵣ-identityʳ w))

  ⊑-trans : ∀ {w'' w' w ρ ρ'} → w'' ⊑[ ρ ] w' → w' ⊑[ ρ' ] w
          → w'' ⊑[ ρ ·ᵣ ρ' ] w
  ⊑-trans {w''} (step τ p e) (step τ' p' e') =
    step (τ ·ᵣ τ')
         (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (·ᵣ-monoʳ-≾ᵣ p'))
         (≃ᵣ-trans e' (≃ᵣ-trans (·ᵣ-cong e ≃ᵣ-refl) (·ᵣ-assoc w'' τ τ')))

  ⊑-mono : ∀ {w' w σ σ'} → σ ≾ᵣ σ' → w' ⊑[ σ ] w → w' ⊑[ σ' ] w
  ⊑-mono q (step τ p e) = step τ (≾ᵣ-trans p q) e

  -- a step within the unit stays within a modality's reach

  ⊑-unit : ∀ {w'' w' w ρ σ} → w'' ⊑[ ρ ] w' → w' ⊑[ σ ] w → σ ≾ᵣ 𝟏ᵣ
         → w'' ⊑[ ρ ] w
  ⊑-unit {ρ = ρ} r s q =
    ⊑-mono (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ q) (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ))) (⊑-trans r s)

  record AtUnit (σ w : R) : Set where
    constructor at-unit
    field
      τ     : R
      bound : τ ≾ᵣ 𝟏ᵣ
      eq    : w ≃ᵣ σ ·ᵣ τ

  AtUnit-close : ∀ {σ₀ σ w' w} → AtUnit σ₀ w' → w' ⊑[ σ ] w → σ ≾ᵣ 𝟏ᵣ
               → AtUnit σ₀ w
  AtUnit-close {σ₀} (at-unit τ₀ p₀ e₀) (step τ p e) q =
    at-unit (τ₀ ·ᵣ τ)
      (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p₀)
        (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (≾ᵣ-trans p q)) (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ 𝟏ᵣ))))
      (≃ᵣ-trans e (≃ᵣ-trans (·ᵣ-cong e₀ ≃ᵣ-refl) (·ᵣ-assoc σ₀ τ₀ τ)))

  ⟦_⟧ᵛ : VType → R → Set
  ⟦ [ σ ] A ⟧ᵛ w = AtUnit σ w
  ⟦ _ ⟧ᵛ       w = Unit

  ty-close : ∀ {w' w σ} → (A : VType) → ⟦ A ⟧ᵛ w' → w' ⊑[ σ ] w → σ ≾ᵣ 𝟏ᵣ
           → ⟦ A ⟧ᵛ w
  ty-close (Base _)  a s q = tt
  ty-close unit      a s q = tt
  ty-close bool      a s q = tt
  ty-close nat       a s q = tt
  ty-close (_ |×| _) a s q = tt
  ty-close (_ |+| _) a s q = tt
  ty-close (list _)  a s q = tt
  ty-close empty     a s q = tt
  ty-close (_ ⇒ _)   a s q = tt
  ty-close (_ ⇛ _)   a s q = tt
  ty-close ([ _ ] _) a s q = AtUnit-close a s q

  et-any : ∀ {A w} → Et A → ⟦ A ⟧ᵛ w
  et-any (Baseₑ _)    = tt
  et-any unitₑ        = tt
  et-any boolₑ        = tt
  et-any natₑ         = tt
  et-any (_ |×|ₑ _)   = tt
  et-any (_ |+|ₑ _)   = tt
  et-any (listₑ _)    = tt
  et-any emptyₑ       = tt

  ⟦_⟧ᶜᵗˣ : Ctx → R → Set
  ⟦ [] ⟧ᶜᵗˣ      w = Unit
  ⟦ Γ ∷ A ⟧ᶜᵗˣ   w = ⟦ Γ ⟧ᶜᵗˣ w × ⟦ A ⟧ᵛ w
  ⟦ Γ ⟨ ρ ⟩ ⟧ᶜᵗˣ w = Σ[ w' ∈ R ] W w' × (w' ⊑[ ρ ] w) × ⟦ Γ ⟧ᶜᵗˣ w'

  ctx-close : ∀ {w' w σ} → (Γ : Ctx) → ⟦ Γ ⟧ᶜᵗˣ w' → w' ⊑[ σ ] w → σ ≾ᵣ 𝟏ᵣ
            → ⟦ Γ ⟧ᶜᵗˣ w
  ctx-close []        d                 s q = tt
  ctx-close (Γ ∷ A)   (d , a)           s q = ctx-close Γ d s q , ty-close A a s q
  ctx-close (Γ ⟨ ρ ⟩) (w'' , ω , r , d) s q = w'' , ω , ⊑-unit r s q , d

  lookup : ∀ {Γ A σ w} → A ∈[ σ ] Γ → ⟦ Γ ⟧ᶜᵗˣ w
         → Σ[ w' ∈ R ] (w' ⊑[ σ ] w) × ⟦ A ⟧ᵛ w'
  lookup {w = w} Hd (d , a) = w , ⊑-refl , a
  lookup (Tl-∷ x)  (d , _)  = lookup x d
  lookup (Tl-⟨⟩ x) (w' , _ , r , d) with lookup x d
  ... | w'' , r' , a = w'' , ⊑-trans r' r , a

  var-sound : ∀ {Γ A σ w} → A ∈[ σ ] Γ → .(A Et∨≾ᵘ σ) → ⟦ Γ ⟧ᶜᵗˣ w → ⟦ A ⟧ᵛ w
  var-sound {A = A} x ok d with lookup x d | eternal? A
  ... | _          | yes et = et-any et
  ... | w' , r , a | no ¬et = ty-close A a r (Et∨≾ᵘ→¬Et⇒≾ ok ¬et)

  ec-const : ∀ {Δ w' w} → W w → EternalCtx Δ → ⟦ Δ ⟧ᶜᵗˣ w' → ⟦ Δ ⟧ᶜᵗˣ w
  ec-const ω ec-[]            d       = tt
  ec-const ω (ec-∷ ec et)     (d , a) = ec-const ω ec d , et-any et
  ec-const {w = w} ω (ec-⟨⟩ q p ec) (w'' , ω'' , _ , d) =
    w , ω , step 𝟏ᵣ q (≃ᵣ-sym (·ᵣ-identityʳ w)) , ec-const ω ec d

  sound : ∀ {Γ Γ' w} → W w → Ren [] Γ Γ' → ⟦ Γ ⟧ᶜᵗˣ w → ⟦ Γ' ⟧ᶜᵗˣ w
  sound ω id-ren                d                      = d
  sound ω (r₂ ∘ʳ r₁)            d                      = sound ω r₂ (sound ω r₁ d)
  sound ω wk-ren                (d , _)                = d
  sound ω (var-ren x ok)        d                      = d , var-sound x ok d
  sound {w = w} ω ⟨⟩-η-ren      d                      = w , ω , ⊑-refl , d
  sound {Γ = Γ ⟨ _ ⟩} ω ⟨⟩-η⁻¹-ren (w' , _ , r , d)   = ctx-close Γ d r ≾ᵣ-refl
  sound ω ⟨⟩-μ-ren   (w' , _ , r' , w'' , ω'' , r'' , d) = w'' , ω'' , ⊑-trans r'' r' , d
  sound ω (⟨⟩-≤-ren p)          (w' , ω' , r , d)      = w' , ω' , ⊑-mono p r , d
  sound ω (⟨⟩-ext-ctx _ ec)     (w' , _ , _ , d)       = ec-const ω ec d
  sound ω (cong-∷-ren r)        (d , a)                = sound ω r d , a
  sound ω (cong-⟨⟩-ren r)       (w' , ω' , s , d)      = w' , ω' , s , sound ω' r d
