------------------------------------------------------------------------
-- The algebraic operations and delays of the effect monad. Both        --
-- mention the box modality graded by the *resource* projection `mapᵉ`  --
-- of the relevant effect grade; the effect accessibility `_⊑ᵉ[_]_`     --
-- used by the monad tree feeds the box via `⊑ᵉ-resource`.              --
--                                                                    --
-- (The monad's `[-]`-strength is core structure and lives in `Core`.)  --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.Monad.Effects
         (S : LanguageSpec)
         (Wld : World (LanguageSpec.Grades S))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

open import Util.Equality

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy

open import DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ; map⇒ᵐ)

-- OPERATIONS AND DELAYS

-- A delay: the box `[ of-natʳ τ ]` is entered by an effect step of
-- grade `of-natᵉ τ`, whose resource projection is `of-natʳ τ`.

delayᵀ : ∀ {A ε} → (τ : ℕ)
       → [ of-natʳ τ ]ᵒ (Tᵒ A ε) →ᵖ Tᵒ A (of-natᵉ τ ·ₑ ε)
delayᵀ τ =
  pmap (λ x → delay-node τ
    (λ q → x (⊑ʳ-mono (≾ᵣ-reflexive map-of-natᵉ) (⊑ᵉ-resource q))))

-- An algebraic operation.

opᵀ : ∀ {A ε} → (op : Op)
    → ⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε)
    →ᵖ Tᵒ A (op-grade op ·ₑ ε)
opᵀ op =
  pmap (λ { (v , x) → op-node op v (λ q y → x (⊑ᵉ-resource q) y) })

-- Naturality

delayᵀ-nat : ∀ {A B ε} → (τ : ℕ) → (f : A →ᵖ B)
           → delayᵀ {ε = ε} τ ∘ᵖ [ of-natʳ τ ]ᶠ (Tᶠ f) ≡ Tᶠ f ∘ᵖ delayᵀ τ
delayᵀ-nat τ f = →ᵖ-ext (λ x → refl)

opᵀ-nat : ∀ {A B ε} → (op : Op) → (f : A →ᵖ B)
        → opᵀ {ε = ε} op ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (Tᶠ f)))
        ≡ Tᶠ f ∘ᵖ opᵀ op
opᵀ-nat op f = →ᵖ-ext (λ { (v , x) → refl })

-- Algebraicity: the operations commute with the monad multiplication.

delayᵀ-algebraicity : ∀ {A ε' ε''} → (τ : ℕ)
                    → μᵀ {A} {of-natᵉ τ ·ₑ ε'} {ε''} ∘ᵖ delayᵀ {ε = ε'} τ
                    ≡ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                      ∘ᵖ delayᵀ τ ∘ᵖ [ of-natʳ τ ]ᶠ (μᵀ {A} {ε'} {ε''})
delayᵀ-algebraicity τ = →ᵖ-ext (λ x → refl)

opᵀ-algebraicity : ∀ {A ε ε'} → (op : Op)
                 → μᵀ {A} {op-grade op ·ₑ ε} {ε'} ∘ᵖ opᵀ {ε = ε} op
                 ≡ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                   ∘ᵖ opᵀ op
                   ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (μᵀ {A} {ε} {ε'})))
opᵀ-algebraicity op = →ᵖ-ext (λ { (v , x) → refl })
