-------------------------------------------------------------------------
-- The algebraic operations and delays of the effect monad. Both       --
-- mention the box modality graded by the *resource* projection `mapᵉ` --
-- of the relevant effect grade, and store that box's Kripke value as  --
-- the node's continuation, rebuilding the node's coherence witnesses  --
-- from the box's (and, for operations, the exponential's) naturality. --
--                                                                     --
-- (The monad's `[-]`-strength is core structure and lives in `Core`.) --
-------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Effects
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Product using (_,_; proj₁; proj₂)

open import Util.Equality

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ; map⇒ᵐ; fstᵐ; sndᵐ; ⟨_,_⟩ᵐ)

-- A delay: its continuation box `[ of-durʳ τ ]` is stored in the
-- delay-node; the node's naturality is the box's own `fun-nat`.

delayᵀ : ∀ {A ε} → (τ : 𝔻)
       → [ of-durʳ τ ]ᵒ (Tᵒ A ε) →ᵖ Tᵒ A (of-durᵉ τ ·ₑ ε)
delayᵀ τ = pmap
  (λ x → delay-node τ (λ q → fun x (⊑-mono (≃ᵣ⇒≾ᵣ map-of-durᵉ) q))
           (λ q r → ≈ᵗ-trans ([]-fun-irr x _ _) (fun-nat x (⊑-mono (≃ᵣ⇒≾ᵣ map-of-durᵉ) q) r)))
  (λ e → delay-≈ (λ q → e (⊑-mono (≃ᵣ⇒≾ᵣ map-of-durᵉ) q)))
  (λ p x → delay-≈ (λ q → []-fun-irr x _ _))

-- An algebraic operation: its boxed continuation `x` is applied at the
-- reached world (via the exponential's `fun` at the reflexive witness)
-- to obtain the op-node's stored continuation; the node's congruence and
-- naturality come from the exponential's `fun-cong`/`fun-nat` and the
-- box's `fun-nat`.

opᵀ : ∀ {A ε} → (op : Op)
    → ⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε)
    →ᵖ Tᵒ A (op-grade op ·ₑ ε)
opᵀ op = pmap
  (λ { (v , x) → op-node op v (λ q y → fun (fun x q) ⊑-refl y)
                   (λ q e → fun-cong (fun x q) ⊑-refl e)
                   (λ q r y → ≈ᵗ-trans (fun-nat x q r ⊑-refl (transport ⟦ arity op ⟧ᵍ r y))
                     (≈ᵗ-trans (fun-irr (fun x q) _ _ (transport ⟦ arity op ⟧ᵍ r y))
                               (fun-nat (fun x q) ⊑-refl r y))) })
  (λ { (ev , ex) → op-≈ ev (λ q y → ex q ⊑-refl y) })
  (λ { p (v , x) → op-≈ (≈-refl ⟦ param op ⟧ᵍ) (λ q y → ≈ᵗ-refl _) })

-- Delays are the passage of time: a zero delay is no delay (its box is the
-- unit-graded one, whose counit `ε` extracts), and consecutive delays merge
-- (the merged box splits by `δ`). Both are the corresponding rules of `_≈ᵗ_`,
-- the accessibility witnesses being reconciled by `[]-fun-irr`.

delayᵀ-zero : ∀ {A ε'}
            → delayᵀ {A} {ε'} 0ᴰ
            ≈ᵖ T-≤ (≃ₑ⇒≿ₑ (≃ₑ-trans (·ₑ-cong of-durᵉ-zero ≃ₑ-refl) (·ₑ-identityˡ ε')))
              ∘ᵖ ε
              ∘ᵖ []-≤ (≃ᵣ⇒≿ᵣ of-durʳ-zero)
delayᵀ-zero x =
  ≈ᵗ-trans (delay-zero {q₀ = ⊑-delay0} delay0ᵉ)
           (sub-≈ ([]-fun-irr x _ _))

delayᵀ-plus : ∀ {A ε'} → (τ₁ τ₂ : 𝔻)
            → delayᵀ {A} {of-durᵉ τ₂ ·ₑ ε'} τ₁
                ∘ᵖ [ of-durʳ τ₁ ]ᶠ (delayᵀ {A} {ε'} τ₂)
                ∘ᵖ δ
                ∘ᵖ []-≤ (≃ᵣ⇒≿ᵣ of-durʳ-plus)
            ≈ᵖ T-≤ (≃ₑ⇒≾ₑ (≃ₑ-trans (·ₑ-cong of-durᵉ-plus ≃ₑ-refl) (·ₑ-assoc (of-durᵉ τ₁) (of-durᵉ τ₂) ε')))
              ∘ᵖ delayᵀ {A} {ε'} (τ₁ +ᴰ τ₂)
delayᵀ-plus τ₁ τ₂ x =
  ≈ᵗ-trans (delay-plus (λ q₁ q₂ → []-fun-irr x _ _) delay+ᵉ) (sub-≈ (≈ᵗ-refl _))

-- Naturality

delayᵀ-nat : ∀ {A B ε} → (τ : 𝔻) → (f : A →ᵖ B)
           → delayᵀ {ε = ε} τ ∘ᵖ [ of-durʳ τ ]ᶠ (Tᶠ f) ≈ᵖ Tᶠ f ∘ᵖ delayᵀ τ
delayᵀ-nat τ f x = delay-≈ (λ q → ≈ᵗ-refl _)

-- Sub-effecting the delayed computation is sub-effecting the delay: the `sub`
-- the coercion leaves in each continuation may be pulled out past the delay
-- node, because the grade it coerces factors through the delay's own
-- (`sub-delay`). This is what makes `T-≤` commute with the multiplication in
-- the *inner* grade, and hence what lets the `↝*` closure compose.

delayᵀ-≤ : ∀ {A ε ε'} → (τ : 𝔻) → (p : ε ≾ₑ ε')
         → delayᵀ {A} {ε'} τ ∘ᵖ [ of-durʳ τ ]ᶠ (T-≤ p)
         ≈ᵖ T-≤ (·ₑ-monoʳ-≾ₑ p) ∘ᵖ delayᵀ {A} {ε} τ
delayᵀ-≤ τ p x =
  -- the two delay nodes agree on their continuations, differing only in the
  -- coherence witness `delay-≈` ignores
  ≈ᵗ-trans (delay-≈ (λ q → ≈ᵗ-refl _)) (≈ᵗ-sym (sub-delayᵗ p _ _))

-- `opᵀ` naturality crosses the exponential functor `map⇒ᵐ`, which in the
-- setoid model reindexes its argument by `transport ⊑-refl`; the discrepancy
-- is exactly `transport-refl` of the exponential.

opᵀ-nat : ∀ {A B ε} → (op : Op) → (f : A →ᵖ B)
        → opᵀ {ε = ε} op ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (Tᶠ f)))
        ≈ᵖ Tᶠ f ∘ᵖ opᵀ op
opᵀ-nat {A} {ε = ε} op f (v , x) =
  op-≈ (≈-refl ⟦ param op ⟧ᵍ)
    (λ q y → Tˢᶠ-congᵗ f (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε) (fun x q) ⊑-refl y))

-- Sub-effecting the continuation is sub-effecting the operation: the `sub` the
-- coercion leaves in each continuation pulls out past the op node (`sub-op`),
-- exactly as `delayᵀ-≤` does past a delay node. The `map⇒ᵐ` reindexing is
-- absorbed by `transport-refl`, as in `opᵀ-nat`.

opᵀ-≤ : ∀ {A ε ε'} → (op : Op) → (p : ε ≾ₑ ε')
      → opᵀ {A} {ε'} op ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (T-≤ p)))
      ≈ᵖ T-≤ (·ₑ-monoʳ-≾ₑ p) ∘ᵖ opᵀ {A} {ε} op
opᵀ-≤ {A} {ε = ε} op p (v , x) =
  ≈ᵗ-trans
    (op-≈ (≈-refl ⟦ param op ⟧ᵍ)
      (λ q y → sub-≈ (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε) (fun x q) ⊑-refl y)))
    (≈ᵗ-sym (sub-opᵗ p v _ _ _))

-- Algebraicity: the operations commute with the monad multiplication.

delayᵀ-algebraicity : ∀ {A ε' ε''} → (τ : 𝔻)
                    → μᵀ {A} {of-durᵉ τ ·ₑ ε'} {ε''} ∘ᵖ delayᵀ {ε = ε'} τ
                    ≈ᵖ T-≤ (≃ₑ⇒≿ₑ (·ₑ-assoc (of-durᵉ τ) ε' ε''))
                      ∘ᵖ delayᵀ τ ∘ᵖ [ of-durʳ τ ]ᶠ (μᵀ {A} {ε'} {ε''})
delayᵀ-algebraicity τ x = sub-≈ (delay-≈ (λ q → ≈ᵗ-refl _))

opᵀ-algebraicity : ∀ {A ε ε'} → (op : Op)
                 → μᵀ {A} {op-grade op ·ₑ ε} {ε'} ∘ᵖ opᵀ {ε = ε} op
                 ≈ᵖ T-≤ (≃ₑ⇒≿ₑ (·ₑ-assoc (op-grade op) ε ε'))
                   ∘ᵖ opᵀ op
                   ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (μᵀ {A} {ε} {ε'})))
opᵀ-algebraicity {A} {ε} {ε'} op (v , x) =
  sub-≈
    (op-≈ (≈-refl ⟦ param op ⟧ᵍ)
      (λ q y → μˢ-congᵗ
        (≈ᵗ-sym (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ (Tᵒ A ε') ε) (fun x q) ⊑-refl y))))

-- The delay is algebraic with respect to the strength. Both sides build the
-- same `delay-node`; under the delay each side strengths `x` at the reached
-- world with box witnesses that agree by `[]-fun-irr` (via `strˢ-congᵗ`).

strᵀ-delayᵀ-algebraicity : ∀ {A B ε} → (τ : 𝔻)
  → strᵀ {A} {B} {of-durᵉ τ ·ₑ ε} ∘ᵖ mapˣᵐ idᵖ (delayᵀ {B} {ε} τ)
  ≈ᵖ delayᵀ τ
    ∘ᵖ [ of-durʳ τ ]ᶠ (strᵀ {A} {B} {ε})
    ∘ᵖ []-monoidal
    ∘ᵖ mapˣᵐ (δ ∘ᵖ []-≤ (≃ᵣ⇒≿ᵣ
         (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl)))) idᵖ
strᵀ-delayᵀ-algebraicity {A} τ (a , x) =
  delay-≈ (λ q →
    strˢ-congᵗ A (λ r → []-fun-irr a _ _) (≈ᵗ-refl (fun x (⊑-mono (≃ᵣ⇒≾ᵣ map-of-durᵉ) q))))

