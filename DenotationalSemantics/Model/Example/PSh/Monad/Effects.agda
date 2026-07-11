------------------------------------------------------------------------
-- The algebraic operations and delays of the effect monad. Both        --
-- mention the box modality graded by the *resource* projection `mapᵉ`  --
-- of the relevant effect grade, and simply *store* that box as the      --
-- node's continuation (so no information is discarded).                --
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
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)

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
open Category PShCat using (mapˣᵐ; map⇒ᵐ; fstᵐ; sndᵐ; ⟨_,_⟩ᵐ; curryᵐ; uncurryᵐ)

-- OPERATIONS AND DELAYS

-- A delay: its continuation box `[ of-natʳ τ ]` is stored in the
-- delay-node (whose continuation is indexed by `mapᵉ (of-natᵉ τ)`,
-- equal to `of-natʳ τ` via `map-of-natᵉ`).

delayᵀ : ∀ {A ε} → (τ : ℕ)
       → [ of-natʳ τ ]ᵒ (Tᵒ A ε) →ᵖ Tᵒ A (of-natᵉ τ ·ₑ ε)
delayᵀ τ = pmap
  (λ x → delay-node τ (λ q → fun x (⊑-coe map-of-natᵉ q)))
  (λ e → delay-≈ (λ q → e (⊑-coe map-of-natᵉ q)))
  (λ p x → delay-≈ (λ q → []-fun-irr x _ _))

-- An algebraic operation: its boxed continuation `x` is applied at the
-- reached world (via the exponential's `fun` at the reflexive witness)
-- to obtain the op-node's stored continuation.

opᵀ : ∀ {A ε} → (op : Op)
    → ⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε)
    →ᵖ Tᵒ A (op-grade op ·ₑ ε)
opᵀ op = pmap
  (λ { (v , x) → op-node op v (λ q y → fun (fun x q) ⊑-refl y) })
  (λ { (ev , ex) → op-≈ ev (λ q y → ex q ⊑-refl y) })
  (λ { p (v , x) → ≈ᵗ-refl _ })

-- Naturality

delayᵀ-nat : ∀ {A B ε} → (τ : ℕ) → (f : A →ᵖ B)
           → delayᵀ {ε = ε} τ ∘ᵖ [ of-natʳ τ ]ᶠ (Tᶠ f) ≈ᵖ Tᶠ f ∘ᵖ delayᵀ τ
delayᵀ-nat τ f x = ≈ᵗ-refl _

-- `opᵀ` naturality crosses the exponential functor `map⇒ᵐ`, which in the
-- setoid model reindexes its argument by `transport ⊑-refl`; the discrepancy
-- is exactly `transport-refl` of the exponential.

opᵀ-nat : ∀ {A B ε} → (op : Op) → (f : A →ᵖ B)
        → opᵀ {ε = ε} op ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (Tᶠ f)))
        ≈ᵖ Tᶠ f ∘ᵖ opᵀ op
opᵀ-nat {A} {ε = ε} op f (v , x) =
  op-≈ (≈-refl ⟦ param op ⟧ᵍ)
    (λ q y → Tˢᶠ-congᵗ f (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε) (fun x q) ⊑-refl y))

-- Algebraicity: the operations commute with the monad multiplication.

delayᵀ-algebraicity : ∀ {A ε' ε''} → (τ : ℕ)
                    → μᵀ {A} {of-natᵉ τ ·ₑ ε'} {ε''} ∘ᵖ delayᵀ {ε = ε'} τ
                    ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                      ∘ᵖ delayᵀ τ ∘ᵖ [ of-natʳ τ ]ᶠ (μᵀ {A} {ε'} {ε''})
delayᵀ-algebraicity τ x = ≈ᵗ-refl _

opᵀ-algebraicity : ∀ {A ε ε'} → (op : Op)
                 → μᵀ {A} {op-grade op ·ₑ ε} {ε'} ∘ᵖ opᵀ {ε = ε} op
                 ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                   ∘ᵖ opᵀ op
                   ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (μᵀ {A} {ε} {ε'})))
opᵀ-algebraicity {A} {ε} {ε'} op (v , x) =
  ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) ε ε'))
    (op-≈ (≈-refl ⟦ param op ⟧ᵍ)
      (λ q y → μˢ-congᵗ
        (≈ᵗ-sym (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ (Tᵒ A ε') ε) (fun x q) ⊑-refl y))))

-- The delay is algebraic with respect to the strength. Both sides build the
-- same `delay-node`; under the delay each side strengths `x` at the reached
-- world with box witnesses that agree by `⊑-irrelevant` (via `strˢ-cong`).

strᵀ-delayᵀ-algebraicity : ∀ {A B ε} → (τ : ℕ)
  → strᵀ {A} {B} {of-natᵉ τ ·ₑ ε} ∘ᵖ mapˣᵐ idᵖ (delayᵀ {B} {ε} τ)
  ≈ᵖ delayᵀ τ
    ∘ᵖ [ of-natʳ τ ]ᶠ (strᵀ {A} {B} {ε})
    ∘ᵖ []-monoidal
    ∘ᵖ mapˣᵐ (δ ∘ᵖ []-≤ (≾ᵣ-reflexive
         (sym (trans map-·ᵉ (cong (_·ᵣ mapᵉ ε) map-of-natᵉ))))) idᵖ
strᵀ-delayᵀ-algebraicity {A} τ (a , x) =
  ≡→≈ᵗ (cong (delay-node τ)
    (ifun-ext (fun-ext (λ q →
      strˢ-cong A (λ r → cong (fun a) (⊑-irrelevant _ _))
        (fun x (⊑-coe map-of-natᵉ q))))))

-- The operation is algebraic with respect to the strength. Both sides build
-- the same `op-node`; under it each side strengths the sub-computation with
-- box witnesses that agree by `⊑-irrelevant` (via `strˢ-cong`).

strᵀ-opᵀ-algebraicity : ∀ {A B ε} → (op : Op)
  → strᵀ {A} {B} {op-grade op ·ₑ ε} ∘ᵖ mapˣᵐ idᵖ (opᵀ {B} {ε} op)
  ≈ᵖ opᵀ op
    ∘ᵖ mapˣᵐ idᵖ
        ([ mapᵉ (op-grade op) ]ᶠ
           (   map⇒ᵐ idᵖ (strᵀ {A} {B} {ε})
            ∘ᵖ curryᵐ ⟨ fstᵐ ∘ᵖ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ)
         ∘ᵖ []-monoidal
         ∘ᵖ mapˣᵐ (δ ∘ᵖ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵖ)
    ∘ᵖ ⟨ fstᵐ ∘ᵖ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵖ sndᵐ ⟩ᵐ ⟩ᵐ
strᵀ-opᵀ-algebraicity {A} {B} {ε} op {w} (a , v , boxk) =
  op-≈ (≈-refl ⟦ param op ⟧ᵍ) (λ q y →
    ≈ᵗ-trans
      (strˢ-congᵗ A
        (λ r → ≈-sym A (transport-refl ([ mapᵉ ε ]ᵒ A) (C q) r))
        (≈ᵗ-sym (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ B ε) (fun boxk q) ⊑-refl y)))
      (≈ᵗ-sym (strˢ-congᵗ A
        (λ r → proj₁ (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ ([ mapᵉ ε ]ᵒ A ×ᵖ Tᵒ B ε)) (Cur q) ⊑-refl y) r)
        (proj₂ (transport-refl (⟦ arity op ⟧ᵍ ⇒ᵖ ([ mapᵉ ε ]ᵒ A ×ᵖ Tᵒ B ε)) (Cur q) ⊑-refl y)))))
  where
    C : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w' → [ mapᵉ ε ]ᶜ A w'
    C q = fun (app (δ {A} {mapᵉ (op-grade op)} {mapᵉ ε})
                   (app ([]-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) a)) q
    Cur : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w'
        → carrier (⟦ arity op ⟧ᵍ ⇒ᵖ ([ mapᵉ ε ]ᵒ A ×ᵖ Tᵒ B ε)) w'
    Cur q = app (curryᵐ ⟨ fstᵐ ∘ᵖ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ) (C q , fun boxk q)
