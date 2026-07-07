------------------------------------------------------------------------
-- The box modality `[ ρ ] A` on discretely-indexed presheaves, given  --
-- the *Kripke necessity* semantics over the graded accessibility       --
-- relation on worlds:                                                  --
--                                                                    --
--   carrier ([ ρ ]ᵒ A) w  =  ∀ {w'} → w ⊑[ ρ ] w' → carrier A w'       --
--                                                                    --
-- i.e. `[ ρ ] A` holds at `w` when `A` holds at every world reachable  --
-- from `w` by spending the resource grade `ρ`. This is a lax graded    --
-- comonad (counit `ε`, comultiplication `δ`), packaged as an instance  --
-- of `DenotationalSemantics.Model.Modality.Future`.                     --
--                                                                    --
-- Every coherence law reduces, via function extensionality, to the    --
-- proof irrelevance of the accessibility relation: the two sides       --
-- feed `A` two witnesses of the *same* accessibility fact, which are   --
-- equal by `⊑-irrelevant`.                                             --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Modality.Future (Rg : Grade) (Wld : World Rg) where

open import Util.Equality

open Grade Rg renaming (Carrier to R)
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base Rg Wld

-- two-sided monotonicity of `·`

·-mono-≾ : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≾ ρ₁' → ρ₂ ≾ ρ₂' → ρ₁ · ρ₂ ≾ ρ₁' · ρ₂'
·-mono-≾ p q = ≾-trans (·-monoˡ-≾ p) (·-monoʳ-≾ q)

-- STRUCTURE

-- Functor

[_]ᵒ : R → PSh → PSh
[ ρ ]ᵒ A = psh (λ w → ∀ {w'} → w ⊑[ ρ ] w' → carrier A w')

[_]ᶠ : ∀ {A B} → (ρ : R) → A →ᵖ B → [ ρ ]ᵒ A →ᵖ [ ρ ]ᵒ B
[ ρ ]ᶠ f = pmap (λ x p → app f (x p))

-- Monotonicity for gradings (covariant: a larger budget is weaker)

[]-≤ : ∀ {A ρ₁ ρ₂} → ρ₁ ≾ ρ₂ → [ ρ₁ ]ᵒ A →ᵖ [ ρ₂ ]ᵒ A
[]-≤ p = pmap (λ x q → x (⊑-mono p q))

-- Counit

ε : ∀ {A} → [ u ]ᵒ A →ᵖ A
ε = pmap (λ x → x ⊑-refl)

-- Comultiplication

δ : ∀ {A ρ₁ ρ₂} → [ ρ₁ · ρ₂ ]ᵒ A →ᵖ [ ρ₁ ]ᵒ ([ ρ₂ ]ᵒ A)
δ = pmap (λ x p q → x (⊑-trans p q))


-- PROPERTIES

-- [_] is functorial

[]-idᵖ : ∀ {A ρ} → [ ρ ]ᶠ (idᵖ {A = A}) ≡ idᵖ
[]-idᵖ = →ᵖ-ext (λ x → refl)

[]-∘ᵖ : ∀ {A B C ρ} → (f : A →ᵖ B) → (g : B →ᵖ C)
      → [ ρ ]ᶠ (g ∘ᵖ f) ≡ [ ρ ]ᶠ g ∘ᵖ [ ρ ]ᶠ f
[]-∘ᵖ f g = →ᵖ-ext (λ x → refl)

-- []-≤ is natural

[]-≤-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵖ B) → (p : ρ₁ ≾ ρ₂)
         → [ ρ₂ ]ᶠ f ∘ᵖ []-≤ {A = A} p ≡ []-≤ {A = B} p ∘ᵖ [ ρ₁ ]ᶠ f
[]-≤-nat f p = →ᵖ-ext (λ x → refl)

-- [_] is functorial in the gradings

[]-≤-refl : ∀ {A ρ} → []-≤ {A} (≾-refl {ρ}) ≡ idᵖ
[]-≤-refl = →ᵖ-ext (λ x → ifun-ext (fun-ext (λ p → cong (λ r → x r) (⊑-irrelevant _ _))))

[]-≤-trans : ∀ {A ρ ρ' ρ''} → (p : ρ ≾ ρ') → (q : ρ' ≾ ρ'')
           → []-≤ {A} q ∘ᵖ []-≤ {A} p ≡ []-≤ {A} (≾-trans p q)
[]-≤-trans p q = →ᵖ-ext (λ x → ifun-ext (fun-ext (λ r → cong (λ s → x s) (⊑-irrelevant _ _))))

-- ε is natural

[]-ε-nat : ∀ {A B} → (f : A →ᵖ B) → f ∘ᵖ ε ≡ ε ∘ᵖ [ u ]ᶠ f
[]-ε-nat f = →ᵖ-ext (λ x → refl)

-- δ is natural

[]-δ-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵖ B)
         → [ ρ₁ ]ᶠ ([ ρ₂ ]ᶠ f) ∘ᵖ δ {A} ≡ δ {B} ∘ᵖ [ ρ₁ · ρ₂ ]ᶠ f
[]-δ-nat f = →ᵖ-ext (λ x → refl)

-- δ is compatible with the gradings

[]-δ-≤ : ∀ {A ρ₁ ρ₂ ρ₁' ρ₂'} → (p : ρ₁ ≾ ρ₁') → (q : ρ₂ ≾ ρ₂')
       → [ ρ₁' ]ᶠ ([]-≤ {A} q) ∘ᵖ []-≤ {[ ρ₂ ]ᵒ A} p ∘ᵖ δ {A = A}
       ≡ δ {A} ∘ᵖ []-≤ {A} (·-mono-≾ p q)
[]-δ-≤ p q =
  →ᵖ-ext (λ x →
    ifun-ext (fun-ext (λ a →
    ifun-ext (fun-ext (λ b →
      cong (λ r → x r) (⊑-irrelevant _ _))))))

-- Graded comonad laws

[]-ε∘δ≡id : ∀ {A ρ}
          → ε {[ ρ ]ᵒ A} ∘ᵖ δ {A} {u} {ρ}
          ≡ []-≤ {A = A} (≾-reflexive (·-identityˡ ρ))
[]-ε∘δ≡id = →ᵖ-ext (λ x → ifun-ext (fun-ext (λ p → cong (λ r → x r) (⊑-irrelevant _ _))))

[]-Dε∘δ≡id : ∀ {A ρ}
           → [ ρ ]ᶠ (ε {A}) ∘ᵖ δ {A} {ρ} {u}
           ≡ []-≤ {A} (≾-reflexive (·-identityʳ ρ))
[]-Dε∘δ≡id = →ᵖ-ext (λ x → ifun-ext (fun-ext (λ a → cong (λ r → x r) (⊑-irrelevant _ _))))

[]-δ∘δ≡Dδ∘δ : ∀ {A ρ₁ ρ₂ ρ₃}
            → δ {[ ρ₃ ]ᵒ A} {ρ₁} {ρ₂} ∘ᵖ δ {A} {ρ₁ · ρ₂} {ρ₃}
            ≡    [ ρ₁ ]ᶠ (δ {A} {ρ₂} {ρ₃}) ∘ᵖ δ {A} {ρ₁} {ρ₂ · ρ₃}
              ∘ᵖ []-≤ {A} (≾-reflexive (·-assoc ρ₁ ρ₂ ρ₃))
[]-δ∘δ≡Dδ∘δ =
  →ᵖ-ext (λ x →
    ifun-ext (fun-ext (λ c →
    ifun-ext (fun-ext (λ d →
    ifun-ext (fun-ext (λ b →
      cong (λ r → x r) (⊑-irrelevant _ _))))))))


-- Packaging the box modality up as a `Future` instance

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future PShCat Rg using (Future)

PShFut : Future
PShFut = record
  { [_]ᵒ        = [_]ᵒ
  ; [_]ᶠ        = [_]ᶠ
  ; []-≤        = λ {A} → []-≤ {A}
  ; ε           = ε
  ; δ           = λ {A} → δ {A}
  ; []-idᵐ      = λ {A} → []-idᵖ {A}
  ; []-∘ᵐ       = []-∘ᵖ
  ; []-≤-nat    = []-≤-nat
  ; []-≤-refl   = λ {A} → []-≤-refl {A}
  ; []-≤-trans  = λ {A} p q → []-≤-trans {A} p q
  ; []-ε-nat    = []-ε-nat
  ; []-δ-nat    = []-δ-nat
  ; []-δ-≤      = λ {A} p q → []-δ-≤ {A} p q
  ; []-ε∘δ≡id   = λ {A} → []-ε∘δ≡id {A}
  ; []-Dε∘δ≡id  = λ {A} → []-Dε∘δ≡id {A}
  ; []-δ∘δ≡Dδ∘δ = λ {A} → []-δ∘δ≡Dδ∘δ {A}
  }
