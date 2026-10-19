------------------------------------------------------------------------
-- The box modality `[ ρ ] A` on setoid-valued presheaves, with the    --
-- *Kripke necessity* semantics over the graded accessibility relation  --
-- on worlds. An element of `[ ρ ]ᵒ A` at a world `w` is an "end": a     --
-- family of elements of `A` at every world reachable from `w` by        --
-- spending the resource grade `ρ`, together with a naturality witness    --
-- reconciling that family with the unit-transport of `A`. This is the    --
-- exact shape of Base's Kripke exponential `_⇒ᶜ_`, but the only input    --
-- is the accessibility witness (there is no argument object), so the     --
-- bundle carries `fun` and `fun-nat` and no `fun-cong`.                  --
--                                                                    --
-- The modality is a lax graded comonad (counit `ε`, comultiplication    --
-- `δ`), packaged as an instance of                                       --
-- `DenotationalSemantics.Model.Modality.Future`. Every coherence law is  --
-- a pointwise `≈` goal; the two sides feed `A` two witnesses of the      --
-- *same* accessibility fact, reconciled by `[]-fun-irr` (proof           --
-- irrelevance of the witnesses) and, where a transport is crossed, by    --
-- `fun-nat`.                                                             --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Modality.Future (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Util.Equality

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)

open GradeSystem GS using (RGrade)
open Grade RGrade renaming (Carrier to R)
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base GS Wld

-- Composition of a graded step with a unit step (and vice versa),
-- collapsing `ρ ·ᵣ uᵣ` resp. `uᵣ ·ᵣ ρ` back to `ρ`.

⊑ρ∘ᵘ : ∀ {ρ w w' w''} → w ⊑[ ρ ] w' → w' ⊑[ u ] w'' → w ⊑[ ρ ] w''
⊑ρ∘ᵘ {ρ} q r = ⊑-mono (≃⇒≾ (·-identityʳ ρ)) (⊑-trans q r)

⊑ᵘ∘ρ : ∀ {ρ w w' w''} → w ⊑[ u ] w' → w' ⊑[ ρ ] w'' → w ⊑[ ρ ] w''
⊑ᵘ∘ρ {ρ} p q = ⊑-mono (≃⇒≾ (·-identityˡ ρ)) (⊑-trans p q)

-- The underlying Kripke family of a box: a value of `A` at every world
-- reachable from `w` by spending the resource grade `ρ`. This is exactly
-- the (naturality-free) carrier of the box bundle `[ ρ ]ᶜ` below.

[_]ᵏ : R → PSh → W → Set
[ ρ ]ᵏ A w = ∀ {w'} → w ⊑[ ρ ] w' → carrier A w'

-- The box bundle: a Kripke-necessity element of `[ ρ ] A` at `w`.

record [_]ᶜ (ρ : R) (A : PSh) (w : W) : Set where
  constructor mk[]
  field
    fun     : [ ρ ]ᵏ A w
    fun-nat : ∀ {w' w''} (q : w ⊑[ ρ ] w') (r : w' ⊑[ u ] w'')
            → _≈_ A (fun (⊑ρ∘ᵘ q r)) (transport A r (fun q))

open [_]ᶜ public

-- The value of a box bundle is independent of the accessibility
-- witness (up to `≈`), since witnesses are proof irrelevant.

[]-fun-irr : ∀ {ρ A w w'} (F : [ ρ ]ᶜ A w) (p q : w ⊑[ ρ ] w')
           → _≈_ A (fun F p) (fun F q)
[]-fun-irr {A = A} F p q with ⊑-irrelevant p q
... | refl = ≈-refl A

-- Functor

[_]ᵒ : R → PSh → PSh
[ ρ ]ᵒ A = record
  { carrier         = [ ρ ]ᶜ A
  ; _≈_             = λ {w} F G → ∀ {w'} (q : w ⊑[ ρ ] w') → _≈_ A (fun F q) (fun G q)
  ; ≈-refl          = λ q → ≈-refl A
  ; ≈-sym           = λ e q → ≈-sym A (e q)
  ; ≈-trans         = λ e e' q → ≈-trans A (e q) (e' q)
  ; transport       = λ p F → mk[]
                        (λ q → fun F (⊑ᵘ∘ρ p q))
                        (λ q r → ≈-trans A
                          ([]-fun-irr F (⊑ᵘ∘ρ p (⊑ρ∘ᵘ q r)) (⊑ρ∘ᵘ (⊑ᵘ∘ρ p q) r))
                          (fun-nat F (⊑ᵘ∘ρ p q) r))
  ; transport-cong  = λ p e q → e (⊑ᵘ∘ρ p q)
  ; transport-refl  = λ F q → []-fun-irr F (⊑ᵘ∘ρ ⊑-refl q) q
  ; transport-trans = λ p q F r → []-fun-irr F (⊑ᵘ∘ρ (⊑ᵘ-trans p q) r) (⊑ᵘ∘ρ p (⊑ᵘ∘ρ q r))
  }

[_]ᶠ : ∀ {A B} → (ρ : R) → A →ᵖ B → [ ρ ]ᵒ A →ᵖ [ ρ ]ᵒ B
[_]ᶠ {A} {B} ρ f = pmap
  (λ F → mk[]
    (λ q → app f (fun F q))
    (λ q r → ≈-trans B (app-cong f (fun-nat F q r)) (nat f r (fun F q))))
  (λ e q → app-cong f (e q))
  (λ p F q → ≈-refl B)

-- Monotonicity for gradings (contravariant: the box is ∀-shaped)

[]-≤ : ∀ {A ρ₁ ρ₂} → ρ₁ ≾ ρ₂ → [ ρ₂ ]ᵒ A →ᵖ [ ρ₁ ]ᵒ A
[]-≤ {A} p = pmap
  (λ F → mk[]
    (λ q → fun F (⊑-mono p q))
    (λ q r → ≈-trans A
      ([]-fun-irr F (⊑-mono p (⊑ρ∘ᵘ q r)) (⊑ρ∘ᵘ (⊑-mono p q) r))
      (fun-nat F (⊑-mono p q) r)))
  (λ e q → e (⊑-mono p q))
  (λ p' F q → []-fun-irr F (⊑ᵘ∘ρ p' (⊑-mono p q)) (⊑-mono p (⊑ᵘ∘ρ p' q)))

-- Counit

ε : ∀ {A} → [ u ]ᵒ A →ᵖ A
ε {A} = pmap
  (λ F → fun F ⊑-refl)
  (λ e → e ⊑-refl)
  (λ p F → ≈-trans A
    ([]-fun-irr F (⊑ᵘ∘ρ p ⊑-refl) (⊑ρ∘ᵘ ⊑-refl p))
    (fun-nat F ⊑-refl p))

-- Comultiplication (split the accessibility witness via `⊑-trans`)

δ : ∀ {A ρ₁ ρ₂} → [ ρ₁ · ρ₂ ]ᵒ A →ᵖ [ ρ₁ ]ᵒ ([ ρ₂ ]ᵒ A)
δ {A} {ρ₁} {ρ₂} = pmap
  (λ F → mk[]
    (λ p → mk[]
      (λ q → fun F (⊑-trans p q))
      (λ q r → ≈-trans A
        ([]-fun-irr F (⊑-trans p (⊑ρ∘ᵘ q r)) (⊑ρ∘ᵘ (⊑-trans p q) r))
        (fun-nat F (⊑-trans p q) r)))
    (λ p r s → []-fun-irr F (⊑-trans (⊑ρ∘ᵘ p r) s) (⊑-trans p (⊑ᵘ∘ρ r s))))
  (λ e p q → e (⊑-trans p q))
  (λ p F a s → []-fun-irr F (⊑ᵘ∘ρ p (⊑-trans a s)) (⊑-trans (⊑ᵘ∘ρ p a) s))

-- Monoidality (lax): feed the shared accessibility witness to both boxes

[]-monoidal : ∀ {A B ρ} → [ ρ ]ᵒ A ×ᵖ [ ρ ]ᵒ B →ᵖ [ ρ ]ᵒ (A ×ᵖ B)
[]-monoidal {A} {B} = pmap
  (λ FG → mk[]
    (λ q → fun (proj₁ FG) q , fun (proj₂ FG) q)
    (λ q r → fun-nat (proj₁ FG) q r , fun-nat (proj₂ FG) q r))
  (λ e q → proj₁ e q , proj₂ e q)
  (λ p FG q → ≈-refl A , ≈-refl B)


-- Unit-graded unit (inverse of `ε` at grade `u`). It transports the
-- value forward along the unit-accessibility witness — realisable for
-- every world precisely because the presheaves are unit-monotone.

ηᵘ : ∀ {A} → A →ᵖ [ u ]ᵒ A
ηᵘ {A} = pmap
  (λ x → mk[]
    (λ p → transport A p x)
    (λ q r → ≈-trans A (transport-irr {A} (⊑ρ∘ᵘ q r) (⊑ᵘ-trans q r) x) (transport-trans A q r x)))
  (λ e q → transport-cong A q e)
  (λ p x q → ≈-trans A (≈-sym A (transport-trans A p q x)) (transport-irr {A} (⊑ᵘ-trans p q) (⊑ᵘ∘ρ p q) x))

-- ηᵘ is natural

ηᵘ-nat : ∀ {A B} → (f : A →ᵖ B) → [ u ]ᶠ f ∘ᵖ ηᵘ ≈ᵖ ηᵘ ∘ᵖ f
ηᵘ-nat f x q = nat f q x

-- ηᵘ and the counit ε are mutually inverse

[]-ε∘ηᵘ≡id : ∀ {A} → ε {A} ∘ᵖ ηᵘ {A} ≈ᵖ idᵖ
[]-ε∘ηᵘ≡id {A} x = transport-refl A x

[]-ηᵘ∘ε≡id : ∀ {A} → ηᵘ {A} ∘ᵖ ε {A} ≈ᵖ idᵖ
[]-ηᵘ∘ε≡id {A} F p = ≈-trans A (≈-sym A (fun-nat F ⊑-refl p)) ([]-fun-irr F (⊑ρ∘ᵘ ⊑-refl p) p)


-- Packaging the box modality up as a `Future` instance

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future PShCat RGrade using (Future)

PShFut : Future
PShFut = record
  { [_]ᵒ        = [_]ᵒ
  ; [_]ᶠ        = [_]ᶠ
  ; []-≤        = λ {A} → []-≤ {A}
  ; ε           = ε
  ; δ           = λ {A} → δ {A}
  ; []-monoidal = []-monoidal
  ; []-idᵐ      = λ {A} {ρ} x q → ≈-refl A
  ; []-∘ᵐ       = λ {A} {B} {C} {ρ} f g x q → ≈-refl C
  ; []-congᶠ    = λ e x q → e (fun x q)
  ; []-≤-nat    = λ {A} {B} {ρ₁} {ρ₂} f p x q → ≈-refl B
  ; []-≤-refl   = λ x q → []-fun-irr x _ _
  ; []-≤-trans  = λ p q x r → []-fun-irr x _ _
  ; []-ε-nat    = λ {A} {B} f x → ≈-refl B
  ; []-δ-nat    = λ {A} {B} f x p s → ≈-refl B
  ; []-monoidal-nat = λ {A} {B} {C} {D} {ρ} f g x q → ≈-refl C , ≈-refl D
  ; []-δ-≤      = λ p q x a b → []-fun-irr x _ _
  ; []-ε∘δ≡id   = λ x s → []-fun-irr x _ _
  ; []-Dε∘δ≡id  = λ x p → []-fun-irr x _ _
  ; []-δ∘δ≡Dδ∘δ = λ x a b c → []-fun-irr x _ _
  ; ηᵘ          = ηᵘ
  ; ηᵘ-nat      = ηᵘ-nat
  ; []-ε∘ηᵘ≡id  = λ {A} → []-ε∘ηᵘ≡id {A}
  ; []-ηᵘ∘ε≡id  = λ {A} → []-ηᵘ∘ε≡id {A}
  ; []-monoidal-fstᵐ = λ {A} {B} {ρ} x q → ≈-refl A
  ; []-monoidal-sndᵐ = λ {A} {B} {ρ} x q → ≈-refl B
  ; []-monoidal-η    = λ {A} {B} {ρ} x q → ≈-refl A , ≈-refl B
  ; []-𝟙-unique      = λ {A} {ρ} f g x q → tt
  }
