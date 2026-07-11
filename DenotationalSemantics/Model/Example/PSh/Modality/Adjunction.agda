------------------------------------------------------------------------
-- The graded adjunction `⟨ ρ ⟩ ⊣ [ ρ ]` on setoid-valued presheaves,   --
-- between the context modality (Kripke possibility) and the box        --
-- modality (Kripke necessity) at a common resource grade `ρ`.          --
--                                                                    --
-- The unit `η⊣ : A →ᵖ [ ρ ] ⟨ ρ ⟩ A` names the past world of the       --
-- possibility bundle by the *present* world, transported forward only  --
-- when the box is later opened; the counit `ε⊣ : ⟨ ρ ⟩ [ ρ ] A →ᵖ A`   --
-- opens a boxed value reached through a lock along the very witness     --
-- that reached it. Both triangle identities and both grade-relaxation   --
-- laws hold on the nose (`≈-refl`); the only genuine coend reasoning is --
-- in the congruences of `η⊣` (a single generating step) and `ε⊣`        --
-- (folding the coend chain through the box's `fun-nat`).                --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Modality.Adjunction (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Data.Product using (_,_)

open import Relation.Binary.Construct.Closure.Equivalence using (return)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star) renaming (ε to εˢ; _◅_ to _◅ˢ_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)

open import Util.Equality

open GradeSystem GS using (RGrade)
open Grade RGrade renaming (Carrier to R)
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base GS Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future GS Wld hiding (⊑ρ∘ᵘ)
open import DenotationalSemantics.Model.Example.PSh.Modality.Past GS Wld

-- STRUCTURE

-- Unit: transpose a value under a lock into a boxed possibility.

η⊣ : ∀ {A ρ} → A →ᵖ [ ρ ]ᵒ (⟨ ρ ⟩ᵒ A)
η⊣ {A} {ρ} = pmap
  (λ x → mk[] (λ p → mk⟨⟩ p x) (λ q r → ≈-refl (⟨ ρ ⟩ᵒ A)))
  (λ {w} {x} {y} e p → return (⊑-refl , ≈-trans A (transport-refl A x) e))
  (λ t x p → ≈-sym (⟨ ρ ⟩ᵒ A) (return (t , ≈-refl A)))

-- Counit: open a boxed value reached through a lock.

ε⊣-app : ∀ {A ρ w} → ⟨ ρ ⟩ᶜ ([ ρ ]ᵒ A) w → carrier A w
ε⊣-app E = fun (val E) (acc E)

-- A single generating step of the coend, resolved through the box's
-- proof-irrelevance and naturality (`fun-nat` is used via the transport
-- reduction inside `c`).

ε⊣-step : ∀ {A ρ w} (E E' : ⟨ ρ ⟩ᶜ ([ ρ ]ᵒ A) w)
        → _◅_ {ρ} {[ ρ ]ᵒ A} {w} E E' → _≈_ A (ε⊣-app E) (ε⊣-app E')
ε⊣-step {A} E E' (s , c) =
  ≈-trans A ([]-fun-irr {A = A} (val E) (acc E) (⊑ᵘ∘ρ s (acc E'))) (c (acc E'))

-- Folding the equivalence closure with the concrete motive
-- `ε⊣-app E ≈ ε⊣-app E'`, avoiding higher-order motive inference. The
-- endpoints of each generating step must be named, since the coend
-- relation mentions them only through projections.

ε⊣-cong : ∀ {A ρ w} {E E' : ⟨ ρ ⟩ᶜ ([ ρ ]ᵒ A) w}
        → _≈_ (⟨ ρ ⟩ᵒ ([ ρ ]ᵒ A)) E E' → _≈_ A (ε⊣-app E) (ε⊣-app E')
ε⊣-cong {A} εˢ = ≈-refl A
ε⊣-cong {A} {E = E} (_◅ˢ_ {j = mid} (fwd r) rest) =
  ≈-trans A (ε⊣-step E mid r) (ε⊣-cong rest)
ε⊣-cong {A} {E = E} (_◅ˢ_ {j = mid} (bwd r) rest) =
  ≈-trans A (≈-sym A (ε⊣-step mid E r)) (ε⊣-cong rest)

ε⊣ : ∀ {A ρ} → ⟨ ρ ⟩ᵒ ([ ρ ]ᵒ A) →ᵖ A
ε⊣ {A} = pmap ε⊣-app ε⊣-cong (λ t E → fun-nat (val E) (acc E) t)

-- PROPERTIES

-- unit and counit are natural

η⊣-nat : ∀ {A B ρ} → (f : A →ᵖ B)
       → [ ρ ]ᶠ (⟨ ρ ⟩ᶠ f) ∘ᵖ η⊣ ≈ᵖ η⊣ ∘ᵖ f
η⊣-nat {B = B} {ρ} f x p = ≈-refl (⟨ ρ ⟩ᵒ B)

ε⊣-nat : ∀ {A B ρ} → (f : A →ᵖ B)
       → f ∘ᵖ ε⊣ ≈ᵖ ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ ([ ρ ]ᶠ f)
ε⊣-nat {B = B} f E = ≈-refl B

-- unit and counit are compatible with the grading

η⊣-≤ : ∀ {A ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
     → []-≤ p ∘ᵖ η⊣ {A} {ρ₂} ≈ᵖ [ ρ₁ ]ᶠ (⟨⟩-≤ p) ∘ᵖ η⊣ {A} {ρ₁}
η⊣-≤ {A} {ρ₂ = ρ₂} p x q = ≈-refl (⟨ ρ₂ ⟩ᵒ A)

ε⊣-≤ : ∀ {A ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
     → ε⊣ {A} {ρ₂} ∘ᵖ ⟨⟩-≤ p ≈ᵖ ε⊣ {A} {ρ₁} ∘ᵖ ⟨ ρ₁ ⟩ᶠ ([]-≤ p)
ε⊣-≤ {A} p E = ≈-refl A

-- triangle identities

triangleˡ : ∀ {A ρ} → ε⊣ {⟨ ρ ⟩ᵒ A} {ρ} ∘ᵖ ⟨ ρ ⟩ᶠ (η⊣ {A} {ρ}) ≈ᵖ idᵖ
triangleˡ {A} {ρ} E = ≈-refl (⟨ ρ ⟩ᵒ A)

triangleʳ : ∀ {A ρ} → [ ρ ]ᶠ (ε⊣ {A} {ρ}) ∘ᵖ η⊣ {[ ρ ]ᵒ A} {ρ} ≈ᵖ idᵖ
triangleʳ {A} F p = ≈-refl A


-- Packaging the adjunction up as an `Adjunction` instance

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Adjunction PShCat RGrade PShFut PShPast using (Adjunction)

PShAdj : Adjunction
PShAdj = record
  { η⊣        = η⊣
  ; ε⊣        = λ {A} → ε⊣ {A}
  ; η⊣-nat    = η⊣-nat
  ; ε⊣-nat    = ε⊣-nat
  ; η⊣-≤      = η⊣-≤
  ; ε⊣-≤      = ε⊣-≤
  ; triangleˡ = λ {A} → triangleˡ {A}
  ; triangleʳ = λ {A} → triangleʳ {A}
  }
