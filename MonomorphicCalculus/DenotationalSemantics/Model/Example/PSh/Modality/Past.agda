------------------------------------------------------------------------
-- The context modality `⟨ ρ ⟩ A` on setoid-valued presheaves, with the --
-- *Kripke possibility* semantics over the graded accessibility relation --
-- on worlds. An element of `⟨ ρ ⟩ A` at a world `w` is a bundle          --
--                                                                    --
--   mk⟨⟩ (acc : wᵖ ⊑[ ρ ] w) (val : carrier A wᵖ)                       --
--                                                                    --
-- i.e. a *past* world `wᵖ`, reachable to `w` by spending the resource     --
-- grade `ρ`, together with a value of `A` at that past world.             --
--                                                                    --
-- As the base presheaves are unit-monotone, this Σ-bundle is quotiented  --
-- into the *coend* `∫^{wᵖ} (wᵖ ⊑[ ρ ] w) ×                               --
-- carrier A wᵖ`. Concretely the per-world equivalence `_≈_` is the        --
-- equivalence closure of the generating relation `_◅_`: a bundle may be   --
-- pushed forward along a unit-accessibility step `wᵖ ⊑[ u ] wᵖ'`,        --
-- transporting its value along and readjusting the witness (the witness   --
-- readjustment is free, by `⊑-irrelevant`). Taking the closure of this   --
-- one-step relation is exactly what makes the adjunction unit `η⊣`        --
-- natural in the worlds: `η⊣` names the past world by the *present* one,  --
-- and moving the present world forward is a generating step.              --
--                                                                    --
-- The modality is a lax graded monad (unit `η`, multiplication `μ` with   --
-- reversed grade order), packaged as an instance of                       --
-- `MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past`.        --
-- Because transport of a                                                  --
-- bundle only readjusts the witness, keeping the past world and value     --
-- fixed, almost every coherence law is either definitional (`≈-refl`) or  --
-- a single generating step for witness-irrelevance (`≈-mk-irr`). The one  --
-- exception is the congruence of `μ`, which folds a value-level chain     --
-- through the fixed-outer-witness map `postμ`.                            --
------------------------------------------------------------------------

open import Grades.Base
open import MonomorphicCalculus.DenotationalSemantics.Model.World

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Data.Product

open import Relation.Binary.Core using (_=[_]⇒_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Construct.Closure.Equivalence
  using (EqClosure; return; gmap; gfold)
  renaming (reflexive to eq-refl; symmetric to eq-sym; transitive to eq-trans;
            isEquivalence to eq-isEquivalence)

open import Util.Equality

open GradeSystem GS using (RGrade)
open Grade RGrade renaming (Carrier to R)
open World Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base GS Wld

-- two-sided monotonicity of `·` derived from the one-sided ones

·-mono-≾ : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≾ ρ₁' → ρ₂ ≾ ρ₂' → ρ₁ · ρ₂ ≾ ρ₁' · ρ₂'
·-mono-≾ p q = ≾-trans (·-monoˡ-≾ p) (·-monoʳ-≾ q)

-- Composition of a graded step with a unit step, collapsing `ρ ·ᵣ uᵣ`
-- back to `ρ`.

⊑ρ∘ᵘ : ∀ {ρ w w' w''} → w ⊑[ ρ ] w' → w' ⊑[ u ] w'' → w ⊑[ ρ ] w''
⊑ρ∘ᵘ {ρ} q r = ⊑-mono (≃⇒≾ (·-identityʳ ρ)) (⊑-trans q r)

-- The possibility bundle: a Kripke-possibility element of `⟨ ρ ⟩ A` at `w`.

record ⟨_⟩ᶜ (ρ : R) (A : PSh) (w : W) : Set where
  constructor mk⟨⟩
  field
    {wᵖ} : W
    acc  : wᵖ ⊑[ ρ ] w
    val  : carrier A wᵖ

open ⟨_⟩ᶜ public

-- The coend generating relation: push the past world forward along a
-- unit step, transporting the value. The witnesses `acc` play no role
-- (they are proof irrelevant), so the relation records only the unit
-- step between past worlds and the value equation it induces.

_◅_ : ∀ {ρ A w} → ⟨ ρ ⟩ᶜ A w → ⟨ ρ ⟩ᶜ A w → Set
_◅_ {A = A} e e' = Σ[ s ∈ wᵖ e ⊑[ u ] wᵖ e' ] _≈_ A (transport A s (val e)) (val e')

-- Functor

⟨_⟩ᵒ : R → PSh → PSh
⟨ ρ ⟩ᵒ A = record
  { carrier         = ⟨ ρ ⟩ᶜ A
  ; _≈_             = λ {w} → EqClosure (_◅_ {ρ} {A} {w})
  ; ≈-refl          = λ {w} {x} → eq-refl (_◅_ {ρ} {A} {w}) {x}
  ; ≈-sym           = λ {w} {x} {y} → eq-sym (_◅_ {ρ} {A} {w}) {x} {y}
  ; ≈-trans         = λ {w} {x} {y} {z} → eq-trans (_◅_ {ρ} {A} {w}) {x} {y} {z}
  ; transport       = λ t e → mk⟨⟩ (⊑ρ∘ᵘ (acc e) t) (val e)
  ; transport-cong  = λ t e → gmap (λ z → mk⟨⟩ (⊑ρ∘ᵘ (acc z) t) (val z)) (λ st → st) e
  ; transport-refl  = λ e → return (⊑-refl , transport-refl A (val e))
  ; transport-trans = λ p q e → return (⊑-refl , transport-refl A (val e))
  }

-- Two bundles with the same past world and value are `≈`-equal
-- irrespective of their accessibility witnesses.

≈-mk-irr : ∀ {ρ A w v} (p q : v ⊑[ ρ ] w) (x : carrier A v)
         → _≈_ (⟨ ρ ⟩ᵒ A) (mk⟨⟩ p x) (mk⟨⟩ q x)
≈-mk-irr {A = A} p q x = return (⊑-refl , transport-refl A x)

⟨_⟩ᶠ : ∀ {A B} → (ρ : R) → A →ᵖ B → ⟨ ρ ⟩ᵒ A →ᵖ ⟨ ρ ⟩ᵒ B
⟨_⟩ᶠ {A} {B} ρ f = pmap
  (λ e → mk⟨⟩ (acc e) (app f (val e)))
  (gmap (λ e → mk⟨⟩ (acc e) (app f (val e)))
        (λ {a} → λ { (s , eq) → s , ≈-trans B (≈-sym B (nat f s (val a))) (app-cong f eq) }))
  (λ t e → ≈-refl (⟨ ρ ⟩ᵒ B))

-- Monotonicity for gradings (covariant: the context modality is Σ-shaped)

⟨⟩-≤ : ∀ {A ρ₁ ρ₂} → ρ₁ ≾ ρ₂ → ⟨ ρ₁ ⟩ᵒ A →ᵖ ⟨ ρ₂ ⟩ᵒ A
⟨⟩-≤ {A} l = pmap
  (λ e → mk⟨⟩ (⊑-mono l (acc e)) (val e))
  (gmap (λ e → mk⟨⟩ (⊑-mono l (acc e)) (val e)) (λ st → st))
  (λ t e → ≈-mk-irr _ _ (val e))

-- Unit

η : ∀ {A} → A →ᵖ ⟨ u ⟩ᵒ A
η {A} = pmap
  (λ x → mk⟨⟩ ⊑-refl x)
  (λ {w} {x} {y} e → return (⊑-refl , ≈-trans A (transport-refl A x) e))
  (λ {w} {w'} t x → eq-sym (_◅_ {u} {A} {w'}) (return (t , ≈-refl A)))

-- Multiplication (note the reversed grade order)

μ-app : ∀ {A ρ₁ ρ₂ w} → ⟨ ρ₁ ⟩ᶜ (⟨ ρ₂ ⟩ᵒ A) w → ⟨ ρ₂ · ρ₁ ⟩ᶜ A w
μ-app e = mk⟨⟩ (⊑-trans (acc (val e)) (acc e)) (val (val e))

-- `μ` with a fixed outer witness, used to fold `μ`'s congruence chain

postμ : ∀ {A ρ₁ ρ₂ v w} → v ⊑[ ρ₁ ] w → ⟨ ρ₂ ⟩ᶜ A v → ⟨ ρ₂ · ρ₁ ⟩ᶜ A w
postμ q X = mk⟨⟩ (⊑-trans (acc X) q) (val X)

postμ-cong : ∀ {A ρ₁ ρ₂ v w} (q : v ⊑[ ρ₁ ] w) {X Y : ⟨ ρ₂ ⟩ᶜ A v}
           → _≈_ (⟨ ρ₂ ⟩ᵒ A) X Y → _≈_ (⟨ ρ₂ · ρ₁ ⟩ᵒ A) (postμ q X) (postμ q Y)
postμ-cong q = gmap (postμ q) (λ st → st)

μ-cong : ∀ {A ρ₁ ρ₂ w} {E E' : ⟨ ρ₁ ⟩ᶜ (⟨ ρ₂ ⟩ᵒ A) w}
       → _≈_ (⟨ ρ₁ ⟩ᵒ (⟨ ρ₂ ⟩ᵒ A)) E E'
       → _≈_ (⟨ ρ₂ · ρ₁ ⟩ᵒ A) (μ-app E) (μ-app E')
μ-cong {A} {ρ₁} {ρ₂} {w} = gfold (eq-isEquivalence (_◅_ {ρ₂ · ρ₁} {A} {w})) μ-app step
  where
    step : _◅_ {ρ₁} {⟨ ρ₂ ⟩ᵒ A} {w} =[ μ-app ]⇒ _≈_ (⟨ ρ₂ · ρ₁ ⟩ᵒ A)
    step {E} {E'} (s , c) = ≈-trans (⟨ ρ₂ · ρ₁ ⟩ᵒ A)
      (≈-mk-irr (⊑-trans (acc (val E)) (acc E))
                (⊑-trans (⊑ρ∘ᵘ (acc (val E)) s) (acc E'))
                (val (val E)))
      (postμ-cong (acc E') c)

μ : ∀ {A ρ₁ ρ₂} → ⟨ ρ₁ ⟩ᵒ (⟨ ρ₂ ⟩ᵒ A) →ᵖ ⟨ ρ₂ · ρ₁ ⟩ᵒ A
μ = pmap μ-app μ-cong (λ t e → ≈-mk-irr _ _ (val (val e)))

-- Unit-graded counit (inverse of `η` at grade `u`). It transports the
-- value forward along the unit-accessibility witness — realisable for
-- every world precisely because the presheaves are unit-monotone. Its
-- congruence folds the coend chain, transporting each generating step
-- along the accessibility witness of the target bundle.

A-isEquiv : ∀ {A : PSh} {w} → IsEquivalence (_≈_ A {w})
A-isEquiv {A} = record { refl = ≈-refl A ; sym = ≈-sym A ; trans = ≈-trans A }

εᵘ-app : ∀ {A w} → ⟨ u ⟩ᶜ A w → carrier A w
εᵘ-app {A} e = transport A (acc e) (val e)

εᵘ-cong : ∀ {A w} {E E' : ⟨ u ⟩ᶜ A w}
        → _≈_ (⟨ u ⟩ᵒ A) E E' → _≈_ A (εᵘ-app E) (εᵘ-app E')
εᵘ-cong {A} {w} = gfold (A-isEquiv {A} {w}) εᵘ-app step
  where
    step : _◅_ {u} {A} {w} =[ εᵘ-app ]⇒ _≈_ A
    step {E} {E'} (s , eq) = ≈-trans A
      (transport-irr {A} (acc E) (⊑ᵘ-trans s (acc E')) (val E))
      (≈-trans A (transport-trans A s (acc E') (val E))
                 (transport-cong A (acc E') eq))

εᵘ : ∀ {A} → ⟨ u ⟩ᵒ A →ᵖ A
εᵘ {A} = pmap
  εᵘ-app
  εᵘ-cong
  (λ t e → ≈-trans A (transport-irr {A} (⊑ρ∘ᵘ (acc e) t) (⊑ᵘ-trans (acc e) t) (val e))
                     (transport-trans A (acc e) t (val e)))


-- ⟨_⟩ is functorial

⟨⟩-idᵖ : ∀ {A ρ} → ⟨ ρ ⟩ᶠ (idᵖ {A}) ≈ᵖ idᵖ
⟨⟩-idᵖ {A} {ρ} e = ≈-refl (⟨ ρ ⟩ᵒ A)

⟨⟩-∘ᵖ : ∀ {A B C ρ} → (g : B →ᵖ C) → (f : A →ᵖ B)
      → ⟨ ρ ⟩ᶠ (g ∘ᵖ f) ≈ᵖ ⟨ ρ ⟩ᶠ g ∘ᵖ ⟨ ρ ⟩ᶠ f
⟨⟩-∘ᵖ {C = C} {ρ} g f e = ≈-refl (⟨ ρ ⟩ᵒ C)

-- ⟨_⟩ᶠ is a congruence

⟨⟩-congᶠ : ∀ {A B ρ} {f g : A →ᵖ B} → f ≈ᵖ g → ⟨ ρ ⟩ᶠ f ≈ᵖ ⟨ ρ ⟩ᶠ g
⟨⟩-congᶠ {B = B} {ρ} {f} e x =
  return (⊑-refl , ≈-trans B (transport-refl B (app f (val x))) (e (val x)))

-- ⟨⟩-≤ is natural

⟨⟩-≤-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵖ B) → (l : ρ₁ ≾ ρ₂)
         → ⟨ ρ₂ ⟩ᶠ f ∘ᵖ ⟨⟩-≤ l ≈ᵖ ⟨⟩-≤ l ∘ᵖ ⟨ ρ₁ ⟩ᶠ f
⟨⟩-≤-nat {B = B} {ρ₂ = ρ₂} f l e = ≈-refl (⟨ ρ₂ ⟩ᵒ B)

-- ⟨_⟩ is functorial in the gradings

⟨⟩-≤-refl : ∀ {A ρ} → ⟨⟩-≤ {A} (≾-refl {ρ}) ≈ᵖ idᵖ
⟨⟩-≤-refl {A} e = ≈-mk-irr _ _ (val e)

⟨⟩-≤-trans : ∀ {A ρ ρ' ρ''} → (p : ρ ≾ ρ') → (q : ρ' ≾ ρ'')
           → ⟨⟩-≤ {A} q ∘ᵖ ⟨⟩-≤ {A} p ≈ᵖ ⟨⟩-≤ (≾-trans p q)
⟨⟩-≤-trans p q e = ≈-mk-irr _ _ (val e)

-- η is natural

⟨⟩-η-nat : ∀ {A B} → (f : A →ᵖ B) → ⟨ u ⟩ᶠ f ∘ᵖ η ≈ᵖ η ∘ᵖ f
⟨⟩-η-nat {B = B} f x = ≈-refl (⟨ u ⟩ᵒ B)

-- μ is natural

⟨⟩-μ-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵖ B)
         → ⟨ ρ₂ · ρ₁ ⟩ᶠ f ∘ᵖ μ ≈ᵖ μ ∘ᵖ ⟨ ρ₁ ⟩ᶠ (⟨ ρ₂ ⟩ᶠ f)
⟨⟩-μ-nat {B = B} {ρ₁} {ρ₂} f e = ≈-refl (⟨ ρ₂ · ρ₁ ⟩ᵒ B)

-- μ is compatible with the gradings

⟨⟩-μ-≤ : ∀ {A ρ₁ ρ₂ ρ₁' ρ₂'} → (p : ρ₁ ≾ ρ₁') → (q : ρ₂ ≾ ρ₂')
       → ⟨⟩-≤ {A} (·-mono-≾ q p) ∘ᵖ μ {A} {ρ₁} {ρ₂}
       ≈ᵖ μ {A} {ρ₁'} {ρ₂'} ∘ᵖ ⟨ ρ₁' ⟩ᶠ (⟨⟩-≤ q) ∘ᵖ ⟨⟩-≤ p
⟨⟩-μ-≤ {A} p q e = ≈-mk-irr _ _ (val (val e))

-- Graded monad laws

⟨⟩-μ∘η≡id : ∀ {A ρ}
          → μ {A} {u} {ρ} ∘ᵖ η
          ≈ᵖ ⟨⟩-≤ (≃⇒≿ (·-identityʳ ρ))
⟨⟩-μ∘η≡id {A} x = ≈-mk-irr _ _ (val x)

⟨⟩-μ∘Tη≡id : ∀ {A ρ}
           → μ {A} {ρ} {u} ∘ᵖ ⟨ ρ ⟩ᶠ η
           ≈ᵖ ⟨⟩-≤ (≃⇒≿ (·-identityˡ ρ))
⟨⟩-μ∘Tη≡id {A} e = ≈-mk-irr _ _ (val e)

⟨⟩-μ∘μ≡μ∘Tμ : ∀ {A ρ₁ ρ₂ ρ₃}
            → μ {A} {ρ₂ · ρ₁} {ρ₃} ∘ᵖ μ {⟨ ρ₃ ⟩ᵒ A} {ρ₁} {ρ₂}
            ≈ᵖ    ⟨⟩-≤ (≃⇒≾ (·-assoc ρ₃ ρ₂ ρ₁))
              ∘ᵖ μ {A} {ρ₁} {ρ₃ · ρ₂} ∘ᵖ ⟨ ρ₁ ⟩ᶠ (μ {A} {ρ₂} {ρ₃})
⟨⟩-μ∘μ≡μ∘Tμ {A} e = ≈-mk-irr _ _ (val (val (val e)))

-- εᵘ is natural

εᵘ-nat : ∀ {A B} → (f : A →ᵖ B) → f ∘ᵖ εᵘ ≈ᵖ εᵘ ∘ᵖ ⟨ u ⟩ᶠ f
εᵘ-nat f e = nat f (acc e) (val e)

-- εᵘ and the unit η are mutually inverse

⟨⟩-εᵘ∘η≡id : ∀ {A} → εᵘ {A} ∘ᵖ η ≈ᵖ idᵖ
⟨⟩-εᵘ∘η≡id {A} x = transport-refl A x

⟨⟩-η∘εᵘ≡id : ∀ {A} → η {A} ∘ᵖ εᵘ ≈ᵖ idᵖ
⟨⟩-η∘εᵘ≡id {A} {w} E = eq-sym (_◅_ {u} {A} {w}) (return (acc E , ≈-refl A))


-- Packaging the context modality up as a `Past` instance

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past PShCat RGrade using (Past)

PShPast : Past
PShPast = record
  { ⟨_⟩ᵒ        = ⟨_⟩ᵒ
  ; ⟨_⟩ᶠ        = ⟨_⟩ᶠ
  ; ⟨⟩-≤        = λ {A} → ⟨⟩-≤ {A}
  ; η           = η
  ; μ           = λ {A} → μ {A}
  ; ⟨⟩-idᵐ      = λ {A} → ⟨⟩-idᵖ {A}
  ; ⟨⟩-∘ᵐ       = ⟨⟩-∘ᵖ
  ; ⟨⟩-congᶠ    = λ {A} {B} {ρ} {f} {g} → ⟨⟩-congᶠ {A} {B} {ρ} {f} {g}
  ; ⟨⟩-≤-nat    = ⟨⟩-≤-nat
  ; ⟨⟩-≤-refl   = λ {A} → ⟨⟩-≤-refl {A}
  ; ⟨⟩-≤-trans  = λ {A} p q → ⟨⟩-≤-trans {A} p q
  ; ⟨⟩-η-nat    = ⟨⟩-η-nat
  ; ⟨⟩-μ-nat    = ⟨⟩-μ-nat
  ; ⟨⟩-μ-≤      = λ {A} p q → ⟨⟩-μ-≤ {A} p q
  ; ⟨⟩-μ∘η≡id   = λ {A} → ⟨⟩-μ∘η≡id {A}
  ; ⟨⟩-μ∘Tη≡id  = λ {A} → ⟨⟩-μ∘Tη≡id {A}
  ; ⟨⟩-μ∘μ≡μ∘Tμ = λ {A} → ⟨⟩-μ∘μ≡μ∘Tμ {A}
  ; εᵘ          = εᵘ
  ; εᵘ-nat      = εᵘ-nat
  ; ⟨⟩-εᵘ∘η≡id  = λ {A} → ⟨⟩-εᵘ∘η≡id {A}
  ; ⟨⟩-η∘εᵘ≡id  = λ {A} → ⟨⟩-η∘εᵘ≡id {A}
  }
