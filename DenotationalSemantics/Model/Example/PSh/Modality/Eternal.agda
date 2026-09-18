------------------------------------------------------------------------
-- Eternal objects in the concrete presheaf model: constant presheaves. --
--                                                                    --
-- `Kᵖ S` is the presheaf constantly equal to the setoid `S` at every   --
-- world, with identity transport. Being world-independent, its value    --
-- can be necessitated into, and extracted from, the box / context        --
-- modality at any grade, so `Kᵖ S` carries an `Eternalᵒ` structure       --
-- (`Kᵖ-eternalᵒ`). This is what interprets the eternal *base* types.     --
--                                                                    --
-- The eternal *type formers* are handled by the closure lemmas:          --
-- `𝟙ᵖ-eternalᵒ` (Unit), `𝔹ᵖ-eternalᵒ` (Bool), `𝟘ᵖ-eternalᵒ` (Empty), and --
-- `×ᵖ-eternalᵒ` (products, for any two eternal objects). Together they   --
-- cover exactly the `Syntax.Types.Eternal` formers.                      --
--                                                                    --
-- For the constant presheaves the `⟨ ⊤ ⟩`-algebra `α` is the mate         --
-- `ε⊣ ∘ᵖ ⟨ ⊤ ⟩ᶠ nec` of a necessitation `nec`, and its two laws hold by   --
-- reflexivity; products reuse the generic closure `×ᵐ-eternalᵒ`.          --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Modality.Eternal (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Level using (0ℓ)
open import Data.Bool using (Bool)
open import Data.Unit using (tt)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (setoid)

open GradeSystem GS using (RGrade)
open Grade RGrade renaming (Carrier to R)
open World Wld

open import DenotationalSemantics.Model.Example.PSh.Base GS Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future GS Wld
  using ([_]ᵒ; mk[]; PShFut)
open import DenotationalSemantics.Model.Example.PSh.Modality.Past GS Wld
  using (⟨_⟩ᵒ; ⟨_⟩ᶠ; PShPast)
open import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction GS Wld
  using (ε⊣; PShAdj)

open import DenotationalSemantics.Model.Category
open Category PShCat using (fstᵐ; sndᵐ; ⟨_,_⟩ᵐ; _∘ᵐ_; _≈ᵐ_)

open import DenotationalSemantics.Model.Modality.Past PShCat RGrade using (Past)

open import DenotationalSemantics.Model.Modality.Eternal
       PShCat RGrade PShFut PShPast PShAdj
  using (Eternalᵒ; ×ᵐ-eternalᵒ; ×ᵐ-eternalᵒ-extᵉ)

-- The constant presheaf on a setoid: the same value at every world,
-- transported by the identity.

Kᵖ : Setoid 0ℓ 0ℓ → PSh
Kᵖ S = record
  { carrier         = λ _ → ∣S∣
  ; _≈_             = _≈ˢ_
  ; ≈-refl          = reflˢ
  ; ≈-sym           = symˢ
  ; ≈-trans         = transˢ
  ; transport       = λ _ x → x
  ; transport-cong  = λ _ e → e
  ; transport-refl  = λ _ → reflˢ
  ; transport-trans = λ _ _ _ → reflˢ
  }
  where open Setoid S renaming (Carrier to ∣S∣; _≈_ to _≈ˢ_; refl to reflˢ; sym to symˢ; trans to transˢ)

-- Necessitation of a constant value at an arbitrary grade: the box's
-- Kripke family is the value itself at every reachable world.

Kᵖ-nec : (S : Setoid 0ℓ 0ℓ) → ∀ {ρ} → Kᵖ S →ᵖ [ ρ ]ᵒ (Kᵖ S)
Kᵖ-nec S = pmap
  (λ x → mk[] (λ _ → x) (λ _ _ → reflˢ))
  (λ e _ → e)
  (λ _ _ _ → reflˢ)
  where open Setoid S renaming (refl to reflˢ)

-- A global element of a constant presheaf: the chosen carrier value at
-- every world.

Kᵖ-const : (S : Setoid 0ℓ 0ℓ) → Setoid.Carrier S → 𝟙ᵖ →ᵖ Kᵖ S
Kᵖ-const S c = pmap (λ _ → c) (λ _ → reflˢ) (λ _ _ → reflˢ)
  where open Setoid S renaming (refl to reflˢ)

Kᵖ-eternalᵒ : (S : Setoid 0ℓ 0ℓ) → Eternalᵒ (Kᵖ S)
Kᵖ-eternalᵒ S = record
  { α       = ε⊣ ∘ᵖ ⟨ ⊤ ⟩ᶠ (Kᵖ-nec S {⊤})
  ; α-unit  = λ _ → reflˢ
  ; α-assoc = λ _ → reflˢ
  }
  where open Setoid S renaming (refl to reflˢ)

-- Closure: the terminal object (Unit).

𝟙ᵖ-eternalᵒ : Eternalᵒ 𝟙ᵖ
𝟙ᵖ-eternalᵒ = record
  { α       = ε⊣ ∘ᵖ ⟨ ⊤ ⟩ᶠ nec
  ; α-unit  = λ _ → tt
  ; α-assoc = λ _ → tt
  }
  where
    nec : ∀ {ρ} → 𝟙ᵖ →ᵖ [ ρ ]ᵒ 𝟙ᵖ
    nec = pmap (λ _ → mk[] (λ _ → tt) (λ _ _ → tt)) (λ _ _ → tt) (λ _ _ _ → tt)

-- Closure: the initial object (Empty).

𝟘ᵖ-eternalᵒ : Eternalᵒ 𝟘ᵖ
𝟘ᵖ-eternalᵒ = record
  { α       = ε⊣ ∘ᵖ ⟨ ⊤ ⟩ᶠ (initialᵖ {[ ⊤ ]ᵒ 𝟘ᵖ})
  ; α-unit  = λ ()
  ; α-assoc = λ ()
  }

-- Closure: the boolean object. `𝔹ᵖ` *is* the constant presheaf on the
-- booleans, so its eternal structure is `Kᵖ-eternalᵒ` at that setoid.

𝔹ᵖ-eternalᵒ : Eternalᵒ 𝔹ᵖ
𝔹ᵖ-eternalᵒ = Kᵖ-eternalᵒ (setoid Bool)

-- Closure: binary products of eternal objects. Algebras are closed under the
-- category's products, so this is the generic construction.

×ᵖ-eternalᵒ : ∀ {A B} → Eternalᵒ A → Eternalᵒ B → Eternalᵒ (A ×ᵖ B)
×ᵖ-eternalᵒ = ×ᵐ-eternalᵒ

-- The product's eternal extraction acts componentwise (the closure is
-- compatible with the projections).

×ᵖ-eternalᵒ-extᵉ : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ}
                 → Eternalᵒ.extᵉ (×ᵖ-eternalᵒ eA eB) {ρ}
                 ≈ᵐ ⟨ Eternalᵒ.extᵉ eA ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ , Eternalᵒ.extᵉ eB ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ
×ᵖ-eternalᵒ-extᵉ = ×ᵐ-eternalᵒ-extᵉ
