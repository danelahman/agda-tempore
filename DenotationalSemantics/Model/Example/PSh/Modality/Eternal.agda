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
-- `𝟙ᵖ-eternalᵒ` (Unit), `𝟘ᵖ-eternalᵒ` (Empty), and `×ᵖ-eternalᵒ`         --
-- (products, for any two eternal objects). Together they cover exactly   --
-- the `Syntax.Types.Eternal` formers.                                    --
--                                                                    --
-- In every case `extᵉ` is taken as the adjoint mate of `necᵉ`, so        --
-- `extᵉ-mate` holds by `≈ᵖ-refl`; the trivial `necᵉ` laws are            --
-- reflexivity, and the product's reduce componentwise to the factors'.   --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Modality.Eternal (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Level using (0ℓ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)

open GradeSystem GS using (RGrade)
open Grade RGrade renaming (Carrier to R)
open World Wld

open import DenotationalSemantics.Model.Example.PSh.Base GS Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future GS Wld
  using ([_]ᵒ; mk[]; fun; []-monoidal; PShFut)
open import DenotationalSemantics.Model.Example.PSh.Modality.Past GS Wld
  using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨_⟩ᶜ; mk⟨⟩; acc; val; PShPast)
open import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction GS Wld
  using (ε⊣; PShAdj)

open import DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ)

open import DenotationalSemantics.Model.Modality.Eternal
       PShCat RGrade PShFut PShPast PShAdj
  using (Eternalᵒ)

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

Kᵖ-eternalᵒ : (S : Setoid 0ℓ 0ℓ) → Eternalᵒ (Kᵖ S)
Kᵖ-eternalᵒ S = record
  { necᵉ      = Kᵖ-nec S
  ; extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (Kᵖ-nec S {ρ})
  ; extᵉ-mate = λ {ρ} _ → reflˢ
  ; necᵉ-u    = λ _ _ → reflˢ
  ; necᵉ-≤    = λ _ _ _ → reflˢ
  ; necᵉ-δ    = λ _ _ _ → reflˢ
  ; extᵉ-μ    = λ _ → reflˢ
  }
  where open Setoid S renaming (refl to reflˢ)

-- Closure: the terminal object (Unit).

𝟙ᵖ-eternalᵒ : Eternalᵒ 𝟙ᵖ
𝟙ᵖ-eternalᵒ = record
  { necᵉ      = nec
  ; extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (nec {ρ})
  ; extᵉ-mate = λ {ρ} _ → tt
  ; necᵉ-u    = λ _ _ → tt
  ; necᵉ-≤    = λ _ _ _ → tt
  ; necᵉ-δ    = λ _ _ _ → tt
  ; extᵉ-μ    = λ _ → tt
  }
  where
    nec : ∀ {ρ} → 𝟙ᵖ →ᵖ [ ρ ]ᵒ 𝟙ᵖ
    nec = pmap (λ _ → mk[] (λ _ → tt) (λ _ _ → tt)) (λ _ _ → tt) (λ _ _ _ → tt)

-- Closure: the initial object (Empty).

𝟘ᵖ-eternalᵒ : Eternalᵒ 𝟘ᵖ
𝟘ᵖ-eternalᵒ = record
  { necᵉ      = λ {ρ} → initialᵖ {[ ρ ]ᵒ 𝟘ᵖ}
  ; extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (initialᵖ {[ ρ ]ᵒ 𝟘ᵖ})
  ; extᵉ-mate = λ {ρ} ()
  ; necᵉ-u    = λ ()
  ; necᵉ-≤    = λ _ ()
  ; necᵉ-δ    = λ ()
  ; extᵉ-μ    = λ ()
  }

-- Closure: binary products of eternal objects. `necᵉ` combines the
-- factors' necessitations through the box's lax monoidality, and every
-- law reduces componentwise to the corresponding law of a factor.

×ᵖ-eternalᵒ : ∀ {A B} → Eternalᵒ A → Eternalᵒ B → Eternalᵒ (A ×ᵖ B)
×ᵖ-eternalᵒ {A} {B} eA eB = record
  { necᵉ      = nec
  ; extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (nec {ρ})
  ; extᵉ-mate = λ {ρ} _ → ≈-refl A , ≈-refl B
  ; necᵉ-u    = λ { (a , b) q → Eternalᵒ.necᵉ-u eA a q , Eternalᵒ.necᵉ-u eB b q }
  ; necᵉ-≤    = λ { p (a , b) q → Eternalᵒ.necᵉ-≤ eA p a q , Eternalᵒ.necᵉ-≤ eB p b q }
  ; necᵉ-δ    = λ { (a , b) p q → Eternalᵒ.necᵉ-δ eA a p q , Eternalᵒ.necᵉ-δ eB b p q }
  ; extᵉ-μ    = alg
  }
  where
    nec : ∀ {ρ} → (A ×ᵖ B) →ᵖ [ ρ ]ᵒ (A ×ᵖ B)
    nec {ρ} = []-monoidal ∘ᵖ mapˣᵐ (Eternalᵒ.necᵉ eA {ρ}) (Eternalᵒ.necᵉ eB {ρ})

    -- Both sides feed the two factors' necessitations the same pair of
    -- accessibility witnesses, so the law holds componentwise, by the
    -- factors' own algebra laws applied to the projected bundles.
    -- one factor's component, bridged through that factor's `extᵉ-mate`
    -- (its `extᵉ` is an abstract field, so it is not *definitionally* the
    -- mate of its `necᵉ`)
    comp : ∀ {C} → (e : Eternalᵒ C) → ∀ {ρ₁ ρ₂ w}
         → (X : ⟨ ρ₁ ⟩ᶜ (⟨ ρ₂ ⟩ᵒ C) w)
         → _≈_ C
             (fun (app (Eternalᵒ.necᵉ e) (val (val X))) (⊑-trans (acc (val X)) (acc X)))
             (fun (app (Eternalᵒ.necᵉ e)
                    (fun (app (Eternalᵒ.necᵉ e) (val (val X))) (acc (val X))))
                  (acc X))
    comp {C} e X =
      ≈-trans C (≈-sym C (Eternalᵒ.extᵉ-mate e _))
      (≈-trans C (Eternalᵒ.extᵉ-μ e X)
      (≈-trans C (Eternalᵒ.extᵉ-mate e _)
                 (app-cong (Eternalᵒ.necᵉ e) (Eternalᵒ.extᵉ-mate e _) (acc X))))

    alg : ∀ {ρ₁ ρ₂ w} → (E : ⟨ ρ₁ ⟩ᶜ (⟨ ρ₂ ⟩ᵒ (A ×ᵖ B)) w)
        → _≈_ (A ×ᵖ B)
            (fun (app nec (val (val E))) (⊑-trans (acc (val E)) (acc E)))
            (fun (app nec
                   ( fun (app (Eternalᵒ.necᵉ eA) (proj₁ (val (val E)))) (acc (val E))
                   , fun (app (Eternalᵒ.necᵉ eB) (proj₂ (val (val E)))) (acc (val E)) ))
                 (acc E))
    alg E =
        comp eA (mk⟨⟩ (acc E) (mk⟨⟩ (acc (val E)) (proj₁ (val (val E)))))
      , comp eB (mk⟨⟩ (acc E) (mk⟨⟩ (acc (val E)) (proj₂ (val (val E)))))
