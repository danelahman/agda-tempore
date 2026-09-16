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
-- In every case `extᵉ` is the mate `ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ nec` of a necessitation --
-- `nec`; the algebra laws are reflexivity for the constant presheaves    --
-- and reduce componentwise to the factors' for products.                 --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Modality.Eternal (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Level using (0ℓ)
open import Data.Bool using (Bool)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (setoid)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure; return; gmap)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅◅_)

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
open Category PShCat using (mapˣᵐ; fstᵐ; sndᵐ; ⟨_,_⟩ᵐ; _∘ᵐ_; idᵐ; _≈ᵐ_;
  ⟨⟩ᵐ-fstᵐ; ⟨⟩ᵐ-sndᵐ; ⟨⟩ᵐ-unique; ⟨_,_⟩ᵐ-cong; ⟨⟩ᵐ-∘; mapˣᵐ-∘; mapˣᵐ-cong; mapˣᵐ-idᵐ;
  ×ᵐ-assoc; ×ᵐ-assoc⁻¹; ×ᵐ-assoc-iso; ×ᵐ-assoc⁻¹-iso;
  ∘ᵐ-assoc; ∘ᵐ-congˡ; ∘ᵐ-congʳ; ∘ᵐ-identityˡ; ∘ᵐ-identityʳ;
  ≈ᵐ-refl; ≈ᵐ-sym; ≈ᵐ-trans)

open import DenotationalSemantics.Model.Modality.Past PShCat RGrade using (Past)
open Past PShPast using (⟨⟩-∘ᵐ; ⟨⟩-idᵐ; ⟨⟩-congᶠ)

open import DenotationalSemantics.Model.Modality.Eternal
       PShCat RGrade PShFut PShPast PShAdj
  using (Eternalᵒ; module ×-strength)

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
  { extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (Kᵖ-nec S {ρ})
  ; extᵉ-≤    = λ _ _ → reflˢ
  ; extᵉ-u    = λ _ → reflˢ
  ; extᵉ-μ    = λ _ → reflˢ
  ; strᵉ      = λ {ρ} {X} → pmap
                  (λ {w} → λ { (e , a) → mk⟨⟩ (acc e) (val e , a) })
                  (λ {w} {(e , a)} {(e' , a')} → λ { (chainX , a≈a') →
                       gmap (λ z → mk⟨⟩ (acc z) (val z , a))
                            (λ { (s , eq) → s , (eq , reflˢ) })
                            chainX
                       ◅◅ return (⊑-refl , (transport-refl X (val e') , a≈a')) })
                  (λ {w} {w'} p → λ { (e , a) → ≈-refl (⟨ ρ ⟩ᵒ (X ×ᵖ Kᵖ S)) })
  ; strᵉ-costrᵉ = λ {ρ} {X} → λ { (e , a) → ≈-refl (⟨ ρ ⟩ᵒ X) , reflˢ }
  ; costrᵉ-strᵉ = λ {ρ} {X} E → ≈-refl (⟨ ρ ⟩ᵒ (X ×ᵖ Kᵖ S))
  }
  where open Setoid S renaming (refl to reflˢ)

-- Closure: the terminal object (Unit).

𝟙ᵖ-eternalᵒ : Eternalᵒ 𝟙ᵖ
𝟙ᵖ-eternalᵒ = record
  { extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (nec {ρ})
  ; extᵉ-≤    = λ _ _ → tt
  ; extᵉ-u    = λ _ → tt
  ; extᵉ-μ    = λ _ → tt
  ; strᵉ      = λ {ρ} {X} → pmap
                  (λ {w} → λ { (e , u) → mk⟨⟩ (acc e) (val e , u) })
                  (λ {w} {(e , u)} {(e' , u')} → λ { (chainX , _) →
                       gmap (λ z → mk⟨⟩ (acc z) (val z , u))
                            (λ { (s , eq) → s , (eq , tt) })
                            chainX
                       ◅◅ return (⊑-refl , (transport-refl X (val e') , tt)) })
                  (λ {w} {w'} p → λ { (e , u) → ≈-refl (⟨ ρ ⟩ᵒ (X ×ᵖ 𝟙ᵖ)) })
  ; strᵉ-costrᵉ = λ {ρ} {X} → λ { (e , u) → ≈-refl (⟨ ρ ⟩ᵒ X) , tt }
  ; costrᵉ-strᵉ = λ {ρ} {X} E → ≈-refl (⟨ ρ ⟩ᵒ (X ×ᵖ 𝟙ᵖ))
  }
  where
    nec : ∀ {ρ} → 𝟙ᵖ →ᵖ [ ρ ]ᵒ 𝟙ᵖ
    nec = pmap (λ _ → mk[] (λ _ → tt) (λ _ _ → tt)) (λ _ _ → tt) (λ _ _ _ → tt)

-- Closure: the initial object (Empty).

𝟘ᵖ-eternalᵒ : Eternalᵒ 𝟘ᵖ
𝟘ᵖ-eternalᵒ = record
  { extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (initialᵖ {[ ρ ]ᵒ 𝟘ᵖ})
  ; extᵉ-≤    = λ _ ()
  ; extᵉ-u    = λ ()
  ; extᵉ-μ    = λ ()
  ; strᵉ      = λ {ρ} {X} → pmap
                  (λ {w} x → ⊥-elim (proj₂ x))
                  (λ {w} {x} _ → ⊥-elim (proj₂ x))
                  (λ {w} {w'} p x → ⊥-elim (proj₂ x))
  ; strᵉ-costrᵉ = λ {ρ} {X} {w} x → ⊥-elim (proj₂ x)
  ; costrᵉ-strᵉ = λ {ρ} {X} E → ⊥-elim (proj₂ (val E))
  }

-- Closure: the boolean object. `𝔹ᵖ` *is* the constant presheaf on the
-- booleans, so its eternal structure is `Kᵖ-eternalᵒ` at that setoid.

𝔹ᵖ-eternalᵒ : Eternalᵒ 𝔹ᵖ
𝔹ᵖ-eternalᵒ = Kᵖ-eternalᵒ (setoid Bool)

-- Closure: binary products of eternal objects. The product's necessitation
-- combines the factors' through the box's lax monoidality, and every law
-- reduces componentwise to the corresponding law of a factor.

×ᵖ-nec : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ} → (A ×ᵖ B) →ᵖ [ ρ ]ᵒ (A ×ᵖ B)
×ᵖ-nec eA eB {ρ} = []-monoidal ∘ᵖ mapˣᵐ (Eternalᵒ.necᵉ eA {ρ}) (Eternalᵒ.necᵉ eB {ρ})

-- The product's extraction, the mate of `×ᵖ-nec`.

×ᵖ-ext : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ} → ⟨ ρ ⟩ᵒ (A ×ᵖ B) →ᵖ (A ×ᵖ B)
×ᵖ-ext eA eB {ρ} = ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (×ᵖ-nec eA eB {ρ})

-- The product's extraction decomposes into the factors' extractions: each
-- component reads its factor through the shared accessibility witness,
-- bridged by that factor's `extᵉ-mate`.
×ᵖ-ext-dec : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ} → ×ᵖ-ext eA eB {ρ}
           ≈ᵐ ⟨ Eternalᵒ.extᵉ eA ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ , Eternalᵒ.extᵉ eB ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ
×ᵖ-ext-dec {A} {B} eA eB {ρ} E =
    ≈-sym A (Eternalᵒ.extᵉ-mate eA (mk⟨⟩ (acc E) (proj₁ (val E))))
  , ≈-sym B (Eternalᵒ.extᵉ-mate eB (mk⟨⟩ (acc E) (proj₂ (val E))))

×ᵖ-eternalᵒ : ∀ {A B} → Eternalᵒ A → Eternalᵒ B → Eternalᵒ (A ×ᵖ B)
×ᵖ-eternalᵒ {A} {B} eA eB = record
  { extᵉ      = ×ᵖ-ext eA eB
  ; extᵉ-≤    = ×-strength.product-laws.ext×-≤ eA eB (×ᵖ-ext eA eB) (×ᵖ-ext-dec eA eB)
  ; extᵉ-u    = ×-strength.product-laws.ext×-u eA eB (×ᵖ-ext eA eB) (×ᵖ-ext-dec eA eB)
  ; extᵉ-μ    = alg
  ; strᵉ      = ×-strength.strᵉ-× eA eB
  ; strᵉ-costrᵉ = ×-strength.product-laws.strᵉ-costrᵉ-× eA eB (×ᵖ-ext eA eB) (×ᵖ-ext-dec eA eB)
  ; costrᵉ-strᵉ = ×-strength.product-laws.costrᵉ-strᵉ-× eA eB (×ᵖ-ext eA eB) (×ᵖ-ext-dec eA eB)
  }
  where
    -- Necessitating through a composite witness agrees with necessitating
    -- twice: `extᵉ-μ`, bridged at each end by `extᵉ-mate` (an `Eternalᵒ`'s
    -- `extᵉ` is an abstract field, hence not *definitionally* the mate of
    -- its `necᵉ`).
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

    -- The product's law holds componentwise: both sides feed the two factors'
    -- necessitations the same pair of accessibility witnesses.
    alg : ∀ {ρ₁ ρ₂ w} → (E : ⟨ ρ₁ ⟩ᶜ (⟨ ρ₂ ⟩ᵒ (A ×ᵖ B)) w)
        → _≈_ (A ×ᵖ B)
            (fun (app (×ᵖ-nec eA eB) (val (val E))) (⊑-trans (acc (val E)) (acc E)))
            (fun (app (×ᵖ-nec eA eB)
                   ( fun (app (Eternalᵒ.necᵉ eA) (proj₁ (val (val E)))) (acc (val E))
                   , fun (app (Eternalᵒ.necᵉ eB) (proj₂ (val (val E)))) (acc (val E)) ))
                 (acc E))
    alg E =
        comp eA (mk⟨⟩ (acc E) (mk⟨⟩ (acc (val E)) (proj₁ (val (val E)))))
      , comp eB (mk⟨⟩ (acc E) (mk⟨⟩ (acc (val E)) (proj₂ (val (val E)))))

-- The product's eternal extraction acts componentwise (the closure is
-- compatible with the projections).

×ᵖ-eternalᵒ-extᵉ : ∀ {A B} → (eA : Eternalᵒ A) → (eB : Eternalᵒ B) → ∀ {ρ}
                 → Eternalᵒ.extᵉ (×ᵖ-eternalᵒ eA eB) {ρ}
                 ≈ᵐ ⟨ Eternalᵒ.extᵉ eA ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ , Eternalᵒ.extᵉ eB ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ
×ᵖ-eternalᵒ-extᵉ eA eB = ×ᵖ-ext-dec eA eB
