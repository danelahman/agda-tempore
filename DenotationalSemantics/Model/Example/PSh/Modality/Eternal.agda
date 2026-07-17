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
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
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
  ∘ᵐ-assoc; ∘ᵐ-congˡ; ∘ᵐ-congʳ; ∘ᵐ-identityˡ; ∘ᵐ-identityʳ;
  ≈ᵐ-refl; ≈ᵐ-sym; ≈ᵐ-trans)

open import DenotationalSemantics.Model.Modality.Past PShCat RGrade using (Past)
open Past PShPast using (⟨⟩-∘ᵐ; ⟨⟩-idᵐ; ⟨⟩-congᶠ)

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
  { necᵉ      = nec
  ; extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (nec {ρ})
  ; extᵉ-mate = λ {ρ} _ → tt
  ; necᵉ-u    = λ _ _ → tt
  ; necᵉ-≤    = λ _ _ _ → tt
  ; necᵉ-δ    = λ _ _ _ → tt
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
  { necᵉ      = λ {ρ} → initialᵖ {[ ρ ]ᵒ 𝟘ᵖ}
  ; extᵉ      = λ {ρ} → ε⊣ ∘ᵖ ⟨ ρ ⟩ᶠ (initialᵖ {[ ρ ]ᵒ 𝟘ᵖ})
  ; extᵉ-mate = λ {ρ} ()
  ; necᵉ-u    = λ ()
  ; necᵉ-≤    = λ _ ()
  ; necᵉ-δ    = λ ()
  ; extᵉ-μ    = λ ()
  ; strᵉ      = λ {ρ} {X} → pmap
                  (λ {w} x → ⊥-elim (proj₂ x))
                  (λ {w} {x} _ → ⊥-elim (proj₂ x))
                  (λ {w} {w'} p x → ⊥-elim (proj₂ x))
  ; strᵉ-costrᵉ = λ {ρ} {X} {w} x → ⊥-elim (proj₂ x)
  ; costrᵉ-strᵉ = λ {ρ} {X} E → ⊥-elim (proj₂ (val E))
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
  ; strᵉ      = strᵉ×
  -- TODO: `strᵉ×` is a composite of isos (`⟨ρ⟩ᶠ assoc`, `eB.strᵉ`,
  -- `mapˣᵐ eA.strᵉ id`, `reassoc`), so it is an iso; the two laws say it
  -- inverts `costrᵉ`. Proof plan (prod-ext + factor laws): from
  -- `eA.strᵉ-costrᵉ`/`eB.strᵉ-costrᵉ` derive `⟨ρ⟩fst ∘ strᵉ ≈ fst` and the
  -- `extᵉ`-component, then relate `extᵉ_{A×B}` to `eA.extᵉ`/`eB.extᵉ` (as in
  -- the `comp`/`alg` lemmas above).
  ; strᵉ-costrᵉ = {!!}
  ; costrᵉ-strᵉ = {!!}
  }
  where
    nec : ∀ {ρ} → (A ×ᵖ B) →ᵖ [ ρ ]ᵒ (A ×ᵖ B)
    nec {ρ} = []-monoidal ∘ᵖ mapˣᵐ (Eternalᵒ.necᵉ eA {ρ}) (Eternalᵒ.necᵉ eB {ρ})

    -- Reassociation isos: `aⁿ` right-nests `(P × A) × B → P × (A × B)`,
    -- `aⁿ⁻¹` left-nests. Used around the factor strengths.
    aⁿ : ∀ {P} → (P ×ᵖ A) ×ᵖ B →ᵖ P ×ᵖ (A ×ᵖ B)
    aⁿ = ⟨ fstᵐ ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ

    aⁿ⁻¹ : ∀ {P} → P ×ᵖ (A ×ᵖ B) →ᵖ (P ×ᵖ A) ×ᵖ B
    aⁿ⁻¹ = ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ

    -- The `⟨_⟩`-strength for a product: bring the factors inside one at a
    -- time, using `eA`'s strength at object `X`, then `eB`'s at `X ×ᵖ A`,
    -- reassociating around them.
    strᵉ× : ∀ {ρ X} → ⟨ ρ ⟩ᵒ X ×ᵖ (A ×ᵖ B) →ᵖ ⟨ ρ ⟩ᵒ (X ×ᵖ (A ×ᵖ B))
    strᵉ× {ρ} {X} =
        ⟨ ρ ⟩ᶠ aⁿ
      ∘ᵐ Eternalᵒ.strᵉ eB
      ∘ᵐ mapˣᵐ (Eternalᵒ.strᵉ eA) idᵐ
      ∘ᵐ aⁿ⁻¹

    -- The inverse: the reverse composite of the factor costrengths.
    costr'× : ∀ {ρ X} → ⟨ ρ ⟩ᵒ (X ×ᵖ (A ×ᵖ B)) →ᵖ ⟨ ρ ⟩ᵒ X ×ᵖ (A ×ᵖ B)
    costr'× {ρ} {X} =
        aⁿ
      ∘ᵐ mapˣᵐ (Eternalᵒ.costrᵉ eA) idᵐ
      ∘ᵐ Eternalᵒ.costrᵉ eB
      ∘ᵐ ⟨ ρ ⟩ᶠ aⁿ⁻¹

    -- Reassociations are mutually inverse (product iso facts).
    -- CHECKPOINT: both reassociator-iso facts have the same residual implicit-
    -- inference issue (the final `⟨⟩ᵐ-unique … ≈ᵐ-refl ≈ᵐ-refl` leaves the
    -- projection objects as metas); the full proof terms are in memory. These
    -- are pure product-category facts (`×ᵐ-assoc`/`×ᵐ-assoc⁻¹` are mutually
    -- inverse) and would be cleaner as reusable Category lemmas.
    aⁿ-aⁿ⁻¹ : ∀ {P} → aⁿ {P} ∘ᵐ aⁿ⁻¹ {P} ≈ᵐ idᵐ
    aⁿ-aⁿ⁻¹ {P} = {!!}

    -- Symmetric to `aⁿ-aⁿ⁻¹` (fst/snd roles swapped). CHECKPOINT: the analogous
    -- proof term is written out in git/memory but has a residual implicit-
    -- inference issue; finish alongside the two record laws.
    aⁿ⁻¹-aⁿ : ∀ {P} → aⁿ⁻¹ {P} ∘ᵐ aⁿ {P} ≈ᵐ idᵐ
    aⁿ⁻¹-aⁿ {P} = {!!}

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
