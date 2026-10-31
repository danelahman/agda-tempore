------------------------------------------------------------------------
-- Handler values for the free graded monad.                          --
--                                                                    --
-- An element of `Hᵖ A ε B ε'` at a world is a family, over the       --
-- handled grades `ε₀ ≾ₑ ε`, of Kripke functions                      --
-- `Tᵒ A ε₀ ⇒ᶜ Tᵒ B (ε₀ ·ₑ ε')`, natural in `ε₀` along `T-≤`.         --
-- Equality, transport, application and abstraction are those of      --
-- `_⇒ᵖ_`, taken at every index.                                      --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.HandlerValues
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Product using (_,_; proj₁; proj₂)

open LanguageSpec S
open GradeSystemInterface Grades
open World Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base Grades Wld

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy
  using (Tᵒ; T-≤)

-- Families of maps over the handled grades, and their naturality

Familyᵖ : PSh → PSh → E → PSh → E → Set
Familyᵖ X A ε B ε' = ∀ {ε₀} → ε₀ ≾ₑ ε → X ×ᵖ Tᵒ A ε₀ →ᵖ Tᵒ B (ε₀ ·ₑ ε')

Naturalᵖ : ∀ {X A ε B ε'} → Familyᵖ X A ε B ε' → Set
Naturalᵖ {ε = ε} f =
  ∀ {ε₀ ε₁} → (p₀ : ε₀ ≾ₑ ε) → (p₁ : ε₁ ≾ₑ ε) → (q : ε₀ ≾ₑ ε₁)
  → f p₁ ∘ᵖ mapˣᵐ idᵖ (T-≤ q) ≈ᵖ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵖ f p₀

-- Elements

record Hᶜ (A : PSh) (ε : E) (B : PSh) (ε' : E) (w : W) : Set where
  constructor mkʰ
  field
    hfun   : ∀ {ε₀} → ε₀ ≾ₑ ε → (Tᵒ A ε₀ ⇒ᶜ Tᵒ B (ε₀ ·ₑ ε')) w
    hfun-≤ : ∀ {ε₀ ε₁} → (p₀ : ε₀ ≾ₑ ε) → (p₁ : ε₁ ≾ₑ ε) → (q : ε₀ ≾ₑ ε₁)
           → ∀ {w'} → (r : w ⊑[ uᵣ ] w') → (t : carrier (Tᵒ A ε₀) w')
           → _≈_ (Tᵒ B (ε₁ ·ₑ ε'))
                 (fun (hfun p₁) r (app (T-≤ q) t))
                 (app (T-≤ (·ₑ-monoˡ-≾ₑ q)) (fun (hfun p₀) r t))

open Hᶜ public

-- The presheaf

Hᵖ : PSh → E → PSh → E → PSh
Hᵖ A ε B ε' = record
  { carrier         = Hᶜ A ε B ε'
  ; _≈_             = λ F G → ∀ {ε₀} (p : ε₀ ≾ₑ ε) → _≈_ (X p) (hfun F p) (hfun G p)
  ; ≈-refl          = λ p q a → ≈-refl (Y p)
  ; ≈-sym           = λ e p q a → ≈-sym (Y p) (e p q a)
  ; ≈-trans         = λ e e' p q a → ≈-trans (Y p) (e p q a) (e' p q a)
  ; transport       = λ r F → mkʰ (λ p → transport (X p) r (hfun F p))
                                  (λ p₀ p₁ q r' t → hfun-≤ F p₀ p₁ q (⊑ᵘ-trans r r') t)
  ; transport-cong  = λ r e p q a → e p (⊑ᵘ-trans r q) a
  ; transport-refl  = λ F p q a → fun-irr (hfun F p) (⊑ᵘ-trans ⊑-refl q) q a
  ; transport-trans = λ r r' F p q a →
                        fun-irr (hfun F p) (⊑ᵘ-trans (⊑ᵘ-trans r r') q) (⊑ᵘ-trans r (⊑ᵘ-trans r' q)) a
  }
  where
    X : ∀ {ε₀} → ε₀ ≾ₑ ε → PSh
    X {ε₀} _ = Tᵒ A ε₀ ⇒ᵖ Tᵒ B (ε₀ ·ₑ ε')
    Y : ∀ {ε₀} → ε₀ ≾ₑ ε → PSh
    Y {ε₀} _ = Tᵒ B (ε₀ ·ₑ ε')

-- Application at an index

projʰ : ∀ {A ε B ε' ε₀} → ε₀ ≾ₑ ε → Hᵖ A ε B ε' →ᵖ (Tᵒ A ε₀ ⇒ᵖ Tᵒ B (ε₀ ·ₑ ε'))
projʰ {B = B} p = pmap (λ F → hfun F p) (λ e → e p) (λ r F q a → ≈-refl (Tᵒ B _))

appʰᵖ : ∀ {A ε B ε'} → Familyᵖ (Hᵖ A ε B ε') A ε B ε'
appʰᵖ p = uncurryᵖ (projʰ p)

appʰᵖ-nat : ∀ {A ε B ε'} → Naturalᵖ (appʰᵖ {A} {ε} {B} {ε'})
appʰᵖ-nat p₀ p₁ q (F , t) = hfun-≤ F p₀ p₁ q ⊑-refl t

appʰᵖ-∘-nat : ∀ {X A ε B ε'} → (h : X →ᵖ Hᵖ A ε B ε')
            → Naturalᵖ (λ p → appʰᵖ p ∘ᵖ mapˣᵐ h idᵖ)
appʰᵖ-∘-nat h p₀ p₁ q (x , t) = hfun-≤ (app h x) p₀ p₁ q ⊑-refl t

-- Abstraction

curryʰᵖ : ∀ {X A ε B ε'} → (f : Familyᵖ X A ε B ε') → Naturalᵖ f
        → X →ᵖ Hᵖ A ε B ε'
curryʰᵖ {X} f nf = pmap
  (λ x → mkʰ (λ p → app (curryᵖ (f p)) x)
             (λ p₀ p₁ q r t → nf p₀ p₁ q (transport X r x , t)))
  (λ e p → app-cong (curryᵖ (f p)) e)
  (λ r x p → nat (curryᵖ (f p)) r x)

curryʰᵖ-cong : ∀ {X A ε B ε'} {f g : Familyᵖ X A ε B ε'}
             → (nf : Naturalᵖ f) → (ng : Naturalᵖ g)
             → (∀ {ε₀} → (p : ε₀ ≾ₑ ε) → f p ≈ᵖ g p)
             → curryʰᵖ f nf ≈ᵖ curryʰᵖ g ng
curryʰᵖ-cong {X} nf ng e x p r t = e p (transport X r x , t)

curryʰᵖ-β : ∀ {X A ε B ε' ε₀} → (f : Familyᵖ X A ε B ε') → (nf : Naturalᵖ f)
          → (p : ε₀ ≾ₑ ε)
          → appʰᵖ p ∘ᵖ mapˣᵐ (curryʰᵖ f nf) idᵖ ≈ᵖ f p
curryʰᵖ-β {X} {A} {ε₀ = ε₀} f nf p (x , t) =
  app-cong (f p) (transport-refl X x , ≈-refl (Tᵒ A ε₀))

curryʰᵖ-η : ∀ {X A ε B ε'} → (h : X →ᵖ Hᵖ A ε B ε')
          → (nh : Naturalᵖ (λ p → appʰᵖ p ∘ᵖ mapˣᵐ h idᵖ))
          → curryʰᵖ (λ p → appʰᵖ p ∘ᵖ mapˣᵐ h idᵖ) nh ≈ᵖ h
curryʰᵖ-η {B = B} {ε' = ε'} h nh x {ε₀} p r t = ≈-trans (Tᵒ B (ε₀ ·ₑ ε'))
  (nat h r x p ⊑-refl t)
  (fun-irr (hfun (app h x) p) (⊑ᵘ-trans r ⊑-refl) r t)
