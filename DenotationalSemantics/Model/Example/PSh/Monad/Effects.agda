------------------------------------------------------------------------
-- The algebraic operations and delays of the effect monad, and the    --
-- box-strength. Operations, delays, and the strength all mention the   --
-- box modality graded by the *resource* projection `mapᵉ` of the       --
-- relevant effect grade; the effect accessibility `_⊑ᵉ[_]_` used by    --
-- the monad tree feeds the box via `⊑ᵉ-resource`.                      --
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
         (Wld : World (LanguageSpec.Grades S))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

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
open Category PShCat using (mapˣᵐ; map⇒ᵐ; sndᵐ)

-- OPERATIONS AND DELAYS

-- A delay: the box `[ of-natʳ τ ]` is entered by an effect step of
-- grade `of-natᵉ τ`, whose resource projection is `of-natʳ τ`.

delayᵀ : ∀ {A ε} → (τ : ℕ)
       → [ of-natʳ τ ]ᵒ (Tᵒ A ε) →ᵖ Tᵒ A (of-natᵉ τ ·ₑ ε)
delayᵀ τ =
  pmap (λ x → delay-node τ
    (λ q → x (⊑-mono (≾ᵣ-reflexive map-of-natᵉ) (⊑ᵉ-resource q))))

-- An algebraic operation.

opᵀ : ∀ {A ε} → (op : Op)
    → ⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε)
    →ᵖ Tᵒ A (op-grade op ·ₑ ε)
opᵀ op =
  pmap (λ { (v , x) → op-node op v (λ q y → x (⊑ᵉ-resource q) y) })

-- Naturality

delayᵀ-nat : ∀ {A B ε} → (τ : ℕ) → (f : A →ᵖ B)
           → delayᵀ {ε = ε} τ ∘ᵖ [ of-natʳ τ ]ᶠ (Tᶠ f) ≡ Tᶠ f ∘ᵖ delayᵀ τ
delayᵀ-nat τ f = →ᵖ-ext (λ x → refl)

opᵀ-nat : ∀ {A B ε} → (op : Op) → (f : A →ᵖ B)
        → opᵀ {ε = ε} op ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (Tᶠ f)))
        ≡ Tᶠ f ∘ᵖ opᵀ op
opᵀ-nat op f = →ᵖ-ext (λ { (v , x) → refl })

-- Algebraicity: the operations commute with the monad multiplication.

delayᵀ-algebraicity : ∀ {A ε' ε''} → (τ : ℕ)
                    → μᵀ {A} {of-natᵉ τ ·ₑ ε'} {ε''} ∘ᵖ delayᵀ {ε = ε'} τ
                    ≡ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                      ∘ᵖ delayᵀ τ ∘ᵖ [ of-natʳ τ ]ᶠ (μᵀ {A} {ε'} {ε''})
delayᵀ-algebraicity τ = →ᵖ-ext (λ x → refl)

opᵀ-algebraicity : ∀ {A ε ε'} → (op : Op)
                 → μᵀ {A} {op-grade op ·ₑ ε} {ε'} ∘ᵖ opᵀ {ε = ε} op
                 ≡ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                   ∘ᵖ opᵀ op
                   ∘ᵖ mapˣᵐ idᵖ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (μᵀ {A} {ε} {ε'})))
opᵀ-algebraicity op = →ᵖ-ext (λ { (v , x) → refl })

-- STRENGTH

-- Coercion of a resource-accessibility witness along an equality of grades.

⊑-coe : ∀ {ρ ρ' w w'} → ρ ≡ ρ' → w ⊑[ ρ ] w' → w ⊑[ ρ' ] w'
⊑-coe e = ⊑-mono (≾ᵣ-reflexive e)

-- The strength threads a box `[ mapᵉ ε ] A` along the tree: at every
-- effect step it advances the box (via `⊑ᵉ-resource` + `⊑-trans`), and
-- pairs the extracted `A` with the returned `B` at the leaves.

{-# TERMINATING #-}
strˢ : ∀ {A B ε w}
     → (∀ {w'} → w ⊑[ mapᵉ ε ] w' → carrier A w') → Tˢ B ε w → Tˢ (A ×ᵖ B) ε w
strˢ box (leaf b) =
  leaf (box (⊑-coe (sym map-uᵉ) ⊑-refl) , b)
strˢ box (op-node op v k) =
  op-node op v (λ q y →
    strˢ (λ r → box (⊑-coe (sym map-·ᵉ) (⊑-trans (⊑ᵉ-resource q) r))) (k q y))
strˢ box (delay-node τ k) =
  delay-node τ (λ q →
    strˢ (λ r → box (⊑-coe (sym map-·ᵉ) (⊑-trans (⊑ᵉ-resource q) r))) (k q))
strˢ box (sub p t) =
  sub p (strˢ (λ r → box (⊑-mono (map-monotoneᵉ p) r)) t)

strᵀ : ∀ {A B ε} → [ mapᵉ ε ]ᵒ A ×ᵖ Tᵒ B ε →ᵖ Tᵒ (A ×ᵖ B) ε
strᵀ = pmap (λ { (a , t) → strˢ a t })

-- Strength is natural

{-# TERMINATING #-}
strˢ-nat : ∀ {A A' B B' ε w} → (f : A →ᵖ A') → (g : B →ᵖ B')
         → (box : ∀ {w'} → w ⊑[ mapᵉ ε ] w' → carrier A w') → (t : Tˢ B ε w)
         → strˢ (λ r → app f (box r)) (Tˢᶠ g t) ≡ Tˢᶠ (mapˣᵐ f g) (strˢ box t)
strˢ-nat f g box (leaf b)          = refl
strˢ-nat f g box (op-node op v k)  =
  cong (op-node op v)
    (ifun-ext (fun-ext (λ q → fun-ext (λ y →
      strˢ-nat f g (λ r → box (⊑-coe (sym map-·ᵉ) (⊑-trans (⊑ᵉ-resource q) r))) (k q y)))))
strˢ-nat f g box (delay-node τ k)  =
  cong (delay-node τ)
    (ifun-ext (fun-ext (λ q →
      strˢ-nat f g (λ r → box (⊑-coe (sym map-·ᵉ) (⊑-trans (⊑ᵉ-resource q) r))) (k q))))
strˢ-nat f g box (sub p t)         =
  cong (sub p) (strˢ-nat f g (λ r → box (⊑-mono (map-monotoneᵉ p) r)) t)

strᵀ-nat : ∀ {A A' B B' ε} → (f : A →ᵖ A') → (g : B →ᵖ B')
         → strᵀ {A'} {B'} ∘ᵖ mapˣᵐ ([ mapᵉ ε ]ᶠ f) (Tᶠ g)
         ≡ Tᶠ (mapˣᵐ f g) ∘ᵖ strᵀ {A} {B}
strᵀ-nat f g = →ᵖ-ext (λ { (a , t) → strˢ-nat f g a t })

-- Strength projects away on the second component

{-# TERMINATING #-}
strˢ-snd : ∀ {A B ε w}
         → (box : ∀ {w'} → w ⊑[ mapᵉ ε ] w' → carrier A w') → (t : Tˢ B ε w)
         → Tˢᶠ sndᵐ (strˢ box t) ≡ t
strˢ-snd box (leaf b)          = refl
strˢ-snd box (op-node op v k)  =
  cong (op-node op v)
    (ifun-ext (fun-ext (λ q → fun-ext (λ y →
      strˢ-snd (λ r → box (⊑-coe (sym map-·ᵉ) (⊑-trans (⊑ᵉ-resource q) r))) (k q y)))))
strˢ-snd box (delay-node τ k)  =
  cong (delay-node τ)
    (ifun-ext (fun-ext (λ q →
      strˢ-snd (λ r → box (⊑-coe (sym map-·ᵉ) (⊑-trans (⊑ᵉ-resource q) r))) (k q))))
strˢ-snd box (sub p t)         =
  cong (sub p) (strˢ-snd (λ r → box (⊑-mono (map-monotoneᵉ p) r)) t)

strᵀ-sndᵐ : ∀ {A B ε} → Tᶠ sndᵐ ∘ᵖ strᵀ {A} {B} {ε} ≡ sndᵐ
strᵀ-sndᵐ = →ᵖ-ext (λ { (a , t) → strˢ-snd a t })
