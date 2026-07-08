------------------------------------------------------------------------
-- Effect handling for the free graded monad on discrete presheaves.    --
--                                                                    --
-- A handler is a family of *clause morphisms*, one per operation `op`   --
-- and residual effect grade `ε''`. `T-alg-of-handlerˢ` folds the tree,  --
-- reinterpreting every `op-node` by the matching clause, keeping delays --
-- as delays, and returning the leaf value (regraded).                   --
--                                                                    --
-- The clauses being morphisms (natural families) is exactly what lets   --
-- the fold recurse under an operation: the same clauses are reused at    --
-- the reached world, with no need to transport the handler along the    --
-- discrete presheaves (which carry no functorial action). The op-node   --
-- already stores its whole continuation *box*, so the clause's boxed     --
-- argument is available directly.                                       --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.Monad.Handling
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
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
open import DenotationalSemantics.Model.Example.PSh.Monad.Effects S Wld GTy

open import DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ; map⇒ᵐ)

-- A handler: a clause morphism for every operation and residual grade.

Handlerˢ : PSh → Set
Handlerˢ A = (op : Op) → (ε'' : E)
           → ⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε'')
               →ᵖ Tᵒ A (op-grade op ·ₑ ε'')

-- The T-algebra folding a handler over a computation tree.

T-alg-of-handlerˢ : ∀ {A ε ε' w} → Handlerˢ A → Tˢ (Tᵒ A ε') ε w → Tˢ A (ε ·ₑ ε') w
T-alg-of-handlerˢ {ε' = ε'} h (leaf s) =
  ε-substˢ (sym (·ₑ-identityˡ ε')) s
T-alg-of-handlerˢ {ε' = ε'} h (op-node {ε = ε₀} op v k) =
  ε-substˢ (sym (·ₑ-assoc (op-grade op) ε₀ ε'))
    (app (h op (ε₀ ·ₑ ε')) (v , λ r y → T-alg-of-handlerˢ h (k r y)))
T-alg-of-handlerˢ {ε' = ε'} h (delay-node {ε = ε₀} τ k) =
  ε-substˢ (sym (·ₑ-assoc (of-natᵉ τ) ε₀ ε'))
    (delay-node τ (λ r → T-alg-of-handlerˢ h (k r)))
T-alg-of-handlerˢ h (sub p t) =
  sub (·ₑ-monoˡ-≾ₑ p) (T-alg-of-handlerˢ h t)

T-alg-of-handlerᵀ : ∀ {A ε ε'} → Handlerˢ A → Tᵒ (Tᵒ A ε') ε →ᵖ Tᵒ A (ε ·ₑ ε')
T-alg-of-handlerᵀ h = pmap (T-alg-of-handlerˢ h)

-- The three algebra laws hold definitionally: each side reduces to the
-- same tree (returning / re-delaying / applying the clause).

T-alg-of-handlerᵀ-ηᵀ : ∀ {A ε'} → (h : Handlerˢ A)
                     → T-alg-of-handlerᵀ h ∘ᵖ ηᵀ {Tᵒ A ε'}
                     ≡ ε-substᵀ (sym (·ₑ-identityˡ ε'))
T-alg-of-handlerᵀ-ηᵀ h = →ᵖ-ext (λ s → refl)

T-alg-of-handlerᵀ-delayᵀ : ∀ {A ε' ε''} → (τ : ℕ) → (h : Handlerˢ A)
                         → T-alg-of-handlerᵀ h ∘ᵖ delayᵀ {Tᵒ A ε''} {ε'} τ
                         ≡ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                           ∘ᵖ delayᵀ τ ∘ᵖ [ of-natʳ τ ]ᶠ (T-alg-of-handlerᵀ h)
T-alg-of-handlerᵀ-delayᵀ τ h = →ᵖ-ext (λ x → refl)

T-alg-of-handlerᵀ-opᵀ : ∀ {A ε' ε''} → (op : Op) → (h : Handlerˢ A)
                      → T-alg-of-handlerᵀ h ∘ᵖ opᵀ {Tᵒ A ε''} {ε'} op
                      ≡ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε' ε''))
                        ∘ᵖ h op (ε' ·ₑ ε'')
                        ∘ᵖ mapˣᵐ idᵖ
                             ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (T-alg-of-handlerᵀ h)))
T-alg-of-handlerᵀ-opᵀ op h = →ᵖ-ext (λ { (v , boxk) → refl })
