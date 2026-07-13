------------------------------------------------------------------------
-- Interpretation of the well-typed terms (values and computations).    --
--                                                                    --
-- A value `Γ ⊢V⦂ A` is a morphism `⟦ Γ ⟧ →ᵐ ⟦ A ⟧ᵛ`; a computation     --
-- `Γ ⊢C⦂ C` is `⟦ Γ ⟧ →ᵐ ⟦ C ⟧ᶜ`. Variables use the machinery of        --
-- `Interpretation.Variables`. Effectful formers use the graded monad:   --
-- `return`↦`ηᵀ`, `⨟`↦`μᵀ ∘ Tᶠ- ∘ strᵀ` (environment threaded by the     --
-- adjunction unit `η⊣`), `perform`↦`opᵀ`, `delay`↦`delayᵀ`,             --
-- `coerce`↦`T-≤`. The Fitch formers use the adjunction: `box` transposes --
-- by `[ ρ ]ᶠ- ∘ η⊣`, and `unbox` extracts the underlying variable via    --
-- `unbox⇒var` and opens it with the counit `ε⊣`.                        --
--                                                                    --
-- `perform`'s parameter/arity are ground types, interpreted via the      --
-- coercion `⟦ type-of-gtype G ⟧ᵛ ≡ ⟦ G ⟧ᵍ` (`ty-gty`).                  --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Terms
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types S
open import Syntax.Contexts S
open import Syntax.Language S
open import Syntax.RenActions S using (unbox⇒var)

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤; εᵘ)
open Adjunction Adj using (η⊣; ε⊣)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE

-- The value-type interpretation of a ground type coincides with its
-- ground-type interpretation.

ty-gty : ∀ (G : GType) → ⟦ type-of-gtype G ⟧ᵛ ≡ ⟦ G ⟧ᵍ
ty-gty (Base b)     = refl
ty-gty Unit         = refl
ty-gty Empty        = refl
ty-gty (G₁ |×|ᵍ G₂) = cong₂ _×ᵐ_ (ty-gty G₁) (ty-gty G₂)
ty-gty ([ ρ ]ᵍ G)   = cong (λ O → [ ρ ]ᵒ O) (ty-gty G)

mutual

  ⟦_⟧ᵛᵗ : ∀ {Γ A} → Γ ⊢V⦂ A → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
  ⟦ var f x  ⟧ᵛᵗ = var-morphism f x
  ⟦ const c  ⟧ᵛᵗ = ⟦ c ⟧ᵏ ∘ᵐ terminalᵐ
  ⟦ ⋆        ⟧ᵛᵗ = terminalᵐ
  ⟦ ⦉ V , W ⦊ ⟧ᵛᵗ = ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ⟦ lam M    ⟧ᵛᵗ = curryᵐ ⟦ M ⟧ᶜᵗ

  ⟦_⟧ᶜᵗ : ∀ {Γ C} → Γ ⊢C⦂ C → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ
  ⟦ return V ⟧ᶜᵗ = ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ
  ⟦ _⨟_ {ε = ε} M N ⟧ᶜᵗ =
    μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ⟦ V · W    ⟧ᶜᵗ = appᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
  ⟦ match V `in M ⟧ᶜᵗ =
    ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ , sndᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
  ⟦ absurd V ⟧ᶜᵗ = initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {ε} op V M) =
    opᵀ op ∘ᵐ
      ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ
      , [ mapᵉ (op-grade op) ]ᶠ
          (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                         (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ))
        ∘ᵐ η⊣ ⟩ᵐ
  ⟦ delay τ M ⟧ᶜᵗ = delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ η⊣
  ⟦_⟧ᶜᵗ {Γ} (handle_`with_`in {A} {B} {ε} {ε'} M H N) =
    T-alg-of-handlerᵀ ⟦ H ⟧ʰᵗ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ
  ⟦ unbox w V M ⟧ᶜᵗ with unbox⇒var w V
  ... | ρ' , x , ρ'≾ρ =
    ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ ρ'≾ρ ∘ᵐ var-proj x ⟩ᵐ
  ⟦ box {ρ = ρ} V M ⟧ᶜᵗ =
    ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , [ ρ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η⊣ ⟩ᵐ
  ⟦ coerce p M ⟧ᶜᵗ = T-≤ p ∘ᵐ ⟦ M ⟧ᶜᵗ

  -- The semantic handler of a syntactic one. Each clause is closed
  -- (`[] ∷ param ∷ cont`), so it interprets to a context-free morphism; the
  -- `ty-gty` coercions adapt the ground-type parameter/arity to their
  -- value-type interpretations. It is context-free, hence inert under
  -- renaming and substitution.
  ⟦_⟧ʰᵗ : ∀ {B}
        → ((op : Op) → (ε'' : E) → (Γ' : Ctx)
             → Γ' ∷ type-of-gtype (param op)
                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
               ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
        → Handlerᵀ ⟦ B ⟧ᵛ
  ⟦ H ⟧ʰᵗ op ε'' =
    ⟦ H op ε'' [] ⟧ᶜᵗ ∘ᵐ
      mapˣᵐ
        ⟨ terminalᵐ , subst (λ O → ⟦ param op ⟧ᵍ →ᵐ O) (sym (ty-gty (param op))) idᵐ ⟩ᵐ
        ([ mapᵉ (op-grade op) ]ᶠ
          (map⇒ᵐ (subst (λ O → O →ᵐ ⟦ arity op ⟧ᵍ) (sym (ty-gty (arity op))) idᵐ) idᵐ))
