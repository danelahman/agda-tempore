------------------------------------------------------------------
-- Completeness of inference for scope-closed typings           --
--                                                              --
-- A scope-closed typing over the empty scope from no           --
-- hypotheses has satisfiable hypotheses, so inference does not --
-- refute the term, and every scheme it answers has a closed    --
-- instance at which the principal type is below the typing's   --
-- (`completeness`), by the scheme's `factor`.                  --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import Language.Spec

open import Grades.Hints using (SystemHints)
open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Inference.ScopeClosed (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open import PolymorphicCalculus.Syntax.Types                 S using (OCType)
open import PolymorphicCalculus.Syntax.Contexts              S using (OCtx; _[_]ᶜᵗˣ; [id]ᶜᵗˣ)
open import PolymorphicCalculus.Syntax.GradeSubstitution     S
open import PolymorphicCalculus.Hypotheses                   S using (∅ᴴ; ⊩ᴵ-∅; _∣_<:̂ᶜ_)
open import PolymorphicCalculus.Hypotheses.Instances         S using (_⊨_)
open import PolymorphicCalculus.Typing                       S using (_∣_⊢C⦂_)
open import PolymorphicCalculus.Typing.Erasure               S using (⌊_⌋ᶜ)
open import PolymorphicCalculus.Syntax.Raw                   S using (RawC)
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S using (_[_]ᴿᶜ; [id]ᴿᶜ)
open import PolymorphicCalculus.Inference.Principality S
  using (PrincipalScheme; module PrincipalScheme; Typable; typable; typed; untypable)
open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer; infer-complete)

open PrincipalScheme

private

  -- the scope-closed typing as a typing at the identity instance

  at-id : ∀ {n} {Γ : OCtx ∅ˢ n} {M : RawC ∅ˢ n} {C : OCType ∅ˢ}
        → (D : ∅ᴴ ∣ Γ ⊢C⦂ C) → ⌊ D ⌋ᶜ ≡ M
        → Σ[ D' ∈ ∅ᴴ ∣ Γ [ idˢ ]ᶜᵗˣ ⊢C⦂ C ] ⌊ D' ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ
  at-id {Γ = Γ} {M} D e =
    subst (λ Γ' → Σ[ D' ∈ ∅ᴴ ∣ Γ' ⊢C⦂ _ ] ⌊ D' ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ) (sym ([id]ᶜᵗˣ Γ))
          (D , trans e (sym ([id]ᴿᶜ M)))

  ⊤-sat : (idˢ {∅ˢ}) ⊨ ∅ᴴ
  ⊤-sat = ⊩ᴵ-∅

completeness : ∀ {n} {Γ : OCtx ∅ˢ n} {M : RawC ∅ˢ n} {C : OCType ∅ˢ}
             → (D : ∅ᴴ ∣ Γ ⊢C⦂ C) → ⌊ D ⌋ᶜ ≡ M
             → (¬ infer Γ M ≡ untypable)
               × (∀ {p} → infer Γ M ≡ typed p
                  → Σ[ δ ∈ Subst (Θ̃ p) ∅ˢ ] (δ ⊨ Q̃ p) × (∅ᴴ ∣ X̃ p [ δ ]ᶜ <:̂ᶜ C))
completeness {Γ = Γ} {M} {C} D e =
  infer-complete Γ M (typable ∅ˢ idˢ ∅ᴴ C (proj₁ D') (proj₂ D') (idˢ , ⊤-sat)) ,
  λ {p} _ → scheme p
  where
    D' = at-id D e

    scheme : (p : PrincipalScheme Γ M)
           → Σ[ δ ∈ Subst (Θ̃ p) ∅ˢ ] (δ ⊨ Q̃ p) × (∅ᴴ ∣ X̃ p [ δ ]ᶜ <:̂ᶜ C)
    scheme p with factor p idˢ ∅ᴴ (proj₁ D') (proj₂ D') idˢ ⊤-sat
    ... | δ , _ , h , st = δ , h , subst (λ C' → ∅ᴴ ∣ X̃ p [ δ ]ᶜ <:̂ᶜ C') ([id]ᶜ C) st
