------------------------------------------------------------------
-- Completeness of inference for scope-closed typings           --
--                                                              --
-- A scope-closed typing of a raw term over the empty scope,    --
-- under the empty hypothesis set, is a typing whose            --
-- hypotheses are satisfiable: inference does not refute the    --
-- term, and every principal scheme it answers has a closed     --
-- instance satisfying its conditions at which the principal    --
-- type is a subtype of the typing's (`completeness`), by the   --
-- completeness clause (`factor`) of the scheme.                --
------------------------------------------------------------------

open import Data.List.Base using ([])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Inference.ScopeClosed (S : LanguageSpec) (opEnum : OpEnum S) where

open import OpenCalculus.Syntax.Types         S using (OCType)
open import OpenCalculus.Syntax.Contexts      S using (OCtx)
open import OpenCalculus.Syntax.Subst         S
open import OpenCalculus.Hypotheses           S using (∅ᴴ; ⊩ᴴ-∅; _∣_<:̂ᶜ_)
open import OpenCalculus.Hypotheses.Instances S using (_⊨_∣_)
open import OpenCalculus.Typing               S using (_∣_⊢C⦂_)
open import OpenCalculus.Typing.Erasure       S using (⌊_⌋ᶜ)
open import OpenCalculus.Syntax.Raw           S using (RawC)
open import OpenCalculus.Syntax.Raw.Subst     S using (_[_]ᴿᶜ; [id]ᴿᶜ)
open import OpenCalculus.Inference.Principality S
  using (PrincipalScheme; module PrincipalScheme; Typable; typable; typed; untypable)
open import OpenCalculus.Inference.SolverImpl S opEnum using (infer; infer-complete)

open PrincipalScheme

private

  -- the scope-closed typing as a typing at the identity instance

  at-id : ∀ {n} {Γ : OCtx ∅ˢ n} {M : RawC ∅ˢ n} {C : OCType ∅ˢ}
        → (D : ∅ᴴ ∣ Γ ⊢C⦂ C) → ⌊ D ⌋ᶜ ≡ M
        → Σ[ D' ∈ ∅ᴴ ∣ Γ [ idˢ ]ᶜᵗˣ ⊢C⦂ C ] ⌊ D' ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ
  at-id {Γ = Γ} {M} D e =
    subst (λ Γ' → Σ[ D' ∈ ∅ᴴ ∣ Γ' ⊢C⦂ _ ] ⌊ D' ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ) (sym ([id]ᶜᵗˣ Γ))
          (D , trans e (sym ([id]ᴿᶜ M)))

  ∅-sat : (idˢ {∅ˢ}) ⊨ ∅ᴴ ∣ []
  ∅-sat = ⊩ᴴ-∅ , []ᴬ

completeness : ∀ {n} {Γ : OCtx ∅ˢ n} {M : RawC ∅ˢ n} {C : OCType ∅ˢ}
             → (D : ∅ᴴ ∣ Γ ⊢C⦂ C) → ⌊ D ⌋ᶜ ≡ M
             → (¬ infer Γ M ≡ untypable)
               × (∀ {p} → infer Γ M ≡ typed p
                  → Σ[ δ ∈ Subst (Θ̃ p) ∅ˢ ] (δ ⊨ Q̃ p ∣ R̃ p) × (∅ᴴ ∣ X̃ p [ δ ]ᶜ <:̂ᶜ C))
completeness {Γ = Γ} {M} {C} D e =
  infer-complete Γ M (typable ∅ˢ idˢ ∅ᴴ C (proj₁ D') (proj₂ D') (idˢ , ∅-sat)) ,
  λ {p} _ → scheme p
  where
    D' = at-id D e

    scheme : (p : PrincipalScheme Γ M)
           → Σ[ δ ∈ Subst (Θ̃ p) ∅ˢ ] (δ ⊨ Q̃ p ∣ R̃ p) × (∅ᴴ ∣ X̃ p [ δ ]ᶜ <:̂ᶜ C)
    scheme p with factor p idˢ ∅ᴴ (proj₁ D') (proj₂ D') idˢ ∅-sat
    ... | δ , _ , h , st = δ , h , subst (λ C' → ∅ᴴ ∣ X̃ p [ δ ]ᶜ <:̂ᶜ C') ([id]ᶜ C) st
