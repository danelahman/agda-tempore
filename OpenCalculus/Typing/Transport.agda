------------------------------------------------------------------
-- Transport of open derivations along equations                --
--                                                              --
-- A derivation moved along an equation of its context or its   --
-- type erases to the same raw term.                            --
------------------------------------------------------------------

open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.Transport (S : LanguageSpec) where

open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Hypotheses      S
open import OpenCalculus.Typing          S
open import OpenCalculus.Typing.Erasure  S

ctx-castᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {A : OVType Θ}
          → Γ ≡ Γ' → Q ∣ Γ ⊢V⦂ A → Q ∣ Γ' ⊢V⦂ A
ctx-castᵛ refl V = V

ctx-castᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {C : OCType Θ}
          → Γ ≡ Γ' → Q ∣ Γ ⊢C⦂ C → Q ∣ Γ' ⊢C⦂ C
ctx-castᶜ refl M = M

⌊ctx-castᵛ⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {A : OVType Θ}
            → (p : Γ ≡ Γ') → (V : Q ∣ Γ ⊢V⦂ A) → ⌊ ctx-castᵛ p V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
⌊ctx-castᵛ⌋ refl V = refl

⌊ctx-castᶜ⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {C : OCType Θ}
            → (p : Γ ≡ Γ') → (M : Q ∣ Γ ⊢C⦂ C) → ⌊ ctx-castᶜ p M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
⌊ctx-castᶜ⌋ refl M = refl

⌊ty-subst⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A A' : OVType Θ}
           → (p : A ≡ A') → (V : Q ∣ Γ ⊢V⦂ A) → ⌊ ty-subst p V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
⌊ty-subst⌋ refl V = refl

⌊c-subst⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C C' : OCType Θ}
          → (p : C ≡ C') → (M : Q ∣ Γ ⊢C⦂ C) → ⌊ c-subst p M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
⌊c-subst⌋ refl M = refl
