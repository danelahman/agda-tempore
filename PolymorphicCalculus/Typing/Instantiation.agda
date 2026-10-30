------------------------------------------------------------------
-- Instantiation of the scope                                   --
--                                                              --
-- At every closed instance `δ ⊨ Q`, a typing under `Q` gives a --
-- scope-closed typing of the run-time erasure of the           --
-- instantiated term, at the instantiated context and type      --
-- (`scope-instantiation`). Handler clauses stay typed at their --
-- own grade variables.                                         --
------------------------------------------------------------------

open import Data.List.Base using ([])
open import Data.Product using (_,_)

open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.Instantiation (S : LanguageSpec) where

open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S
open import PolymorphicCalculus.Syntax.GradeSubstitution     S
open import PolymorphicCalculus.Hypotheses                   S
open import PolymorphicCalculus.Hypotheses.Instances         S using (_⊨_; ⊨⇒⊩ᴴ)
open import PolymorphicCalculus.Typing                       S
open import PolymorphicCalculus.Typing.Erasure               S
open import PolymorphicCalculus.Typing.GradeSubstitution     S
open import PolymorphicCalculus.Typing.ScopeClosed           S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S
open import PolymorphicCalculus.Syntax.Run                   S

scope-instantiationᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {X : OVType Θ} {δ : Subst Θ ∅ˢ}
               → (V : Q ∣ Γ ⊢V⦂ X) → δ ⊨ Q
               → Γ [ δ ]ᶜᵗˣ ⊢ᵛ eraseᵛ (⌊ V ⌋ᵛ [ δ ]ᴿᵛ) ⦂ X [ δ ]ᵛ
scope-instantiationᵛ {δ = δ} V h = substᵛ δ (⊨⇒⊩ᴴ h) V , cong eraseᵛ (⌊substᵛ⌋ δ (⊨⇒⊩ᴴ h) V)

scope-instantiation : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {δ : Subst Θ ∅ˢ}
              → (M : Q ∣ Γ ⊢C⦂ C) → δ ⊨ Q
              → Γ [ δ ]ᶜᵗˣ ⊢ᶜ eraseᶜ (⌊ M ⌋ᶜ [ δ ]ᴿᶜ) ⦂ C [ δ ]ᶜ
scope-instantiation {δ = δ} M h = substᶜ δ (⊨⇒⊩ᴴ h) M , cong eraseᶜ (⌊substᶜ⌋ δ (⊨⇒⊩ᴴ h) M)
