------------------------------------------------------------------
-- Instantiation of the scope                                   --
--                                                              --
-- A typing under `Q` is a family of typings over the empty     --
-- scope under the truths: at every closed instance `δ ⊨ Q`,    --
-- the run-time erasure of the instantiated term, its           --
-- annotations dropped, is typed at the instantiated context,   --
-- which keeps its program context, and type                    --
-- (`scope-instantiation`). Handler clauses stay typed at their --
-- own grade variables: a quantified hypothesis, holding at     --
-- every grade, is one of the truths.                           --
------------------------------------------------------------------

open import Data.List.Base using ([])
open import Data.Product using (_,_)

open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.Instantiation (S : LanguageSpec) where

open import OpenCalculus.Syntax.Types             S
open import OpenCalculus.Syntax.Contexts          S
open import OpenCalculus.Syntax.Subst             S
open import OpenCalculus.Hypotheses               S
open import OpenCalculus.Hypotheses.Instances     S using (_⊨_; ⊨⇒⊩ᴴ)
open import OpenCalculus.Typing                   S
open import OpenCalculus.Typing.Erasure           S
open import OpenCalculus.Typing.GradeSubstitution S
open import OpenCalculus.Typing.ScopeClosed       S
open import OpenCalculus.Syntax.Raw.Subst         S
open import OpenCalculus.Syntax.Run               S

scope-instantiationᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {X : OVType Θ} {δ : Subst Θ ∅ˢ}
               → (V : Q ∣ Γ ⊢V⦂ X) → δ ⊨ Q
               → Γ [ δ ]ᶜᵗˣ ⊢ᵛ eraseᵛ (⌊ V ⌋ᵛ [ δ ]ᴿᵛ) ⦂ X [ δ ]ᵛ
scope-instantiationᵛ {δ = δ} V h = substᵛ δ (⊨⇒⊩ᴴ h) V , cong eraseᵛ (⌊substᵛ⌋ δ (⊨⇒⊩ᴴ h) V)

scope-instantiation : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {δ : Subst Θ ∅ˢ}
              → (M : Q ∣ Γ ⊢C⦂ C) → δ ⊨ Q
              → Γ [ δ ]ᶜᵗˣ ⊢ᶜ eraseᶜ (⌊ M ⌋ᶜ [ δ ]ᴿᶜ) ⦂ C [ δ ]ᶜ
scope-instantiation {δ = δ} M h = substᶜ δ (⊨⇒⊩ᴴ h) M , cong eraseᶜ (⌊substᶜ⌋ δ (⊨⇒⊩ᴴ h) M)
