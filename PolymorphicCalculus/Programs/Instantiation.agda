------------------------------------------------------------------
-- Instantiation, and the corollary for programs                --
--                                                              --
-- In a program `P` typed at the program context of `Γ`, at     --
-- every closed instance `δ ⊨ Q`, a typing under `Q` gives a    --
-- scope-closed typing of the erasure of the instantiated term, --
-- the definitions of `P` substituted, at the instance of `Γ`   --
-- without its program context (`instantiation`). A term typed  --
-- in a program context is then typed in the empty state, and   --
-- halts (`programs`).                                          --
------------------------------------------------------------------

open import Data.Product using (_×_; _,_)

open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Programs.Instantiation (S : LanguageSpec) where

open import PolymorphicCalculus.Syntax.Types                     S
open import PolymorphicCalculus.Syntax.Contexts                  S
open import PolymorphicCalculus.Syntax.GradeSubstitution         S
open import PolymorphicCalculus.Hypotheses                       S
open import PolymorphicCalculus.Hypotheses.Instances             S using (_⊨_; ⊨⇒⊩ᴴ)
open import PolymorphicCalculus.Typing                           S
open import PolymorphicCalculus.Typing.Erasure                   S
open import PolymorphicCalculus.Typing.Transport                 S
open import PolymorphicCalculus.Typing.GradeSubstitution         S
open import PolymorphicCalculus.Typing.ScopeClosed               S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution     S
open import PolymorphicCalculus.Syntax.Run                       S
open import PolymorphicCalculus.OperationalSemantics.State       S using (∅; toCtx)
open import PolymorphicCalculus.OperationalSemantics.Termination S using (Halts; termination)
open import PolymorphicCalculus.Programs.Syntax                  S
open import PolymorphicCalculus.Programs.Substitution            S
open import PolymorphicCalculus.Programs.Typing                  S

------------------------------------------------------------------------
-- Instantiation: at a closed instance `δ ⊨ Q`, a typing under `Q` in a
-- typed program gives a scope-closed typing of the erasure of the
-- instantiated term, the definitions substituted

instantiationᵛ : ∀ {Θ n P} {Q : Hyps Θ} {Γ : OCtx Θ n} {X : OVType Θ} {δ : Subst Θ ∅ˢ}
               → ⊢ᴾ P ⦂ defs Γ → (V : Q ∣ Γ ⊢ᵛ⦂ X) → δ ⊨ Q
               → local Γ [ δ ]ᶜᵗˣ ⊢ᵛ ⌊ ⌊ V ⌋ᵛ [ δ ]ᴿᵛ ⌋ᴾᵛ P ⦂ X [ δ ]ᵛ
instantiationᵛ {P = P} {δ = δ} t V h =
  substᵛ δ (⊨⇒⊩ᴴ h) V' ,
  trans (cong eraseᵛ (⌊substᵛ⌋ δ (⊨⇒⊩ᴴ h) V'))
    (trans (erase-substᵛ ⌊ V' ⌋ᵛ δ)
      (trans (∥sdef-v∥ (programEnv t) V)
             (cong (_[ ⟦ P ⟧ᴾ ]ᵈᵛ) (sym (erase-substᵛ ⌊ V ⌋ᵛ δ)))))
  where V' = sdef-v (programEnv t) V

instantiation : ∀ {Θ n P} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {δ : Subst Θ ∅ˢ}
              → ⊢ᴾ P ⦂ defs Γ → (M : Q ∣ Γ ⊢ᶜ⦂ C) → δ ⊨ Q
              → local Γ [ δ ]ᶜᵗˣ ⊢ᶜ ⌊ ⌊ M ⌋ᶜ [ δ ]ᴿᶜ ⌋ᴾᶜ P ⦂ C [ δ ]ᶜ
instantiation {P = P} {δ = δ} t M h =
  substᶜ δ (⊨⇒⊩ᴴ h) M' ,
  trans (cong eraseᶜ (⌊substᶜ⌋ δ (⊨⇒⊩ᴴ h) M'))
    (trans (erase-substᶜ ⌊ M' ⌋ᶜ δ)
      (trans (∥sdef-c∥ (programEnv t) M)
             (cong (_[ ⟦ P ⟧ᴾ ]ᵈᶜ) (sym (erase-substᶜ ⌊ M ⌋ᶜ δ)))))
  where M' = sdef-c (programEnv t) M

------------------------------------------------------------------------
-- A term typed in the program context of a typed program is typed in the
-- empty state at every closed instance, and halts

programs : ∀ {Θ P Δ} {Q : Hyps Θ} {C : OCType Θ} {δ : Subst Θ ∅ˢ}
         → ⊢ᴾ P ⦂ Δ → (M : Q ∣ ⌜ Δ ⌝ᵖ ⊢ᶜ⦂ C) → δ ⊨ Q
         → toCtx ∅ ⊢ᶜ ⌊ ⌊ M ⌋ᶜ [ δ ]ᴿᶜ ⌋ᴾᶜ P ⦂ C [ δ ]ᶜ
           × Halts ∅ (⌊ ⌊ M ⌋ᶜ [ δ ]ᴿᶜ ⌋ᴾᶜ P)
programs {P = P} {Δ = Δ} {C = C} {δ = δ} t M h = typed , termination typed
  where
    typed : toCtx ∅ ⊢ᶜ ⌊ ⌊ M ⌋ᶜ [ δ ]ᴿᶜ ⌋ᴾᶜ P ⦂ C [ δ ]ᶜ
    typed = subst (λ Γ → Γ ⊢ᶜ ⌊ ⌊ M ⌋ᶜ [ δ ]ᴿᶜ ⌋ᴾᶜ P ⦂ C [ δ ]ᶜ)
                  (cong (_[ δ ]ᶜᵗˣ) (local-⌜⌝ Δ))
                  (instantiation (subst (⊢ᴾ _ ⦂_) (sym (defs-⌜⌝ Δ)) t) M h)
