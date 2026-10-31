------------------------------------------------------------------
-- The program judgement                                        --
--                                                              --
-- `⊢ᴾ P ⦂ Δ`: each definition `f = V` of `P` is typable in the --
-- program context of those before it, and `Δ` binds it to the  --
-- principal type scheme of `V` there. The definitions of a     --
-- typed program have closed typings at their schemes           --
-- (`programEnv`); in its program context a value of box type   --
-- is a resource value (`program-resource-value`).              --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (just)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (<⇒≢)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Programs.Typing (S : LanguageSpec) where

open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.Contexts          S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S
open import PolymorphicCalculus.Hypotheses.Instances     S using (Satisfiable)
open import PolymorphicCalculus.Typing                   S
open import PolymorphicCalculus.Typing.Erasure           S
open import PolymorphicCalculus.Typing.Transport         S
open import PolymorphicCalculus.Typing.Renaming          S using (∥_∥ᵛ)
open import PolymorphicCalculus.Typing.Resources         S
open import PolymorphicCalculus.Syntax.Raw               S using (RawV)
open import PolymorphicCalculus.Syntax.Run               S using (eraseᵛ; erase-substᵛ)
open import PolymorphicCalculus.Inference.Principality   S
  using (PrincipalSchemeᵛ; module PrincipalSchemeᵛ)
open import PolymorphicCalculus.Programs.Syntax         S
open import PolymorphicCalculus.Programs.Substitution   S

open PrincipalSchemeᵛ

------------------------------------------------------------------------
-- The judgement

-- An accepted definition: a principal scheme with satisfiable hypotheses

record Accepted (Δ : PCtx) (V : RawV ∅ˢ 0) : Set where
  constructor accepted
  field
    principal : PrincipalSchemeᵛ Δ V
    typable   : Satisfiable (Q̃ principal)

open Accepted public

schemeᴬ : ∀ {Δ V} → Accepted Δ V → Scheme
schemeᴬ a = ∀ˢ (Θ̃ (principal a)) (Q̃ (principal a)) (X̃ (principal a))

infix 4 ⊢ᴾ_⦂_

data ⊢ᴾ_⦂_ : Program → PCtx → Set where
  ∅ᴾ   : ⊢ᴾ ∅ᴾ ⦂ ∅ᵖ
  _∷ᴾ_ : ∀ {P Δ V} → ⊢ᴾ P ⦂ Δ → (a : Accepted Δ V) → ⊢ᴾ P ∷ᴾ V ⦂ Δ ∷ᵖ schemeᴬ a

------------------------------------------------------------------------
-- The definitions of a typed program

lenᴾ-⊢ : ∀ {P Δ} → ⊢ᴾ P ⦂ Δ → lenᴾ P ≡ len Δ
lenᴾ-⊢ ∅ᴾ       = refl
lenᴾ-⊢ (t ∷ᴾ a) = cong suc (lenᴾ-⊢ t)

-- A definition's value, earlier definitions substituted, typed at its
-- scheme in the empty context

closedDef : ∀ {P Δ V} → DefsEnv ⟦ P ⟧ᴾ Δ → (a : Accepted Δ V)
          → Σ[ D ∈ (Q̃ (principal a) ∣ [] ⊢ᵛ⦂ X̃ (principal a)) ]
              (∥ D ∥ᵛ ≡ eraseᵛ V [ ⟦ P ⟧ᴾ ]ᵈᵛ)
closedDef {P} {Δ} {V} r a =
  ctx-castᵛ (local-⌜⌝ Δ) (sdef-v r' D₁) ,
  trans (cong eraseᵛ (⌊ctx-castᵛ⌋ (local-⌜⌝ Δ) _))
    (trans (∥sdef-v∥ r' D₁)
      (cong (_[ ⟦ P ⟧ᴾ ]ᵈᵛ)
        (trans (cong eraseᵛ (trans (⌊ty-subst⌋ ([id]ᵛ (X̃ p)) _) (proj₂ D₀)))
               (erase-substᵛ V from∅))))
  where
    p  = principal a
    D₀ = sound p idˢ (Q̃ p) ⊩ᴴ-refl
    D₁ = ty-subst ([id]ᵛ (X̃ p)) (proj₁ D₀)
    r' = subst (DefsEnv ⟦ P ⟧ᴾ) (sym (defs-⌜⌝ Δ)) r

programEnv : ∀ {P Δ} → ⊢ᴾ P ⦂ Δ → DefsEnv ⟦ P ⟧ᴾ Δ
closed (programEnv ∅ᴾ) ()
closed (programEnv (_∷ᴾ_ {P} {Δ} {V} t a)) here =
  proj₁ c , trans (⟦∷⟧-here P V (sym (lenᴾ-⊢ t))) (cong just (sym (proj₂ c)))
  where c = closedDef {P = P} (programEnv t) a
closed (programEnv (_∷ᴾ_ {P} {Δ} {V} t a)) (there m) =
  proj₁ c , trans (⟦∷⟧-there P V (λ e → <⇒≢ (∈ᵖ-< m) (trans e (lenᴾ-⊢ t)))) (proj₂ c)
  where c = closed (programEnv t) m

------------------------------------------------------------------------
-- Resource values

-- The schemes of a typed program have non-resource types

program-nonResource : ∀ {P Δ} → ⊢ᴾ P ⦂ Δ → NonResourceDefs Δ
program-nonResource (_∷ᴾ_ {Δ = Δ} t a) here =
  subst NonResource ([id]ᵛ (X̃ p))
        (nonResource-closed (subst NonResourceDefs (sym (defs-⌜⌝ Δ)) (program-nonResource t))
                            (proj₁ (sound p idˢ (Q̃ p) ⊩ᴴ-refl)))
  where p = principal a
program-nonResource (t ∷ᴾ a) (there m) = program-nonResource t m

program-resource-value : ∀ {P Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ'' X''}
                       → ⊢ᴾ P ⦂ defs Γ → (V : Q ∣ Γ ⊢ᵛ⦂ [ ρ'' ] X'')
                       → ResourceValue Q Γ ρ'' X'' ⌊ V ⌋ᵛ
program-resource-value t V = resource-value (program-nonResource t) V
