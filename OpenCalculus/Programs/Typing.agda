------------------------------------------------------------------
-- The program judgement                                        --
--                                                              --
-- `⊢ᴾ P ⦂ Δ`: each definition `f = V` of the program `P` is    --
-- typable in the program context of the definitions before it, --
-- and `Δ` binds it to the principal type scheme of `V` there.  --
-- The definitions of a typed program have closed typings at    --
-- their schemes (`programEnv`).                                   --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (just)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (<⇒≢)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Programs.Typing (S : LanguageSpec) where

open import OpenCalculus.Syntax.Types            S
open import OpenCalculus.Syntax.Contexts         S
open import OpenCalculus.Syntax.Subst            S
open import OpenCalculus.Hypotheses              S
open import OpenCalculus.Hypotheses.Instances    S using (Satisfiable)
open import OpenCalculus.Typing                  S
open import OpenCalculus.Typing.Erasure          S
open import OpenCalculus.Typing.Transport        S
open import OpenCalculus.Typing.Renaming         S using (∥_∥ᵛ)
open import OpenCalculus.Syntax.Raw              S using (RawV)
open import OpenCalculus.Syntax.Run              S using (eraseᵛ; erase-substᵛ)
open import OpenCalculus.Inference.Principality  S
  using (PrincipalSchemeᵛ; module PrincipalSchemeᵛ)
open import OpenCalculus.Programs.Syntax         S
open import OpenCalculus.Programs.Substitution   S

open PrincipalSchemeᵛ

------------------------------------------------------------------------
-- The judgement

-- An accepted definition: a principal type scheme of the value in the
-- program context before it, with satisfiable hypotheses

record Accepted (Δ : PCtx) (V : RawV ∅ˢ 0) : Set where
  constructor accepted
  field
    principal : PrincipalSchemeᵛ Δ V
    typable   : Satisfiable (Q̃ principal)

open Accepted public

-- The scheme it adds to the program context

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

-- A definition's value, typed at its scheme in the program context
-- before it, the earlier definitions substituted, in the empty context

closedDef : ∀ {P Δ V} → DefsEnv ⟦ P ⟧ᴾ Δ → (a : Accepted Δ V)
          → Σ[ D ∈ (Q̃ (principal a) ∣ [] ⊢V⦂ X̃ (principal a)) ]
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
    D₀ = instantiate p idˢ (Q̃ p) ⊩ᴴ-refl
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
