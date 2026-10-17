------------------------------------------------------------------
-- Inferred programs are typed in the closed calculus           --
--                                                              --
-- A typable raw term has, at a closed instance of its          --
-- variables, a closed typing of the same term                  --
-- (`closed-typing`), so a typed verdict with a satisfiable     --
-- scheme and an established check each give one. A closed      --
-- context embeds in the open calculus (`⌜_⌝ᶜᵗˣ`), and there    --
-- the typing is in that context itself (`check-closed-ctx`).   --
-- An established program in the empty context is thus a        --
-- program of the closed calculus, and it halts                 --
-- (`check-program`, by `Adequacy.Normalization.halts`); its    --
-- denotation in any model is that of the closed typing, to     --
-- which operational soundness and adequacy apply as stated.    --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Function.Bundles using (Equivalence)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module Bridge.Inference (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types    S
open import Syntax.Contexts S using (Ctx; [])
open import Syntax.Language S
import Syntax.Erasure S as CE

open import OperationalSemantics.State                    S using (∅)
open import OperationalSemantics.PreservationTheorem      S using (⟨_,_⟩)
open import OperationalSemantics.Adequacy.Evaluation      S using (Prog; Halts)
open import OperationalSemantics.Adequacy.Normalization   S using (halts)

open import TypeInference.OpenSyntax.Types     S using (OCType)
open import TypeInference.OpenSyntax.Contexts  S using (OCtx)
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.Raw.Syntax           S using (RawC)
open import TypeInference.Principality         S
  using (PrincipalScheme; Typable; typable; typable-⇔; established; typed)
open import TypeInference.OpenSyntax.Instances S using (Satisfiable)
open import TypeInference.SolverImpl           S opEnum using (infer; check; check-established)

open import Bridge.Types S
open import Bridge.Terms S

-- A closed typing of a raw term in a closed context

ClosedTyping : Ctx → CE.ErC → Set
ClosedTyping Γ M = Σ[ C ∈ CType ] Σ[ D ∈ Γ ⊢C⦂ C ] (CE.⌊ D ⌋ᶜ ≡ M)

-- A typable term has a closed typing at a closed instance of the
-- variables of its context

closed-typing : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n}
              → Typable Γ M
              → Σ[ δ ∈ Subst Θ ∅ˢ ] ClosedTyping ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⌊ M ⌋ᴿᶜ
closed-typing {Γ = Γ} {M} (typable Θ₀ σ₀ Q₀ C₀ D₀ e (δ₀ , s)) with bridge δ₀ s D₀
... | D' , e' =
  σ₀ ⨟ˢ δ₀ , ⌞ C₀ [ δ₀ ]ᶜ ⌟ᶜ , castᶜ p refl D' ,
  trans (castᶜ-⌊⌋ p refl D') (trans e' (trans (cong ⌊_⌋ᴿᶜ e) (⌊[]⌋ᴿᶜ M σ₀)))
  where
    p = cong ⌞_⌟ᶜᵗˣ ([⨟]ᶜᵗˣ Γ σ₀ δ₀)

-- A typed verdict whose scheme is satisfiable, and an established check

infer-closed : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
             → infer Γ M ≡ typed p
             → Satisfiable (PrincipalScheme.Q̃ p) (PrincipalScheme.R̃ p)
             → Σ[ δ ∈ Subst Θ ∅ˢ ] ClosedTyping ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⌊ M ⌋ᴿᶜ
infer-closed Γ M {p} _ s = closed-typing (Equivalence.from (typable-⇔ p) s)

check-closed : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
             → {p : PrincipalScheme Γ M}
             → {s : Satisfiable (PrincipalScheme.Q̃ p) (PrincipalScheme.R̃ p)}
             → check Γ M ≡ established p s
             → Σ[ δ ∈ Subst Θ ∅ˢ ] ClosedTyping ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⌊ M ⌋ᴿᶜ
check-closed Γ M eq = closed-typing (check-established Γ M eq)

-- In a closed context, the typing is in that context

closed-typing-ctx : (Γ : Ctx) → {M : RawC ∅ˢ ∣ Γ ∣ᶜ}
                  → Typable ⌜ Γ ⌝ᶜᵗˣ M → ClosedTyping Γ ⌊ M ⌋ᴿᶜ
closed-typing-ctx Γ t with closed-typing t
... | δ , C , D , e =
  C , castᶜ p refl D , trans (castᶜ-⌊⌋ p refl D) e
  where
    p = trans (cong ⌞_⌟ᶜᵗˣ (∅-[]ᶜᵗˣ δ ⌜ Γ ⌝ᶜᵗˣ)) ⌞⌜ Γ ⌝⌟ᶜᵗˣ

check-closed-ctx : (Γ : Ctx) → (M : RawC ∅ˢ ∣ Γ ∣ᶜ)
                 → {p : PrincipalScheme ⌜ Γ ⌝ᶜᵗˣ M}
                 → {s : Satisfiable (PrincipalScheme.Q̃ p) (PrincipalScheme.R̃ p)}
                 → check ⌜ Γ ⌝ᶜᵗˣ M ≡ established p s
                 → ClosedTyping Γ ⌊ M ⌋ᴿᶜ
check-closed-ctx Γ M eq = closed-typing-ctx Γ (check-established ⌜ Γ ⌝ᶜᵗˣ M eq)

-- An established program is a program of the closed calculus, and it halts

check-program : (M : RawC ∅ˢ 0)
              → {p : PrincipalScheme ⌜ [] ⌝ᶜᵗˣ M}
              → {s : Satisfiable (PrincipalScheme.Q̃ p) (PrincipalScheme.R̃ p)}
              → check ⌜ [] ⌝ᶜᵗˣ M ≡ established p s
              → Σ[ A ∈ VType ] Σ[ ε ∈ E ] Σ[ P ∈ Prog A ε ]
                  ((CE.⌊ P ⌋ᶜ ≡ ⌊ M ⌋ᴿᶜ) × Halts ⟨ ∅ , P ⟩)
check-program M eq with check-closed-ctx [] M eq
... | A ‼ ε , P , e = A , ε , P , e , halts P
