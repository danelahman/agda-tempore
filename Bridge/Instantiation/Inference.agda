------------------------------------------------------------------
-- Inference yields declarative typings                         --
--                                                              --
-- For a term whose handlers are second-class, inference yields --
-- a family of declarative typings, one per instance satisfying --
-- the scheme: a typed verdict's principal                      --
-- scheme `∀ Θ̃. Q̃ ∧ R̃ ⇒ X̃` gives, for every declarative         --
-- instance `σ` of `Θ̃` with `σ ⊨ᴰ Q̃` and the obligations `R̃`    --
-- met at `⌜ σ ⌝ˢ`, a declarative typing                        --
-- `⟦ Γ [ σ̃ ]ᶜᵗˣ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ X̃ ⟧ᶜ σ` of the term at the       --
-- instance `σ̃ ⨟ᴰ σ` of its variables, box grades evaluated    --
-- there (`infer-instantiate`); so does an established check,   --
-- through its scheme alone (`check-instantiate`). No instance  --
-- is chosen.                                                   --
--                                                              --
-- The obligations are met in the open entailment, their rigids --
-- kept as variables, which is what the scheme's instantiation  --
-- consumes; it implies their declarative reading `σ ⊨ᴰᴿ R̃`     --
-- (`⊩ᴼˢ→⊨ᴰᴿ`), not conversely.                                 --
--                                                              --
-- A checked program in the empty context is, at each such      --
-- instance, a closed program of that term, and it halts        --
-- (`check-program`, by `Adequacy.Normalization.halts`); its    --
-- denotation in any model is that of the closed program, to    --
-- which operational soundness and adequacy apply as stated.    --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_; _,_)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module Bridge.Instantiation.Inference (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types                 S
open import ClosedCalculus.Syntax.Contexts S using ([])
open import ClosedCalculus.Syntax.Terms    S
import ClosedCalculus.Syntax.Erasure S as CE

open import ClosedCalculus.OperationalSemantics.State               S using (∅)
open import ClosedCalculus.OperationalSemantics.PreservationTheorem S using (⟨_,_⟩)
open import ClosedCalculus.Adequacy.Evaluation                      S using (Halts)
open import ClosedCalculus.Adequacy.Normalization                   S using (halts)

open import OpenCalculus.Syntax.Types           S using (OCType)
open import OpenCalculus.Syntax.Contexts        S using (OCtx; [])
open import OpenCalculus.Syntax.Subst           S
open import OpenCalculus.Hypotheses             S using (∅ᴴ)
open import OpenCalculus.Hypotheses.Instances   S using (Satisfiable; _⊩ᴼˢ_[_])
open import OpenCalculus.Syntax.Raw             S using (RawC; SecondClassᶜ)
open import OpenCalculus.Syntax.Raw.Subst       S using (secondClass-[]ᴿᶜ)
import OpenCalculus.Typing.Erasure S as OE
open import OpenCalculus.Inference.Principality S
  using (PrincipalScheme; module PrincipalScheme; typed; established)
open import OpenCalculus.Inference.SolverImpl           S opEnum using (infer; check)

open import Bridge.Instantiation.Types          S
open import Bridge.Instantiation.Judgements     S
open import Bridge.Instantiation.Correspondence S
open import Bridge.Instantiation.Terms          S

open PrincipalScheme

-- A principal type scheme of a term whose handlers are second-class is
-- a family of declarative typings of its term, one per instance
-- satisfying the scheme. The hypotheses are read
-- declaratively; the obligations, whose rigids stay variables, in the
-- open entailment at the constant instance `⌜ σ ⌝ˢ`, which gives their
-- declarative reading (`⊩ᴼˢ→⊨ᴰᴿ`).

scheme-instantiate : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n}
                   → (p : PrincipalScheme Γ M) → SecondClassᶜ M
                   → (σ : DInst (Θ̃ p)) → σ ⊨ᴰ Q̃ p → ∅ᴴ ⊩ᴼˢ R̃ p [ ⌜ σ ⌝ˢ ]
                   → Σ[ D ∈ ⟦ Γ [ σ̃ p ]ᶜᵗˣ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ X̃ p ⟧ᶜ σ ] (CE.⌊ D ⌋ᶜ ≡ ⌊ M ⌋ᴿᶜ (σ̃ p ⨟ᴰ σ))
scheme-instantiate {Γ = Γ} {M} p c σ s r
  with ⌜⌝ˢ-⊨ s
... | h , _
  with instantiate p ⌜ σ ⌝ˢ ∅ᴴ (h , r)
... | D , e
  with instantiateᶜ ∅ᴰ ⊨ᴰ-∅ D (subst SecondClassᶜ (sym e) (secondClass-[]ᴿᶜ M c))
... | D' , e' =
  castᶜ pΓ pC D' ,
  trans (castᶜ-⌊⌋ pΓ pC D')
    (trans e' (trans (cong (λ X → ⌊ X ⌋ᴿᶜ ∅ᴰ) e)
                     (trans (⌊[]⌋ᴿᶜ M (σ̃ p ⨟ˢ δ) ∅ᴰ) (⌊≗⌋ᴿᶜ pσ M))))
  where
    δ = ⌜ σ ⌝ˢ

    pΓ : ⌞ Γ [ σ̃ p ⨟ˢ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ≡ ⟦ Γ [ σ̃ p ]ᶜᵗˣ ⟧ᶜᵗˣ σ
    pΓ = trans (cong ⌞_⌟ᶜᵗˣ (sym ([⨟]ᶜᵗˣ Γ (σ̃ p) δ)))
               (trans (⌞[]⌟ᶜᵗˣ δ (Γ [ σ̃ p ]ᶜᵗˣ)) (⟦≗⟧ᶜᵗˣ ⌞⌜ σ ⌝ˢ⌟ (Γ [ σ̃ p ]ᶜᵗˣ)))

    pC : ⌞ X̃ p [ δ ]ᶜ ⌟ᶜ ≡ ⟦ X̃ p ⟧ᶜ σ
    pC = trans (⌞[]⌟ᶜ δ (X̃ p)) (⟦≗⟧ᶜ ⌞⌜ σ ⌝ˢ⌟ (X̃ p))

    pσ : ((σ̃ p ⨟ˢ δ) ⨟ᴰ ∅ᴰ) ≗ᴰ (σ̃ p ⨟ᴰ σ)
    pσ = ≗ᴰ-trans (⨟ˢ-⨟ᴰ (σ̃ p) δ ∅ᴰ) (⨟ᴰ-≗ (σ̃ p) ⌞⌜ σ ⌝ˢ⌟)

-- Inference: a typed verdict is a family of declarative typings, one
-- per instance satisfying its scheme

infer-instantiate : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
                  → infer Γ M ≡ typed p → SecondClassᶜ M
                  → (σ : DInst (Θ̃ p)) → σ ⊨ᴰ Q̃ p → ∅ᴴ ⊩ᴼˢ R̃ p [ ⌜ σ ⌝ˢ ]
                  → Σ[ D ∈ ⟦ Γ [ σ̃ p ]ᶜᵗˣ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ X̃ p ⟧ᶜ σ ] (CE.⌊ D ⌋ᶜ ≡ ⌊ M ⌋ᴿᶜ (σ̃ p ⨟ᴰ σ))
infer-instantiate Γ M {p} _ = scheme-instantiate p

-- Checking: the same from an established check, through its scheme
-- alone; the instance the check establishes is not used

check-instantiate : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                  → {p : PrincipalScheme Γ M} → {e : Satisfiable (Q̃ p) (R̃ p)}
                  → check Γ M ≡ established p e → SecondClassᶜ M
                  → (σ : DInst (Θ̃ p)) → σ ⊨ᴰ Q̃ p → ∅ᴴ ⊩ᴼˢ R̃ p [ ⌜ σ ⌝ˢ ]
                  → Σ[ D ∈ ⟦ Γ [ σ̃ p ]ᶜᵗˣ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ X̃ p ⟧ᶜ σ ] (CE.⌊ D ⌋ᶜ ≡ ⌊ M ⌋ᴿᶜ (σ̃ p ⨟ᴰ σ))
check-instantiate Γ M {p} _ = scheme-instantiate p

-- A program with second-class handlers, checked in the empty context,
-- is at every instance
-- satisfying its scheme a closed program of the term there, and it halts.
-- Its denotation in any model is that of this program, to which
-- operational soundness and adequacy apply as stated.

Halts∅ : (C : CType) → [] ⊢C⦂ C → Set
Halts∅ (A ‼ ε) P = Halts ⟨ ∅ , P ⟩

check-program : ∀ {Θ} → (M : RawC Θ 0)
              → {p : PrincipalScheme [] M} → {e : Satisfiable (Q̃ p) (R̃ p)}
              → check [] M ≡ established p e → SecondClassᶜ M
              → (σ : DInst (Θ̃ p)) → σ ⊨ᴰ Q̃ p → ∅ᴴ ⊩ᴼˢ R̃ p [ ⌜ σ ⌝ˢ ]
              → Σ[ P ∈ [] ⊢C⦂ ⟦ X̃ p ⟧ᶜ σ ] ((CE.⌊ P ⌋ᶜ ≡ ⌊ M ⌋ᴿᶜ (σ̃ p ⨟ᴰ σ)) × Halts∅ _ P)
check-program M {p} _ c σ s r with scheme-instantiate p c σ s r
... | P , e = P , e , halts∅ (⟦ X̃ p ⟧ᶜ σ) P
  where
    halts∅ : (C : CType) → (P : [] ⊢C⦂ C) → Halts∅ C P
    halts∅ (A ‼ ε) P = halts P
