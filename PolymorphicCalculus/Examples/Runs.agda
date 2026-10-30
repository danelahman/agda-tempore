--------------------------------------------------------------------
-- Satisfiability at definitions and establishment at runs        --
--                                                                --
-- Programs whose qualifier inference leaves open: `infer`        --
-- searches it for a refutation (`Search`), and `check` also for  --
-- a closed instance. The instances under `Runs/` check the       --
-- verdicts by `refl` and derive typability or its refutation.    --
--------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (suc)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Runs (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (𝔻; of-durᵉ; ⊤ₑ)
open Operations Ops using (Op)

open import PolymorphicCalculus.Syntax.Grades S
open import PolymorphicCalculus.Syntax.Types  S
open import PolymorphicCalculus.Syntax.Raw    S

open import PolymorphicCalculus.Syntax.Contexts  S using (OCtx)
open import PolymorphicCalculus.Inference.Principality         S using (Check; established; unestablished; Typable)
open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer; check; check-established) public
open import PolymorphicCalculus.Examples.Scheme S public
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- The verdict of a check, its evidence dropped

data Verdict : Set where
  established untypable unestablished stuck : Verdict

verdict : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → Check Γ M → Verdict
verdict (established _ _)  = established
verdict Check.untypable    = untypable
verdict (unestablished _)  = unestablished
verdict Check.stuck        = stuck

-- An established verdict, read back as a typing (`check-established`)

check-typable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
              → verdict (check Γ M) ≡ established → Typable Γ M
check-typable Γ M v with check Γ M in e
check-typable Γ M v  | established p s = check-established Γ M e
check-typable Γ M () | Check.untypable
check-typable Γ M () | unestablished _
check-typable Γ M () | Check.stuck

------------------------------------------------------------------
-- The grade of a duration

⌜_⌝ᵉ : ∀ {Θ} → 𝔻 → EExp Θ
⌜ τ ⌝ᵉ = econst (of-durᵉ τ)

------------------------------------------------------------------
-- 1. A function annotated to take as long as its argument and `τ`
--
--   budget τ c = (let f = (λ g. g (); delay τ) : (U → U ! ε₀) → U ! ε₀
--                 in f (λ _. ())) : U ! c
--
-- Where the unit is least this leaves `τ · ε₀ ≾ ε₀ ∧ ε₀ ≾ c`: refuted
-- through the factor edge if `τ` is not below `c`, else by lowering
-- `ε₀` to the top unless `c` is the top. At left-sided time `u ≾ ε₀`
-- refutes every `c` but the top.

-- The scope of the program's variables: one effect variable

Θ₁ : Scope
Θ₁ = scope 0 0 1

ε̂₀ : EExp Θ₁
ε̂₀ = evar fzero

budget : 𝔻 → EExp Θ₁ → RawC Θ₁ 0
budget τ c =
  (return (lam ((v₀ · ⋆) ⨟ delay τ (return ⋆))
             ⦂ᵛ ((Unit ⇒ Unit ‼ ε̂₀) ⇒ Unit ‼ ε̂₀))
   ⨟ (v₀ · lam (return ⋆)))
  ⦂ᶜ (Unit ‼ c)

-- annotated at the grade of a duration, and at the top

budget-at : 𝔻 → 𝔻 → RawC Θ₁ 0
budget-at τ c = budget τ ⌜ c ⌝ᵉ

budget-top : 𝔻 → RawC Θ₁ 0
budget-top τ = budget τ (econst ⊤ₑ)

------------------------------------------------------------------
-- 2. A handler calling the result of its resumption
--
--   stretch τ = handle () with handler {
--                 op p k ↦ let a = op p in unbox k as k' in
--                          let f = k' a in f (); (λ _. delay τ);
--                 return x ↦ λ _. delay τ}
--
-- Each clause leaves `∀ j. op · j · ε ≾ op · j`, `ε` localised to `τ`:
-- refuted at a witness at right-sided time, established at left-sided.

late : ∀ {Θ n} → 𝔻 → RawV Θ n
late τ = lam (delay τ (return ⋆))

call-result : ∀ {Θ n} → 𝔻 → Op → RawC (Θ +e) (suc (suc n))
call-result τ op =
  perform op v₁ (unbox (var (fsuc fzero)) ((v₀ · v₁) ⨟ ((v₀ · ⋆) ⨟ return (late τ))))

stretch : 𝔻 → RawC ∅ˢ 0
stretch τ = handle (return ⋆) `with handler (return (late τ)) (call-result τ)
