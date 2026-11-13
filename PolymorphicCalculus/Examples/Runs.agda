------------------------------------------------------------------------
-- Satisfiability at definitions and establishment at runs            --
--                                                                    --
-- Some programs leave hypotheses that inference cannot settle on     --
-- its own. Inference (`infer`) searches them for a refutation;       --
-- checking a closed program (`check`) also searches for a closed     --
-- instance that satisfies them, which establishes the program as     --
-- typable.                                                           --
--                                                                    --
-- The examples                                                       --
--   deadline τ c   a function annotated to take as long as its       --
--                  argument and a delay `τ`, the whole annotated at  --
--                  `c`; at a duration (`deadline-at`) and at the     --
--                  top (`deadline-top`)                              --
--   stretch τ      a handler calling the result of its resumption    --
--                                                                    --
-- How to read them                                                   --
--   Each program is written above its definition in ordinary         --
--   syntax. The modules under `Runs/` check the verdicts with        --
--   `refl` at upper and lower bounds:                                --
--     deadline-top-verdict : verdict (check [] (deadline-top 1))     --
--                              ≡ established                         --
--   An established verdict is read back as a typing                  --
--   (`check-typable`); an `untypable` verdict from `infer` gives a   --
--   proof that the program is untypable. A deadline is established   --
--   at the top and refuted at the durations tried, at both grades;   --
--   `stretch` is refuted at upper bounds and established at lower    --
--   bounds.                                                          --
------------------------------------------------------------------------

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
open GradeSystemInterface Grades using (𝔻; ιₑ; ⊤ₑ)
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
⌜ τ ⌝ᵉ = econst (ιₑ τ)

------------------------------------------------------------------
-- 1. A function annotated to take as long as its argument and `τ`
--
--   deadline τ c = (let f = (λ g. g (); delay τ) : (U → U ! ε₀) → U ! ε₀
--                   in f (λ _. ())) : U ! c
--
-- Where the unit is least it needs `ε₀ · τ ≾ ε₀ ∧ ε₀ ≾ c`. This fails
-- if `τ` is not below `c`; otherwise, for a positive `τ`, the least
-- `ε₀` it allows is the top, so it fails unless `c` is the top. At
-- lower bounds on time the condition `𝟏 ≾ ε₀` refutes every `c` but
-- the top.

-- The scope of the program's variables: one effect variable

Θ₁ : Scope
Θ₁ = scope 0 0 1

ε̂₀ : EExp Θ₁
ε̂₀ = evar fzero

deadline : 𝔻 → EExp Θ₁ → RawC Θ₁ 0
deadline τ c =
  (return (fun ((v₀ · ⋆) ⨟ delay τ (return ⋆))
             ⦂ᵛ ((unit ⇒ unit ! ε̂₀) ⇒ unit ! ε̂₀))
   ⨟ (v₀ · fun (return ⋆)))
  ⦂ᶜ (unit ! c)

-- annotated at the grade of a duration, and at the top

deadline-at : 𝔻 → 𝔻 → RawC Θ₁ 0
deadline-at τ c = deadline τ ⌜ c ⌝ᵉ

deadline-top : 𝔻 → RawC Θ₁ 0
deadline-top τ = deadline τ (econst ⊤ₑ)

------------------------------------------------------------------
-- 2. A handler calling the result of its resumption
--
--   stretch τ = handle () with handler {
--                 op p k ↦ let a = op p in unbox k as k' in
--                          let f = k' a in f (); (λ _. delay τ);
--                 return x ↦ λ _. delay τ}
--
-- Each clause needs `∀ j. op · j · ε ≾ op · j` over its grade variable
-- `j`, with `ε` the delay `τ`: a candidate `j` refutes it at
-- upper bounds on time, and it is established at lower bounds on time.

late : ∀ {Θ n} → 𝔻 → RawV Θ n
late τ = fun (delay τ (return ⋆))

call-result : ∀ {Θ n} → 𝔻 → Op → RawC (Θ +e) (suc (suc n))
call-result τ op =
  perform op v₁ (unbox (var (fsuc fzero)) ((v₀ · v₁) ⨟ ((v₀ · ⋆) ⨟ return (late τ))))

stretch : 𝔻 → RawC ∅ˢ 0
stretch τ = handle (return ⋆) `with handler (return (late τ)) (call-result τ)
