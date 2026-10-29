--------------------------------------------------------------------
-- Inference with durations that are not whole ticks              --
--                                                                --
-- Programs exercising `delay τ` at an arbitrary duration monoid, --
-- each taking its durations as arguments. None has an            --
-- annotation. A box is claimed after two consecutive delays: the --
-- premise of `unbox` compares the grade elapsed over both with   --
-- the box's grade, and inference decides it on the grade's       --
-- constants. Where the box's grade is inferred, the scheme asks  --
-- for a box at the grade of the two delays together.             --
--                                                                --
-- The instances under `Durations/` check the verdicts and        --
-- schemes by `refl` at dense time, with rational durations.      --
--------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Examples.Durations (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (𝔻; of-durʳ; of-durᵉ; _·ᵣ_; uᵣ; _≾ᵣ?_)
  renaming (_≾ᵣ_ to _≾ᴳ_)

open import OpenCalculus.Syntax.Grades          S
open import OpenCalculus.Syntax.Types           S
open import OpenCalculus.Syntax.Contexts        S
open import OpenCalculus.Syntax.Subst           S using (idˢ)
open import OpenCalculus.Hypotheses             S
open import OpenCalculus.Hypotheses.Instances   S using (Satisfiable-∅)
open import OpenCalculus.Typing                 S
open import OpenCalculus.Syntax.Raw             S
open import OpenCalculus.Syntax.Raw.Subst       S using (_[_]ᴿᶜ)
open import OpenCalculus.Typing.Erasure         S using (⌊_⌋ᶜ)
open import OpenCalculus.Inference.Principality S

open import OpenCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import OpenCalculus.Examples.Scheme S public
open import OpenCalculus.Examples.Variables

------------------------------------------------------------------
-- The grades of a duration

⌜_⌝ʳ : ∀ {Θ} → 𝔻 → RExp Θ
⌜ τ ⌝ʳ = rconst (of-durʳ τ)

⌜_⌝ᵉ : ∀ {Θ} → 𝔻 → EExp Θ
⌜ τ ⌝ᵉ = econst (of-durᵉ τ)

-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

------------------------------------------------------------------
-- 1. A box claimed after two delays
--
--   claim-after ρ τ τ' = box[ρ] () as x in delay τ; delay τ'; unbox x as y in y
--
-- The premise is `uᵣ · of-dur τ · of-dur τ' ≾ of-dur ρ`, decided on
-- the constants.

claim-after : 𝔻 → 𝔻 → 𝔻 → RawC ∅ˢ 0
claim-after ρ τ τ' = box ⌜ ρ ⌝ʳ ⋆ (delay τ (delay τ' (unbox fzero (return v₀))))

claim-after-D : ∀ ρ τ τ' → uᵣ ·ᵣ of-durʳ τ ·ᵣ of-durʳ τ' ≾ᴳ of-durʳ ρ
              → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (⌜ τ ⌝ᵉ ·̂ₑ (⌜ τ' ⌝ᵉ ·̂ₑ ûₑ))
claim-after-D ρ τ τ' p =
  box ⌜ ρ ⌝ʳ ⋆
    (delay τ (delay τ' (unbox (Tl-⟨⟩ (Tl-⟨⟩ Hd)) elapsed (<:̂ᵛ-refl _) (return (var Hd ok₀)))))
  where
    elapsed : ∅ᴴ ⊩ ûᵣ ·̂ᵣ ⌜ τ ⌝ʳ ·̂ᵣ ⌜ τ' ⌝ʳ ≾̂ᵣ ⌜ ρ ⌝ʳ
    elapsed = transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-const-· ≡̂ᵣ-refl) ≡̂ᵣ-const-·)) (atomᵣ p)

    ok₀ : VarOK ∅ᴴ Unit ûᵣ
    ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

claim-after-typable : ∀ ρ τ τ' → True ((uᵣ ·ᵣ of-durʳ τ ·ᵣ of-durʳ τ') ≾ᵣ? of-durʳ ρ)
                    → Typable [] (claim-after ρ τ τ')
claim-after-typable ρ τ τ' p = closed (claim-after-D ρ τ τ' (toWitness p)) refl

-- typed, the effect is the grade of the total duration `τ`

expected-claim-after : 𝔻 → Scheme
expected-claim-after τ = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ⌜ τ ⌝ᵉ

------------------------------------------------------------------
-- 2. A box grade inferred over two delays
--
--   inferred-grade τ τ' b = delay τ; delay τ'; unbox b as y in y
--
-- The claim asks for the grade of the two delays below the
-- argument's grade, and the argument sits contravariantly: the
-- principal scheme takes a box at that grade.

inferred-grade : 𝔻 → 𝔻 → RawC ∅ˢ 0
inferred-grade τ τ' = return (lam (delay τ (delay τ' (unbox fzero (return v₀)))))

-- the scheme at the total duration `τ`

expected-inferred-grade : 𝔻 → Scheme
expected-inferred-grade τ = ∀[ 1 , 0 , 0 ] ⊤ ⟹ ([ ⌜ τ ⌝ʳ ] α₀ ⇒ α₀ ‼ ⌜ τ ⌝ᵉ) ‼ ûₑ
