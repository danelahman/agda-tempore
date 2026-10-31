--------------------------------------------------------------------
-- Inference with durations that are not whole ticks              --
--                                                                --
-- A box claimed after two delays of arbitrary durations, and a   --
-- box grade inferred over them. The instances under              --
-- `Durations/` check each answer by `refl` at dense time.        --
--------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Durations (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (𝔻; ιᵣ; ιₑ; _·ᵣ_; 𝟏ᵣ; _≾ᵣ?_)
  renaming (_≾ᵣ_ to _≾ᴳ_)

open import PolymorphicCalculus.Syntax.Grades                S
open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S hiding (Scheme)
open import PolymorphicCalculus.Syntax.GradeSubstitution     S using (idˢ)
open import PolymorphicCalculus.Hypotheses                   S
open import PolymorphicCalculus.Hypotheses.Instances         S using (Satisfiable-∅)
open import PolymorphicCalculus.Typing                       S
open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S using (_[_]ᴿᶜ)
open import PolymorphicCalculus.Typing.Erasure               S using (⌊_⌋ᶜ)
open import PolymorphicCalculus.Inference.Principality       S

open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import PolymorphicCalculus.Examples.Scheme S public
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- The grades of a duration

⌜_⌝ʳ : ∀ {Θ} → 𝔻 → RExp Θ
⌜ τ ⌝ʳ = rconst (ιᵣ τ)

⌜_⌝ᵉ : ∀ {Θ} → 𝔻 → EExp Θ
⌜ τ ⌝ᵉ = econst (ιₑ τ)

-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

------------------------------------------------------------------
-- 1. A box claimed after two delays
--
--   claim-after ρ τ τ' = box[ρ] () as x in delay τ; delay τ'; unbox x as y in y
--
-- `𝟏ᵣ · ι τ · ι τ' ≾ ι ρ`, decided on the constants.

claim-after : 𝔻 → 𝔻 → 𝔻 → RawC ∅ˢ 0
claim-after ρ τ τ' = box ⌜ ρ ⌝ʳ ⋆ (delay τ (delay τ' (unbox (var fzero) (return v₀))))

claim-after-D : ∀ ρ τ τ' → 𝟏ᵣ ·ᵣ ιᵣ τ ·ᵣ ιᵣ τ' ≾ᴳ ιᵣ ρ
              → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ unit ! (⌜ τ ⌝ᵉ ·̂ₑ (⌜ τ' ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
claim-after-D ρ τ τ' p =
  box ⌜ ρ ⌝ʳ ⋆
    (delay τ (delay τ' (unbox (res-var {z = Tl-⟨⟩ (Tl-⟨⟩ Hd)}) elapsed (return (var Hd ok₀)))))
  where
    elapsed : ∅ᴴ ⊩ 𝟏̂ᵣ ·̂ᵣ ⌜ τ ⌝ʳ ·̂ᵣ ⌜ τ' ⌝ʳ ≾̂ᵣ ⌜ ρ ⌝ʳ
    elapsed = transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-const-· ≡̂ᵣ-refl) ≡̂ᵣ-const-·)) (atomᵣ p)

    ok₀ : ∅ᴴ ⊩ unit Et∨≾ᵘ 𝟏̂ᵣ
    ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

claim-after-typable : ∀ ρ τ τ' → True ((𝟏ᵣ ·ᵣ ιᵣ τ ·ᵣ ιᵣ τ') ≾ᵣ? ιᵣ ρ)
                    → Typable [] (claim-after ρ τ τ')
claim-after-typable ρ τ τ' p = closed (claim-after-D ρ τ τ' (toWitness p)) refl

-- typed, the effect is the grade of the total duration `τ`

expected-claim-after : 𝔻 → Scheme
expected-claim-after τ = ∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! ⌜ τ ⌝ᵉ

------------------------------------------------------------------
-- 2. A box grade inferred over two delays
--
--   inferred-grade τ τ' b = delay τ; delay τ'; unbox b as y in y
--
-- The principal scheme takes a box at the grade of both delays.

inferred-grade : 𝔻 → 𝔻 → RawC ∅ˢ 0
inferred-grade τ τ' = return (fun (delay τ (delay τ' (unbox (var fzero) (return v₀)))))

-- the scheme at the total duration `τ`

expected-inferred-grade : 𝔻 → Scheme
expected-inferred-grade τ = ∀[ 1 , 0 , 0 ] ⊤ ⟹ ([ ⌜ τ ⌝ʳ ] α₀ ⇒ α₀ ! ⌜ τ ⌝ᵉ) ! 𝟏̂ₑ
