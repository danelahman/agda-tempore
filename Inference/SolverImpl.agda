------------------------------------------------------------------
-- A concrete constraint solver                                   --
--                                                                --
-- The `Solver` of `Inference.Solver` is an assumption, and must   --
-- be: `_≾ᵣ_`/`_≾ₑ_` are undecidable in the `Grade` interface and  --
-- `⋀ᵒᵖ`/`∀ᵉ` are infinitary. This module builds as much of one as --
-- is buildable, under three explicit assumptions — decidability   --
-- of the two grade orders and an enumeration of the operation     --
-- symbols — and is honest about the rest.                         --
--                                                                --
-- The design is the temporal-millet prototype's, adapted to the   --
-- fact that satisfaction of `_≐ᵥ_` is *syntactic* equality of     --
-- substituted types: substitution never normalises grades, so a   --
-- solved type equation must be made literally true by assignment, --
-- never by rewriting. Accordingly:                                --
--                                                                --
--   * the solver carries the substitution as an *accumulator* and --
--     returns the satisfaction witness, so every accepting path   --
--     is correct by construction and no separate soundness proof  --
--     is needed;                                                  --
--   * at an existential it guesses, by probing the constraint it  --
--     scopes over for a pattern equation that pins the fresh      --
--     variable (`Inference.SolverImpl.Match`), and falls back on  --
--     the prototype's defaults (`Unit`, `ûᵣ`, `ûₑ`);              --
--   * a grade ordering is decided by normalising both sides to    --
--     atom lists and comparing them atom by atom                  --
--     (`Inference.SolverImpl.Normal`);                            --
--   * `∀ᵉ` lifts the accumulator, so a rigid effect variable is   --
--     an opaque constant of the enlarged target scope and is      --
--     never guessed;                                              --
--   * `⋀ᵒᵖ` is discharged by exhausting `OpEnum`.                 --
--                                                                --
-- What is *not* attained: `gsolve-complete`. The guessing is a    --
-- heuristic — a failure is "this solver found nothing", not "no   --
-- solution exists" — so `GroundSolver` is not instantiated, and   --
-- `Solver` (residual `Hyps`, principality) is out of scope        --
-- altogether. See DECISIONS-TypeInference.md for the fragment     --
-- the solver does decide.                                         --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

open import Inference.SolverImpl.Enum using (OpEnum)

module Inference.SolverImpl
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types S using (EternalBaseType; eternalBaseType?)

open import Inference.Open.Grades S
open import Inference.Open.Types  S
open import Inference.Open.Subst  S
open import Inference.Open.Hyps   S

open import Inference.Constraints.Syntax       S
open import Inference.Constraints.Satisfaction S

open import Syntax.Contexts S using (Ctx)
open import Syntax.Language S using (_⊢C⦂_)

open import Inference.Open.ClosedContexts   S using (skel; ⌜_⌝ᶜᵗˣ;
                                                     ⌜⌝ᶜᵗˣ-subst; ⌜⌝ᶜᵗˣ-ground)
open import Inference.Open.Grounding        S using (∅ᴴ-⊨)
open import Inference.Open.GroundingTheorem S using (groundC)

open import Inference.Raw.Syntax S using (RawC)
open import Inference.Soundness  S using (soundC; ctx-substᶜ; ⌊ctxᶜ⌋)
open import Inference.Infer      S using (Θ₁; X̂₁; t̂₁; C∅[_,_]; Inferred; inferred; θ∅)

open import Inference.SolverImpl.Enum   S using (AllOp; all-lookup; all-build)
open import Inference.SolverImpl.Match  S
open import Inference.SolverImpl.Normal S _≾ᵣ?_ _≾ₑ?_

open OpEnum opEnum

--------------------------------------------------------------
-- Trying a list of candidates                               --
--------------------------------------------------------------

firstJust : ∀ {A : Set} {P : A → Set} → ((x : A) → Maybe (P x))
          → List A → Maybe (Σ[ x ∈ A ] P x)
firstJust g []       = nothing
firstJust g (x ∷ xs) with g x
... | just p  = just (x , p)
... | nothing = firstJust g xs

--------------------------------------------------------------
-- Eternality of a hypothesis-free open type                 --
--                                                           --
-- Mirrors `eternal?` of `Syntax.Types`. No grounding is      --
-- involved: a type variable is only eternal by hypothesis,   --
-- and the solver's hypothesis set is empty.                  --
--------------------------------------------------------------

et? : ∀ {Θ} {Q : Hyps Θ} → (A : OVType Θ) → Maybe (Q ⊩ᴱ A)
et? (tvar α) = nothing
et? (Base b) with eternalBaseType? b
... | yes p = just (Baseₑ p)
... | no _  = nothing
et? Unit      = just Unitₑ
et? Bool      = just Boolₑ
et? Empty     = just Emptyₑ
et? (A |×| B) with et? A | et? B
... | just p | just q = just (p |×|ₑ q)
... | _      | _      = nothing
et? (A ⇒ C)   = nothing
et? ([ ρ ] A) = nothing

--------------------------------------------------------------
-- Candidate witnesses for an existential                    --
--                                                           --
-- The probe's answer first, the prototype's default second.  --
--------------------------------------------------------------

candᵗ : ∀ {Θ Θ'} → Subst Θ Θ' → Constraint (Θ +ty) → List (OVType Θ')
candᵗ σ C with probeᵗ (env⊙ᵗ σ) C
... | just B  = B ∷ Unit ∷ []
... | nothing = Unit ∷ []

candʳ : ∀ {Θ Θ'} → Subst Θ Θ' → Constraint (Θ +r) → List (RExp Θ')
candʳ σ C with probeʳ (env⊙ʳ σ) C
... | just ρ  = ρ ∷ ûᵣ ∷ []
... | nothing = ûᵣ ∷ []

candᵉ : ∀ {Θ Θ'} → Subst Θ Θ' → Constraint (Θ +e) → List (EExp Θ')
candᵉ σ C with probeᵉ (env⊙ᵉ σ) C
... | just ε  = ε ∷ ûₑ ∷ []
... | nothing = ûₑ ∷ []

--------------------------------------------------------------
-- The solver                                                --
--                                                           --
-- `solve σ C` extends the accumulator `σ` over the binders   --
-- of `C` and checks every atom under it, returning the       --
-- satisfaction witness itself.                               --
--------------------------------------------------------------

solve : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (C : Constraint Θ) → Maybe (σ ⊨[ ∅ᴴ ] C)
solve σ ⊤̂ = just tt
solve σ ⊥̂ = nothing
solve σ (C ∧̂ D) with solve σ C | solve σ D
... | just p | just q = just (p , q)
... | _      | _      = nothing
solve σ (A ≐ᵥ B)   = A [ σ ]ᵛ ≟ᵛ B [ σ ]ᵛ
solve σ (ρ ≾̂ᵣᶜ ρ') = decide≾ᵣ (ρ [ σ ]ʳ) (ρ' [ σ ]ʳ)
solve σ (ε ≾̂ₑᶜ ε') = decide≾ₑ (ε [ σ ]ᵉ) (ε' [ σ ]ᵉ)
solve σ (Etᶜ A)    = et? (A [ σ ]ᵛ)
solve σ (Et∨≾ᵘ A ρ) with et? (A [ σ ]ᵛ) | decide≾ᵣ (ρ [ σ ]ʳ) ûᵣ
... | just p  | _       = just (inj₁ p)
... | nothing | just q  = just (inj₂ q)
... | nothing | nothing = nothing
solve σ (∃ᵗ C) = firstJust (λ B → solve (σ ,ᵗ B) C) (candᵗ σ C)
solve σ (∃ʳ C) = firstJust (λ ρ → solve (σ ,ʳ ρ) C) (candʳ σ C)
solve σ (∃ᵉ C) = firstJust (λ ε → solve (σ ,ᵉ ε) C) (candᵉ σ C)
solve σ (∀ᵉ C) = solve (σ ↑ᵉ) C
solve σ (⋀ᵒᵖ f) with all-build (λ op → solve σ (f op)) ops
... | just ps = just (λ op → all-lookup ps (complete op))
... | nothing = nothing

--------------------------------------------------------------
-- Seeding the accumulator                                   --
--                                                           --
-- The variables of the constraint's own scope are not bound  --
-- by any `∃`, so they are probed one by one against the      --
-- constraint, each in the company of the current values of   --
-- the others. Two sweeps let a type's own grades be fixed    --
-- after the type is.                                         --
--------------------------------------------------------------

defaultˢ : ∀ {Θ Θ'} → Subst Θ Θ'
defaultˢ = sub (λ _ → Unit) (λ _ → ûᵣ) (λ _ → ûₑ)

sweepᵗ : ∀ {Θ Θ'} → Subst Θ Θ' → Constraint Θ → Subst Θ Θ'
sweepᵗ σ C = sub (λ α → orDefault (sTy σ α) (probeᵗ (env♯ᵗ σ α) C)) (sR σ) (sE σ)

sweepʳ : ∀ {Θ Θ'} → Subst Θ Θ' → Constraint Θ → Subst Θ Θ'
sweepʳ σ C = sub (sTy σ) (λ i → orDefault (sR σ i) (probeʳ (env♯ʳ σ i) C)) (sE σ)

sweepᵉ : ∀ {Θ Θ'} → Subst Θ Θ' → Constraint Θ → Subst Θ Θ'
sweepᵉ σ C = sub (sTy σ) (sR σ) (λ i → orDefault (sE σ i) (probeᵉ (env♯ᵉ σ i) C))

sweepˢ : ∀ {Θ Θ'} → Subst Θ Θ' → Constraint Θ → Subst Θ Θ'
sweepˢ σ C = sweepᵉ (sweepʳ (sweepᵗ σ C) C) C

seedˢ : ∀ {Θ} → Constraint Θ → Subst Θ ∅ˢ
seedˢ C = sweepˢ defaultˢ C

--------------------------------------------------------------
-- Solving into the empty scope                              --
--                                                           --
-- This is the `gsolve` field of `GroundSolver`, and all of   --
-- it that is attainable: a success carries its own           --
-- soundness, a failure carries nothing.                      --
--------------------------------------------------------------

gsolveImpl : ∀ {Θ} → (C : Constraint Θ)
           → Maybe (Σ[ σ ∈ Subst Θ ∅ˢ ] (σ ⊨[ ∅ᴴ ] C))
gsolveImpl C with solve (seedˢ C) C
... | just p  = just (seedˢ C , p)
... | nothing = nothing

--------------------------------------------------------------
-- Inference, end to end                                     --
--                                                           --
-- `Inference.Infer.infer` takes a whole `GroundSolver`, so   --
-- it is out of reach (see above). Its pipeline is not: the   --
-- solution `gsolveImpl` returns is exactly what `soundC`,    --
-- `ctx-substᶜ` and `groundC` consume, and the result is a    --
-- typing derivation of the ORIGINAL system together with     --
-- its mirrored origin and erasure equation.                   --
--------------------------------------------------------------

inferImpl : (Γ : Ctx) → (M : RawC (skel Γ)) → Maybe (Inferred Γ M)
inferImpl Γ M = elaborate (gsolveImpl C∅[ Γ , M ])
  where
    elaborate : Maybe (Σ[ σ ∈ Subst Θ₁ ∅ˢ ] (σ ⊨[ ∅ᴴ ] C∅[ Γ , M ]))
              → Maybe (Inferred Γ M)
    elaborate nothing          = nothing
    elaborate (just (σ , sat)) = just (inferred σ D̂ ⌊D̂⌋ _ _ refl refl D)
      where
        elab = soundC ⌜ Γ ⌝ᶜᵗˣ M X̂₁ t̂₁ sat
        ce   = ⌜⌝ᶜᵗˣ-subst σ Γ

        D̂   = ctx-substᶜ ce (proj₁ elab)
        ⌊D̂⌋ = trans (⌊ctxᶜ⌋ ce (proj₁ elab)) (proj₂ elab)

        D = subst (λ G → G ⊢C⦂ _) (⌜⌝ᶜᵗˣ-ground θ∅ Γ) (groundC θ∅ ∅ᴴ-⊨ D̂)
