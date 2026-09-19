------------------------------------------------------------------
-- A concrete constraint solver                                   --
--                                                                --
-- The `Solver` of `TypeInference.Solver` is an assumption, and must   --
-- be: `_≾ᵣ_`/`_≾ₑ_` are undecidable in the `Grade` interface and  --
-- `⋀ᵒᵖ`/`∀ᵉ` are infinitary. This module builds as much of one as --
-- is buildable, under three explicit assumptions — decidability   --
-- of the two grade orders and an enumeration of the operation     --
-- symbols — and is honest about the rest. Two further parameters  --
-- are optional: a proof that the unit is the least grade, on      --
-- either side, which `nothing` switches off.                      --
--                                                                --
-- The solver is in two halves, and the split is the point.        --
--                                                                --
--   * `TypeInference.SolverImpl.Solve` drives the constraint against  --
--     the unification core of `TypeInference.SolverImpl.Core`. It     --
--     takes no defaults: a type equation is solved by the core,   --
--     a grade ordering and an eternality demand are carried as a  --
--     residual, and the `var`-rule disjunction is biased towards  --
--     its grade disjunct, which constrains no type. What it       --
--     returns is a substitution together with what is left over,  --
--     and a witness deferred until the leftovers are discharged.  --
--   * `TypeInference.SolverImpl.Close` discharges the leftovers into  --
--     the empty scope. This is the heuristic half: slack, then    --
--     the defaults `Unit`/`ûᵣ`/`ûₑ`, then the decision procedures  --
--     of `TypeInference.SolverImpl.Normal`.                           --
--                                                                --
-- Satisfaction of `_≐ᵥ_` is *syntactic* equality of substituted   --
-- types — substitution never normalises grades — so a solved type --
-- equation is made literally true by assignment, and the core's   --
-- verdicts across the sorts are the right ones.                   --
--                                                                --
-- What is *not* attained: `gsolve-complete`. Closing is a         --
-- heuristic — a failure is "this solver found nothing", not "no   --
-- solution exists" — so `GroundSolver` is not instantiated.       --
------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Binary.Definitions using (Decidable)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))              -- optional unit-minimality of `_≾ᵣ_`
  (umin?ₑ : Maybe (H.UnitMinₑ S))              -- optional unit-minimality of `_≾ₑ_`
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

open import Syntax.Contexts S using (Ctx)
open import Syntax.Language S using (_⊢C⦂_)

open import TypeInference.Open.ClosedContexts   S using (skel; ⌜_⌝ᶜᵗˣ;
                                                     ⌜⌝ᶜᵗˣ-subst; ⌜⌝ᶜᵗˣ-ground)
open import TypeInference.Open.Grounding        S using (∅ᴴ-⊨)
open import TypeInference.Open.GroundingTheorem S using (groundC)

open import TypeInference.Raw.Syntax S using (RawC)
open import TypeInference.Soundness  S using (soundC; ctx-substᶜ; ⌊ctxᶜ⌋)
open import TypeInference.Infer      S using (Θ₁; X̂₁; t̂₁; C∅[_,_]; Inferred; inferred; θ∅)


open import TypeInference.SolverImpl.State S using (St; θ; res; init)
open import TypeInference.SolverImpl.Solve S _≾ᵣ?_ _≾ₑ?_ opEnum umin?ᵣ umin?ₑ using (solve)
open import TypeInference.SolverImpl.Close S _≾ᵣ?_ _≾ₑ?_ umin?ᵣ umin?ₑ using (close)

--------------------------------------------------------------
-- Solving into the empty scope                              --
--                                                           --
-- This is the `gsolve` field of `GroundSolver`, and all of   --
-- it that is attainable: a success carries its own           --
-- soundness, a failure carries nothing. The witness the      --
-- driver deferred is applied to the closing substitution and --
-- the discharge of the residual it comes with, and IS the    --
-- satisfaction proof.                                       --
--------------------------------------------------------------

gsolveImpl : ∀ {Θ} → (C : Constraint Θ)
           → Maybe (Σ[ σ ∈ Subst Θ ∅ˢ ] (σ ⊨[ ∅ᴴ ] C))
gsolveImpl C with solve init C
... | nothing = nothing
... | just (s' , m , w) with close (res s')
...   | nothing      = nothing
...   | just (δ , h) = just (θ s' ⨟ˢ δ , w δ ∅ᴴ h)

--------------------------------------------------------------
-- Inference, end to end                                     --
--                                                           --
-- `TypeInference.Infer.infer` takes a whole `GroundSolver`, so   --
-- it is out of reach (see above). Its pipeline is not: the   --
-- solution `gsolveImpl` returns is exactly what `soundC`,    --
-- `ctx-substᶜ` and `groundC` consume, and the result is a    --
-- typing derivation of the ORIGINAL system together with     --
-- its mirrored origin and erasure equation.                  --
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
