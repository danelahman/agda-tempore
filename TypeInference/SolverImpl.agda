------------------------------------------------------------------
-- A concrete constraint solver, under an enumerability           --
-- assumption.                                                    --
-- Parameters: an operation enumeration, and optional             --
-- unit-minimality witnesses. The grade orders are decided by     --
-- the grades themselves.                                         --
------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)


open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))              -- optional unit-minimality of `_≾ᵣ_`
  (umin?ₑ : Maybe (H.UnitMinₑ S))              -- optional unit-minimality of `_≾ₑ_`
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

open import Syntax.Contexts S using (Ctx)
open import Syntax.Language S using (_⊢C⦂_)

open import TypeInference.OpenSyntax.ClosedContexts   S using (skel; ⌜_⌝ᶜᵗˣ;
                                                           ⌜⌝ᶜᵗˣ-subst; ⌜⌝ᶜᵗˣ-ground)
open import TypeInference.OpenSyntax.Grounding        S using (∅ᴴ-⊨)
open import TypeInference.OpenSyntax.GroundingTheorem S using (groundC)

open import TypeInference.Raw.Syntax S using (RawC)
open import TypeInference.Soundness  S using (soundC; ctx-substᶜ; ⌊ctxᶜ⌋)
open import TypeInference.Infer      S using (Θ₁; X̂₁; t̂₁; C∅[_,_]; Inferred; inferred; θ∅)


open import TypeInference.SolverImpl.State S using (St; θ; res; init)
open import TypeInference.SolverImpl.Solve S opEnum umin?ᵣ umin?ₑ using (solve)
open import TypeInference.SolverImpl.Close S umin?ᵣ umin?ₑ
  using (close)
open import TypeInference.SolverImpl.Canon   S using (canonᵛ)
open import TypeInference.SolverImpl.Product S using (canonₑ)

-- The `gsolve` field of `GroundSolver` — the only part attainable here.

gsolveImpl : ∀ {Θ} → (C : Constraint Θ)
           → Maybe (Σ[ σ ∈ Subst Θ ∅ˢ ] (σ ⊨[ ∅ᴴ ] C))
gsolveImpl C with solve init C
... | nothing = nothing
... | just (s' , m , w) with close (res s')
...   | nothing      = nothing
...   | just (δ , h) = just (θ s' ⨟ˢ δ , w δ ∅ᴴ h)

-- The reporting boundary of the ground path: the solved type and
-- effect, every grade expression in product normal form. It is the
-- counterpart of `Restricted.reportOn`, and rests on the same fact,
-- that `canonᵛ`/`canonₑ` leave the denotation alone.

greportImpl : (Γ : Ctx) → (M : RawC (skel Γ))
            → Maybe (OVType ∅ˢ × EExp ∅ˢ)
greportImpl Γ M with gsolveImpl C∅[ Γ , M ]
... | nothing      = nothing
... | just (σ , _) = just (canonᵛ (X̂₁ [ σ ]ᵛ) , canonₑ (t̂₁ [ σ ]ᵉ))

-- Feeds `gsolveImpl`'s result to `soundC`, `ctx-substᶜ` and `groundC`,
-- bypassing `TypeInference.Infer.infer` (which needs a whole `GroundSolver`).

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
