------------------------------------------------------------------
-- The driver as a solver interface instance                     --
--                                                                --
-- `TypeInference.Solver.Restricted.SolverOn` asks for a solver        --
-- returning a scope, a substitution and a hypothesis set. The     --
-- driver returns a state; `toHyps` reads its residual back as     --
-- the hypothesis set, and the three fields follow from the        --
-- driver's deferred witness, `solve-fail` and `solve-principal`.  --
--                                                                --
-- Principality is unguarded; refutation is guarded by `NoRig`,   --
-- since at a rigid binder a failure can be a failure of           --
-- `Normal`'s decision procedures. The read-back may also fail, on --
-- an eternality demand that decomposes to nothing — and that is   --
-- refutable, because substitution preserves a type's head former. --
------------------------------------------------------------------

open import Data.List.Base using (List; [])
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Restricted
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Types S
open import TypeInference.Open.Subst S
open import TypeInference.Open.Hyps  S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ; ≐ˢ-sym)

open import TypeInference.Solver.Fragment   S
open import TypeInference.Solver.Restricted S

open import TypeInference.SolverImpl.Core.Unify    S using (Rig; _∈ᶠ_)
open import TypeInference.SolverImpl.Core.UnifyMGU S using (Fixing; fixing)

open import TypeInference.SolverImpl.Resid     S
open import TypeInference.SolverImpl.State     S
open import TypeInference.SolverImpl.Solve     S _≾ᵣ?_ _≾ₑ?_ opEnum umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Principal S _≾ᵣ?_ _≾ₑ?_ opEnum umin?ᵣ umin?ₑ

Fixing-[] : ∀ {Θ Ψ} → (σ : Subst Θ Ψ) → Fixing [] σ
Fixing-[] σ = fixing (λ i ()) (λ i i' ())

solveOn : ∀ {Θ} → Constraint Θ
        → Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))
solveOn C with solve init C
... | nothing = nothing
... | just (s' , m , w) with toHyps (res s')
...   | nothing        = nothing
...   | just (Q , hq) = just (Ψ s' , θ s' , Q)

solveOn-sound : ∀ {Θ} → (C : Constraint Θ)
              → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
              → solveOn C ≡ just (Θ' , σ , Q)
              → σ ⊨[ Q ] C
solveOn-sound C eq with solve init C in e
... | nothing = ⊥just eq
... | just (s' , m , w) with toHyps (res s') in e'
...   | nothing = ⊥just eq
...   | just (Q₀ , hq) with eq
...     | refl = ⊨-resp-≐ˢ (⨟-idʳ (θ s')) C (w idˢ Q₀ hq)

solveOn-complete : ∀ {Θ} → (C : Constraint Θ) → NoRig C
                 → solveOn C ≡ nothing
                 → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
                 → ¬ (σ ⊨[ Q ] C)
solveOn-complete C nr eq σ Q sat with solve init C in e
... | nothing = solve-fail init C nr e σ Q (Fixing-[] σ) ⊩ᴿ-empty sat
... | just (s' , m , w) with toHyps (res s') in e'
...   | just _  = ⊥nothing eq
...   | nothing with toHyps-nothing (res s') e'
...     | A , mem , q =
          etDec-refute A q (proj₁ fac) (⊩ts (proj₁ (proj₂ (proj₂ fac))) mem)
  where
    fac = solve-principal init C e σ Q sat ⊩ᴿ-empty

solveOn-principal : ∀ {Θ} → (C : Constraint Θ)
                  → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                  → solveOn C ≡ just (Θ⁺ , σ⁺ , Q⁺)
                  → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                  → σ ⊨[ Q ] C
                  → Σ[ δ ∈ Subst Θ⁺ Θ'' ]
                      (((σ⁺ ⨟ˢ δ) ≐ˢ σ) × (Q ⊩ᴴ Q⁺ [ δ ]))
solveOn-principal C eq σ Q sat with solve init C in e
... | nothing = ⊥just eq
... | just (s' , m , w) with toHyps (res s') in e'
...   | nothing = ⊥just eq
...   | just (Q₀ , hq) with eq
...     | refl = δ ,
                 ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m)) δ) tri ,
                 toHyps-compl (res s') e' δ hres
  where
    fac  = solve-principal init C e σ Q sat ⊩ᴿ-empty
    δ    = proj₁ fac
    tri  = proj₁ (proj₂ fac)
    hres = proj₁ (proj₂ (proj₂ fac))

solverImplOn : SolverOn NoRig (λ _ → ⊤)
solverImplOn = record
  { solve           = solveOn
  ; solve-sound     = solveOn-sound
  ; solve-complete  = solveOn-complete
  ; solve-principal = λ C _ → solveOn-principal C
  }
