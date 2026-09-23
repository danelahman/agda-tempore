------------------------------------------------------------------
-- A program's report.                                            --
--                                                                --
-- `reportOn`, run on the constraint generated for a program in   --
-- an open context, with the report written out as data: the      --
-- scope it is stated in, the reported type, and the eternality   --
-- atoms, subtyping atoms, resource-grade orderings, effect-grade --
-- orderings and var-rule disjunctions left with it. `sizeOf`     --
-- keeps only how many of each sort survive.                      --
--                                                                --
-- A report is walked through once before it is returned, so that --
-- all of it is evaluated in one reduction, the solver's run      --
-- shared between its parts; compared with a literal position by  --
-- position, an unevaluated report would run it again for each.   --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false; _∧_) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary.Decidable using (does)

open import Syntax.Grades

open import Syntax.LanguageSpec

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Demo.Report
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   S
open import TypeInference.OpenSyntax.Types    S
open import TypeInference.OpenSyntax.Contexts S using (OCtx)
open import TypeInference.OpenSyntax.Hyps     S

open import TypeInference.Raw.Syntax S using (RawC)

open import TypeInference.Principality S using (X̂; t̂; C[_,_])

open import TypeInference.SolverImpl.Restricted S opEnum umin?ᵣ umin?ₑ
  using (reportOn; Reported)

Report : Set
Report = Σ[ Θ ∈ Scope ] (OCType Θ
                          × List (TyVar Θ)
                          × List (TyVar Θ × TyVar Θ)
                          × List (RExp Θ × RExp Θ)
                          × List (EExp Θ × EExp Θ)
                          × List (OVType Θ × RExp Θ))

-- A walk through every part of a report; its answer is always `true`

private

  walkℕ : ℕ → 𝔹
  walkℕ zero    = true
  walkℕ (suc n) = walkℕ n

  walkᶠ : ∀ {n} → Fin n → 𝔹
  walkᶠ zero    = true
  walkᶠ (suc i) = walkᶠ i

  walkᵉ : ∀ {Θ} → EExp Θ → 𝔹
  walkᵉ (evar i)   = walkᶠ i
  walkᵉ (econst c) = does (c ≾ₑ? c)
  walkᵉ (ε ·̂ₑ ε')  = walkᵉ ε ∧ walkᵉ ε'
  walkᵉ (ε ⊔̂ₑ ε')  = walkᵉ ε ∧ walkᵉ ε'

  walkʳ : ∀ {Θ} → RExp Θ → 𝔹
  walkʳ (rvar i)   = walkᶠ i
  walkʳ (rconst c) = does (c ≾ᵣ? c)
  walkʳ (ρ ·̂ᵣ ρ')  = walkʳ ρ ∧ walkʳ ρ'
  walkʳ (ρ ⊔̂ᵣ ρ')  = walkʳ ρ ∧ walkʳ ρ'
  walkʳ ∣ ε ∣̂ᵉ     = walkᵉ ε

  mutual

    walkᵛ : ∀ {Θ} → OVType Θ → 𝔹
    walkᵛ (tvar α)  = walkᶠ α
    walkᵛ (Base b)  = true
    walkᵛ Unit      = true
    walkᵛ Bool      = true
    walkᵛ (A |×| B) = walkᵛ A ∧ walkᵛ B
    walkᵛ Empty     = true
    walkᵛ (A ⇒ C)   = walkᵛ A ∧ walkᶜ C
    walkᵛ ([ ρ ] A) = walkʳ ρ ∧ walkᵛ A

    walkᶜ : ∀ {Θ} → OCType Θ → 𝔹
    walkᶜ (A ‼ ε) = walkᵛ A ∧ walkᵉ ε

  walkˡ : ∀ {A : Set} → (A → 𝔹) → List A → 𝔹
  walkˡ f []       = true
  walkˡ f (x ∷ xs) = f x ∧ walkˡ f xs

  walkᵖ : ∀ {A B : Set} → (A → 𝔹) → (B → 𝔹) → A × B → 𝔹
  walkᵖ f g (x , y) = f x ∧ g y

  walk : Report → 𝔹
  walk (scope a b c , X , es , ss , rs , fs , ds) =
    walkℕ a ∧ walkℕ b ∧ walkℕ c ∧ walkᶜ X
    ∧ walkˡ walkᶠ es ∧ walkˡ (walkᵖ walkᶠ walkᶠ) ss
    ∧ walkˡ (walkᵖ walkʳ walkʳ) rs ∧ walkˡ (walkᵖ walkᵉ walkᵉ) fs
    ∧ walkˡ (walkᵖ walkᵛ walkʳ) ds

  -- `x`, once the walk has answered

  after : ∀ {A : Set} → 𝔹 → A → A
  after true  x = x
  after false x = x

  report! : Report → Maybe Report
  report! r = after (walk r) (just r)

reportOf : ∀ {Θ n} → OCtx Θ n → RawC n → Maybe Report
reportOf {Θ} Γ M with reportOn (X̂ Θ ‼ t̂ Θ) C[ Γ , M ]
... | nothing = nothing
... | just r  = report! (Reported.Θ' r , Reported.X̃ r ,
                         ets  (Reported.Q̃ r) , subᵥ (Reported.Q̃ r) ,
                         ordᵣ (Reported.Q̃ r) , ordₑ (Reported.Q̃ r) ,
                         disj (Reported.Q̃ r))

sizeOf : ∀ {Θ n} → OCtx Θ n → RawC n → Maybe (ℕ × ℕ × ℕ × ℕ × ℕ)
sizeOf Γ M = map sizes (reportOf Γ M)
  where
    sizes : Report → ℕ × ℕ × ℕ × ℕ × ℕ
    sizes (_ , _ , ets , subs , osᵣ , osₑ , ds) =
      length ets , length subs , length osᵣ , length osₑ , length ds
