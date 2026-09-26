------------------------------------------------------------------
-- The rigid-binder-free fragment                                 --
--                                                                --
-- The driver is stuck only at the close of a rigid scope, so it  --
-- is never stuck on a constraint with no rigid binder, from any  --
-- state.                                                         --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_,_)

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.Outcome

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.RigidFree
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open Operations Ops

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.Constraints.Syntax S

open import TypeInference.SolverImpl.Core.AList    S using (⟦_⟧ᴬ)
open import TypeInference.SolverImpl.Core.Decorate S using (expandSub)
open import TypeInference.SolverImpl.Core.Eqn      S using (eqᵛ)
open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.State  S
open import TypeInference.SolverImpl.Normal S using (decide≾ᵣ)
open import TypeInference.SolverImpl.Solve  S opEnum

open OpEnum opEnum

labelled-≢stuck : ∀ {Θ} {s : St Θ} {C : Constraint Θ} → (op : Op)
                → (x : Outcome _) → x ≢ stuck → labelled {s = s} {C = C} op x ≢ stuck
labelled-≢stuck op refuted    h = λ ()
labelled-≢stuck op stuck      h = ⊥-elim (h refl)
labelled-≢stuck op (solved _) h = λ ()

threadOps-≢stuck : ∀ {Θ} {f : Op → Constraint Θ} → (g : (s : St Θ) → (op : Op) → Outcome _)
                 → (∀ s op → g s op ≢ stuck)
                 → (l : List Op) → (s : St Θ) → threadOps {f = f} g l s ≢ stuck
threadOps-≢stuck g h []       s = λ ()
threadOps-≢stuck {f = f} g h (op ∷ l) s with g s op in e
... | refuted = λ ()
... | stuck   = ⊥-elim (h s op e)
... | solved (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁ in e'
...   | refuted  = λ ()
...   | stuck    = λ _ → threadOps-≢stuck g h l s₁ e'
...   | solved _ = λ ()

solve-rigidFree : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ) → RigidFree C → solve s C ≢ stuck
solve-rigidFree s ⊤̂ p = λ ()
solve-rigidFree s ⊥̂ p = λ ()
solve-rigidFree s (C ∧̂ D) (p , q) with solve s C in e
... | refuted = λ ()
... | stuck   = ⊥-elim (solve-rigidFree s C p e)
... | solved (s₁ , m₁ , w₁) with solve s₁ D in e'
...   | refuted  = λ ()
...   | stuck    = λ _ → solve-rigidFree s₁ D q e'
...   | solved _ = λ ()
solve-rigidFree s (A ≐ᵥ B) p with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
... | nothing = λ ()
... | just (Ψ⁺ , ρ , equ) with expandSub (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ))
...   | nothing = λ ()
...   | just (Ψ' , δ) with subsList (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ))
                         | etsDec (ts (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ))
...     | nothing | _       = λ ()
...     | just _  | nothing = λ ()
...     | just _  | just _  = λ ()
solve-rigidFree s (A ≾̂ᵥᶜ B) p with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
... | nothing = λ ()
... | just (Ψ' , δ) with subDec (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ)
...   | nothing = λ ()
...   | just d  with subsList (ss (res s [ δ ]ᴿ)) | etsDec (ts (res s [ δ ]ᴿ))
...     | nothing | _       = λ ()
...     | just _  | nothing = λ ()
...     | just _  | just _  = λ ()
solve-rigidFree s (ρ ≾̂ᵣᶜ ρ') p = λ ()
solve-rigidFree s (ε ≾̂ₑᶜ ε') p = λ ()
solve-rigidFree s (Etᶜ A) p = solveEt-≢stuck (etDec (A [ θ s ]ᵛ)) refl
  where
    solveEt-≢stuck : ∀ x e → solveEt s A x e ≢ stuck
    solveEt-≢stuck nothing  e = λ ()
    solveEt-≢stuck (just _) e = λ ()
solve-rigidFree s (Et∨≾ᵘ A ρ) p with decide≾ᵣ {Q = ∅ᴴ} (ρ [ θ s ]ʳ) ûᵣ
... | just _  = λ ()
... | nothing = solveDisj-≢stuck (etDec (A [ θ s ]ᵛ)) refl
  where
    solveDisj-≢stuck : ∀ x e → solveDisj s A ρ x e ≢ stuck
    solveDisj-≢stuck nothing        e = λ ()
    solveDisj-≢stuck (just [])      e = λ ()
    solveDisj-≢stuck (just (_ ∷ _)) e = λ ()
solve-rigidFree s (∃ᵗ C) p with solve (s ↑ᵗˢ) C in e
... | refuted  = λ ()
... | stuck    = ⊥-elim (solve-rigidFree (s ↑ᵗˢ) C p e)
... | solved _ = λ ()
solve-rigidFree s (∃ʳ C) p with solve (s ↑ʳˢ) C in e
... | refuted  = λ ()
... | stuck    = ⊥-elim (solve-rigidFree (s ↑ʳˢ) C p e)
... | solved _ = λ ()
solve-rigidFree s (∃ᵉ C) p with solve (s ↑ᵉˢ) C in e
... | refuted  = λ ()
... | stuck    = ⊥-elim (solve-rigidFree (s ↑ᵉˢ) C p e)
... | solved _ = λ ()
solve-rigidFree s (∀ᵉ C) ()
solve-rigidFree s (⋀ᵒᵖ f) p
  with threadOps {f = f} (λ s' op → labelled {C = f op} op (solve s' (f op))) ops s in e
... | refuted  = λ ()
... | stuck    =
      ⊥-elim (threadOps-≢stuck _
                (λ s' op → labelled-≢stuck op (solve s' (f op)) (solve-rigidFree s' (f op) (p op)))
                ops s e)
... | solved _ = λ ()
