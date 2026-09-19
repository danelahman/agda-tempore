------------------------------------------------------------------
-- Closing a residual into the empty scope                       --
--                                                                --
-- The driver leaves a residual and a scope of unknowns; closing  --
-- it is where the heuristics live, and where they are confined.  --
-- Three flat passes:                                             --
--                                                                --
--   * slack — an ordering whose right-hand side is still a bare  --
--     variable is made an equality, the variable taking the left  --
--     side. An expected effect grade is only ever a right-hand    --
--     side, so this is what keeps an inferred effect the product  --
--     it was built from instead of collapsing to the unit;        --
--   * defaults — every unknown left over becomes `Unit`, `ûᵣ` or  --
--     `ûₑ`;                                                       --
--   * discharge — every atom is decided by `TypeInference.SolverImpl. --
--     Normal` and every eternality demand by `etDec`.             --
--                                                                --
-- A failure here is "this oracle found nothing", not "there is    --
-- nothing to find": the passes are linear and do not search.      --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

module TypeInference.SolverImpl.Close
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.SolverImpl.Core.Size S using (Sz)

open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.Normal S _≾ᵣ?_ _≾ₑ?_ umin?ᵣ umin?ₑ

--------------------------------------------------------------
-- Defaults                                                  --
--------------------------------------------------------------

groundˢ : ∀ {Ψ} → Subst Ψ ∅ˢ
groundˢ = sub (λ _ → Unit) (λ _ → ûᵣ) (λ _ → ûₑ)

--------------------------------------------------------------
-- Slack                                                     --
--                                                           --
-- Assignments are composed, so an unknown pinned to an       --
-- expression that is itself pinned later comes out fully     --
-- resolved; an unknown already pinned is left alone.         --
--------------------------------------------------------------

updᵉ : ∀ {Ψ} → EVar Ψ → EExp Ψ → Subst Ψ Ψ
updᵉ i ε = sub tvar rvar (λ k → if ⌊ k ≟ᶠ i ⌋ then ε else evar k)

updʳ : ∀ {Ψ} → RVar Ψ → RExp Ψ → Subst Ψ Ψ
updʳ i ρ = sub tvar (λ k → if ⌊ k ≟ᶠ i ⌋ then ρ else rvar k) evar

slackᵉ : ∀ {Ψ} → List (EExp Ψ × EExp Ψ) → Subst Ψ Ψ → Subst Ψ Ψ
slackᵉ []             σ = σ
slackᵉ ((ε , ε') ∷ l) σ with ε' [ σ ]ᵉ
... | evar i   = slackᵉ l (σ ⨟ˢ updᵉ i (ε [ σ ]ᵉ))
... | econst c = slackᵉ l σ
... | _ ·̂ₑ _   = slackᵉ l σ

slackʳ : ∀ {Ψ} → List (RExp Ψ × RExp Ψ) → Subst Ψ Ψ → Subst Ψ Ψ
slackʳ []             σ = σ
slackʳ ((ρ , ρ') ∷ l) σ with ρ' [ σ ]ʳ
... | rvar i   = slackʳ l (σ ⨟ˢ updʳ i (ρ [ σ ]ʳ))
... | rconst c = slackʳ l σ
... | _ ·̂ᵣ _   = slackʳ l σ
... | ∣ _ ∣̂ᵉ   = slackʳ l σ

slack¹ : ∀ {Ψ} → Resid Ψ → Subst Ψ Ψ → Subst Ψ Ψ
slack¹ R σ = slackʳ (rs R) (slackᵉ (es R) σ)

slack* : ∀ {Ψ} → ℕ → Resid Ψ → Subst Ψ Ψ → Subst Ψ Ψ
slack* nzero    R σ = σ
slack* (nsuc n) R σ = slack* n R (slack¹ R σ)

--------------------------------------------------------------
-- Discharge                                                 --
--------------------------------------------------------------

checkʳ : ∀ {Ψ} → (l : List (RExp Ψ × RExp Ψ)) → (δ : Subst Ψ ∅ˢ)
       → Maybe (∀ {ρ ρ'} → (ρ , ρ') ∈ l → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
checkʳ []             δ = just (λ ())
checkʳ ((ρ , ρ') ∷ l) δ with decide≾ᵣ {Q = ∅ᴴ} (ρ [ δ ]ʳ) (ρ' [ δ ]ʳ) | checkʳ l δ
... | just p  | just f  = just (λ { (here refl) → p ; (there m) → f m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

checkᵉ : ∀ {Ψ} → (l : List (EExp Ψ × EExp Ψ)) → (δ : Subst Ψ ∅ˢ)
       → Maybe (∀ {ε ε'} → (ε , ε') ∈ l → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
checkᵉ []             δ = just (λ ())
checkᵉ ((ε , ε') ∷ l) δ with decide≾ₑ {Q = ∅ᴴ} (ε [ δ ]ᵉ) (ε' [ δ ]ᵉ) | checkᵉ l δ
... | just p  | just f  = just (λ { (here refl) → p ; (there m) → f m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

checkᵗ : ∀ {Ψ} → (l : List (OVType Ψ)) → (δ : Subst Ψ ∅ˢ)
       → Maybe (∀ {A} → A ∈ l → ∅ᴴ ⊩ᴱ A [ δ ]ᵛ)
checkᵗ []      δ = just (λ ())
checkᵗ (A ∷ l) δ with etDec (A [ δ ]ᵛ) in eq | checkᵗ l δ
... | just []       | just f  =
      just (λ { (here refl) → etDec-sound {Q = ∅ᴴ} (A [ δ ]ᵛ) eq (λ ())
              ; (there m)   → f m })
... | just []       | nothing = nothing
... | just (α ∷ αs) | _       = nothing
... | nothing       | _       = nothing

closeAt : ∀ {Ψ} → (R : Resid Ψ) → (δ : Subst Ψ ∅ˢ) → Maybe (∅ᴴ ⊩ᴿ R [ δ ])
closeAt R δ with checkʳ (rs R) δ | checkᵉ (es R) δ | checkᵗ (ts R) δ
... | just f  | just g  | just k  = just (mk⊩ᴿ f g k)
... | just _  | just _  | nothing = nothing
... | just _  | nothing | _       = nothing
... | nothing | _       | _       = nothing

--------------------------------------------------------------
-- Closing                                                   --
--------------------------------------------------------------

close : ∀ {Ψ} → (R : Resid Ψ) → Maybe (Σ[ δ ∈ Subst Ψ ∅ˢ ] (∅ᴴ ⊩ᴿ R [ δ ]))
close {Ψ} R with closeAt R (slack* (Sz Ψ) R idˢ ⨟ˢ groundˢ)
... | just h  = just (slack* (Sz Ψ) R idˢ ⨟ˢ groundˢ , h)
... | nothing = nothing
