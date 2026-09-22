------------------------------------------------------------------
-- Closes a residual into the empty scope                         --
--                                                                --
-- The residual is read as bounds: its orderings and those the    --
-- subtyping demands decompose to, under the assignment reached   --
-- so far, a join on the left bounding by each of its summands    --
-- and an ordering whose left side is a summand of its right      --
-- bounding nothing, since it holds whatever the assignment.      --
--                                                                --
-- Slack sends a flexible grade variable to the join of its lower --
-- bounds, formed whether or not they are constants yet and       --
-- computed once the whole is closed. Tightening is its dual: a   --
-- variable bounded above and never below goes to its upper       --
-- bound, several being combined by comparability, grades having  --
-- no meet. A bound the variable occurs in is declined. What the  --
-- two passes leave is defaulted by the polarity of the same      --
-- bounds: the greatest grade where only lower bounds push, the   --
-- unit otherwise.                                                --
--                                                                --
-- At the empty scope an expression is a constant, so the checks  --
-- are complete and only the choice of substitution is heuristic. --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_; _∧_; _∨_; not; false) renaming (Bool to 𝔹)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

module TypeInference.SolverImpl.Close
  (S : LanguageSpec)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.OpenSyntax.Grounding S
  using (Grounding; grounding; ⟦_⟧ʳ; ⟦_⟧ᵉ; ∅ᴴ-⊨; ground-≾ᵣ; ground-≾ₑ)

open import TypeInference.SolverImpl.Core.Occurs S using (occʳ-r; occᵉ-e)
open import TypeInference.SolverImpl.Core.Size   S using (Sz)

open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Polarity S
open import TypeInference.SolverImpl.Normal   S umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Eliminate S using (joinᵣ; joinₑ)

-- The unique grounding of the empty scope, and the constant an
-- expression of that scope evaluates to

θ∅ : Grounding ∅ˢ
θ∅ = grounding (λ ()) (λ ()) (λ ())

evalᵉ-⟦⟧ : (ε : EExp ∅ˢ) → evalᵉ ε ≡ ⟦ ε ⟧ᵉ θ∅
evalᵉ-⟦⟧ (evar ())
evalᵉ-⟦⟧ (econst c) = refl
evalᵉ-⟦⟧ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (evalᵉ-⟦⟧ ε) (evalᵉ-⟦⟧ ε')
evalᵉ-⟦⟧ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (evalᵉ-⟦⟧ ε) (evalᵉ-⟦⟧ ε')

evalʳ-⟦⟧ : (ρ : RExp ∅ˢ) → evalʳ ρ ≡ ⟦ ρ ⟧ʳ θ∅
evalʳ-⟦⟧ (rvar ())
evalʳ-⟦⟧ (rconst c) = refl
evalʳ-⟦⟧ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (evalʳ-⟦⟧ ρ) (evalʳ-⟦⟧ ρ')
evalʳ-⟦⟧ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (evalʳ-⟦⟧ ρ) (evalʳ-⟦⟧ ρ')
evalʳ-⟦⟧ ∣ ε ∣̂ᵉ     = cong mapᵉ (evalᵉ-⟦⟧ ε)

-- Orderings of the empty scope, decided and refuted

closed≾ᵣ : (ρ ρ' : RExp ∅ˢ) → Maybe (∅ᴴ ⊩ ρ ≾̂ᵣ ρ')
closed≾ᵣ ρ ρ' with evalʳ ρ ≾ᵣ? evalʳ ρ'
... | yes p = just (transᵣ (proj₁ (⊩-reflectᵣ ρ))
                           (transᵣ (atomᵣ p) (proj₂ (⊩-reflectᵣ ρ'))))
... | no _  = nothing

closed≾ₑ : (ε ε' : EExp ∅ˢ) → Maybe (∅ᴴ ⊩ ε ≾̂ₑ ε')
closed≾ₑ ε ε' with evalᵉ ε ≾ₑ? evalᵉ ε'
... | yes p = just (transₑ (proj₁ (⊩-reflectₑ ε))
                           (transₑ (atomₑ p) (proj₂ (⊩-reflectₑ ε'))))
... | no _  = nothing

closed≾ᵣ-refute : (ρ ρ' : RExp ∅ˢ) → closed≾ᵣ ρ ρ' ≡ nothing → ¬ (∅ᴴ ⊩ ρ ≾̂ᵣ ρ')
closed≾ᵣ-refute ρ ρ' eq d with evalʳ ρ ≾ᵣ? evalʳ ρ'
closed≾ᵣ-refute ρ ρ' () d | yes _
closed≾ᵣ-refute ρ ρ' eq d | no ¬p =
  ¬p (subst₂ _≾ᵣ_ (sym (evalʳ-⟦⟧ ρ)) (sym (evalʳ-⟦⟧ ρ')) (ground-≾ᵣ ∅ᴴ-⊨ d))

closed≾ₑ-refute : (ε ε' : EExp ∅ˢ) → closed≾ₑ ε ε' ≡ nothing → ¬ (∅ᴴ ⊩ ε ≾̂ₑ ε')
closed≾ₑ-refute ε ε' eq d with evalᵉ ε ≾ₑ? evalᵉ ε'
closed≾ₑ-refute ε ε' () d | yes _
closed≾ₑ-refute ε ε' eq d | no ¬p =
  ¬p (subst₂ _≾ₑ_ (sym (evalᵉ-⟦⟧ ε)) (sym (evalᵉ-⟦⟧ ε')) (ground-≾ₑ ∅ᴴ-⊨ d))

-- A grade only pushed upwards is defaulted to the greatest grade,
-- every other to the unit.

defᵣ : Pol → RExp ∅ˢ
defᵣ p = if onlyBelow p then rconst ⊤ᵣ else ûᵣ

defₑ : Pol → EExp ∅ˢ
defₑ p = if onlyBelow p then econst ⊤ₑ else ûₑ

groundˢ : ∀ {Ψ} → Resid Ψ → Subst Ψ ∅ˢ
groundˢ R = sub (λ _ → Unit) (λ i → defᵣ (polᵣ R i)) (λ i → defₑ (polₑ R i))

-- Assignments compose: an unknown pinned to an expression pinned later
-- comes out fully resolved; an unknown already pinned is left alone.

updᵉ : ∀ {Ψ} → EVar Ψ → EExp Ψ → Subst Ψ Ψ
updᵉ i ε = sub tvar rvar (λ k → if ⌊ k ≟ᶠ i ⌋ then ε else evar k)

updʳ : ∀ {Ψ} → RVar Ψ → RExp Ψ → Subst Ψ Ψ
updʳ i ρ = sub tvar (λ k → if ⌊ k ≟ᶠ i ⌋ then ρ else rvar k) evar

-- The summands of an expression, a join read as the list of what it
-- joins

sumsᵉ : ∀ {Ψ} → EExp Ψ → List (EExp Ψ)
sumsᵉ (evar i)   = evar i ∷ []
sumsᵉ (econst c) = econst c ∷ []
sumsᵉ (ε ·̂ₑ ε')  = (ε ·̂ₑ ε') ∷ []
sumsᵉ (ε ⊔̂ₑ ε')  = sumsᵉ ε ++ sumsᵉ ε'

sumsʳ : ∀ {Ψ} → RExp Ψ → List (RExp Ψ)
sumsʳ (rvar i)   = rvar i ∷ []
sumsʳ (rconst c) = rconst c ∷ []
sumsʳ (ρ ·̂ᵣ ρ')  = (ρ ·̂ᵣ ρ') ∷ []
sumsʳ (ρ ⊔̂ᵣ ρ')  = sumsʳ ρ ++ sumsʳ ρ'
sumsʳ ∣ ε ∣̂ᵉ     = ∣ ε ∣̂ᵉ ∷ []

amongᵉ : ∀ {Ψ} → EExp Ψ → List (EExp Ψ) → 𝔹
amongᵉ ε []       = false
amongᵉ ε (ε' ∷ l) = ⌊ ε ≟ᵉ ε' ⌋ ∨ amongᵉ ε l

amongʳ : ∀ {Ψ} → RExp Ψ → List (RExp Ψ) → 𝔹
amongʳ ρ []       = false
amongʳ ρ (ρ' ∷ l) = ⌊ ρ ≟ʳ ρ' ⌋ ∨ amongʳ ρ l

-- A list of orderings read as bounds under an assignment. A join is
-- below the right side exactly when each of its summands is, so each
-- summand on the left is a bound of its own; a summand of the right
-- side is below it whatever the assignment, so that ordering bounds
-- nothing.

splitᵉ : ∀ {Ψ} → List (EExp Ψ) → EExp Ψ → List (EExp Ψ × EExp Ψ)
splitᵉ []      ε' = []
splitᵉ (ε ∷ l) ε' =
  if amongᵉ ε (sumsᵉ ε') then splitᵉ l ε' else (ε , ε') ∷ splitᵉ l ε'

splitʳ : ∀ {Ψ} → List (RExp Ψ) → RExp Ψ → List (RExp Ψ × RExp Ψ)
splitʳ []      ρ' = []
splitʳ (ρ ∷ l) ρ' =
  if amongʳ ρ (sumsʳ ρ') then splitʳ l ρ' else (ρ , ρ') ∷ splitʳ l ρ'

viewᵉ : ∀ {Ψ} → Subst Ψ Ψ → List (EExp Ψ × EExp Ψ) → List (EExp Ψ × EExp Ψ)
viewᵉ σ []             = []
viewᵉ σ ((ε , ε') ∷ l) = splitᵉ (sumsᵉ (ε [ σ ]ᵉ)) (ε' [ σ ]ᵉ) ++ viewᵉ σ l

viewʳ : ∀ {Ψ} → Subst Ψ Ψ → List (RExp Ψ × RExp Ψ) → List (RExp Ψ × RExp Ψ)
viewʳ σ []             = []
viewʳ σ ((ρ , ρ') ∷ l) = splitʳ (sumsʳ (ρ [ σ ]ʳ)) (ρ' [ σ ]ʳ) ++ viewʳ σ l

-- Every lower bound a list of bounds places on one unknown, and every
-- upper bound

lowerᵉ : ∀ {Ψ} → EVar Ψ → List (EExp Ψ × EExp Ψ) → List (EExp Ψ)
lowerᵉ i []                   = []
lowerᵉ i ((ε , evar j)   ∷ l) = if ⌊ j ≟ᶠ i ⌋ then ε ∷ lowerᵉ i l else lowerᵉ i l
lowerᵉ i ((ε , econst _) ∷ l) = lowerᵉ i l
lowerᵉ i ((ε , _ ·̂ₑ _)   ∷ l) = lowerᵉ i l
lowerᵉ i ((ε , _ ⊔̂ₑ _)   ∷ l) = lowerᵉ i l

lowerʳ : ∀ {Ψ} → RVar Ψ → List (RExp Ψ × RExp Ψ) → List (RExp Ψ)
lowerʳ i []                   = []
lowerʳ i ((ρ , rvar j)   ∷ l) = if ⌊ j ≟ᶠ i ⌋ then ρ ∷ lowerʳ i l else lowerʳ i l
lowerʳ i ((ρ , rconst _) ∷ l) = lowerʳ i l
lowerʳ i ((ρ , _ ·̂ᵣ _)   ∷ l) = lowerʳ i l
lowerʳ i ((ρ , _ ⊔̂ᵣ _)   ∷ l) = lowerʳ i l
lowerʳ i ((ρ , ∣ _ ∣̂ᵉ)   ∷ l) = lowerʳ i l

upperᵉ : ∀ {Ψ} → EVar Ψ → List (EExp Ψ × EExp Ψ) → List (EExp Ψ)
upperᵉ i []                    = []
upperᵉ i ((evar j   , ε') ∷ l) = if ⌊ j ≟ᶠ i ⌋ then ε' ∷ upperᵉ i l else upperᵉ i l
upperᵉ i ((econst _ , ε') ∷ l) = upperᵉ i l
upperᵉ i ((_ ·̂ₑ _   , ε') ∷ l) = upperᵉ i l
upperᵉ i ((_ ⊔̂ₑ _   , ε') ∷ l) = upperᵉ i l

upperʳ : ∀ {Ψ} → RVar Ψ → List (RExp Ψ × RExp Ψ) → List (RExp Ψ)
upperʳ i []                    = []
upperʳ i ((rvar j   , ρ') ∷ l) = if ⌊ j ≟ᶠ i ⌋ then ρ' ∷ upperʳ i l else upperʳ i l
upperʳ i ((rconst _ , ρ') ∷ l) = upperʳ i l
upperʳ i ((_ ·̂ᵣ _   , ρ') ∷ l) = upperʳ i l
upperʳ i ((_ ⊔̂ᵣ _   , ρ') ∷ l) = upperʳ i l
upperʳ i ((∣ _ ∣̂ᵉ   , ρ') ∷ l) = upperʳ i l

-- The lower bounds, folded into their join. The join is formed whether
-- or not the bounds are constants yet: a variable one still holds is
-- settled by the rounds that follow, and the join is computed once the
-- whole is closed.

boundᵉ : ∀ {Ψ} → List (EExp Ψ) → Maybe (EExp Ψ)
boundᵉ []      = nothing
boundᵉ (ε ∷ l) = just (joinₑ ε l)

boundʳ : ∀ {Ψ} → List (RExp Ψ) → Maybe (RExp Ψ)
boundʳ []      = nothing
boundʳ (ρ ∷ l) = just (joinᵣ ρ l)

-- Two upper bounds on one unknown, combined: the smaller of two
-- comparable bounds, else neither. Grades carry no meet, so this is
-- the whole of it.

cmpᵉ⁻ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Maybe (EExp Ψ)
cmpᵉ⁻ ε ε' with decide≾ₑ {Q = ∅ᴴ} ε ε' | decide≾ₑ {Q = ∅ᴴ} ε' ε
... | just _  | _       = just ε
... | nothing | just _  = just ε'
... | nothing | nothing = nothing

cmpʳ⁻ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Maybe (RExp Ψ)
cmpʳ⁻ ρ ρ' with decide≾ᵣ {Q = ∅ᴴ} ρ ρ' | decide≾ᵣ {Q = ∅ᴴ} ρ' ρ
... | just _  | _       = just ρ
... | nothing | just _  = just ρ'
... | nothing | nothing = nothing

-- The upper bounds, folded by comparability. A singleton is its own
-- fold; a pair that does not compare takes the fold with it, so an
-- unknown is never sent above a bound it was given.

capᵉ : ∀ {Ψ} → List (EExp Ψ) → Maybe (EExp Ψ)
capᵉ []           = nothing
capᵉ (ε ∷ [])     = just ε
capᵉ (ε ∷ ε' ∷ l) with capᵉ (ε' ∷ l)
... | nothing  = nothing
... | just ε'' = cmpᵉ⁻ ε ε''

capʳ : ∀ {Ψ} → List (RExp Ψ) → Maybe (RExp Ψ)
capʳ []           = nothing
capʳ (ρ ∷ [])     = just ρ
capʳ (ρ ∷ ρ' ∷ l) with capʳ (ρ' ∷ l)
... | nothing  = nothing
... | just ρ'' = cmpʳ⁻ ρ ρ''

-- A bound in which the unknown itself occurs is no value for it

bindᵉ : ∀ {Ψ} → EVar Ψ → Maybe (EExp Ψ) → Subst Ψ Ψ → Subst Ψ Ψ
bindᵉ i nothing  σ = σ
bindᵉ i (just ε) σ = if occᵉ-e i ε then σ else σ ⨟ˢ updᵉ i ε

bindʳ : ∀ {Ψ} → RVar Ψ → Maybe (RExp Ψ) → Subst Ψ Ψ → Subst Ψ Ψ
bindʳ i nothing  σ = σ
bindʳ i (just ρ) σ = if occʳ-r i ρ then σ else σ ⨟ˢ updʳ i ρ

slackᵉ : ∀ {Ψ} → (l l₀ : List (EExp Ψ × EExp Ψ)) → Subst Ψ Ψ → Subst Ψ Ψ
slackᵉ []             l₀ σ = σ
slackᵉ ((ε , ε') ∷ l) l₀ σ with ε' [ σ ]ᵉ
... | evar i   = slackᵉ l l₀ (bindᵉ i (boundᵉ (lowerᵉ i (viewᵉ σ l₀))) σ)
... | econst _ = slackᵉ l l₀ σ
... | _ ·̂ₑ _   = slackᵉ l l₀ σ
... | _ ⊔̂ₑ _   = slackᵉ l l₀ σ

slackʳ : ∀ {Ψ} → (l l₀ : List (RExp Ψ × RExp Ψ)) → Subst Ψ Ψ → Subst Ψ Ψ
slackʳ []             l₀ σ = σ
slackʳ ((ρ , ρ') ∷ l) l₀ σ with ρ' [ σ ]ʳ
... | rvar i   = slackʳ l l₀ (bindʳ i (boundʳ (lowerʳ i (viewʳ σ l₀))) σ)
... | rconst _ = slackʳ l l₀ σ
... | _ ·̂ᵣ _   = slackʳ l l₀ σ
... | _ ⊔̂ᵣ _   = slackʳ l l₀ σ
... | ∣ _ ∣̂ᵉ   = slackʳ l l₀ σ

-- Tightening is confined to the unknowns no demand bounds from below,
-- the upper bound being no value for one that is pushed up too. The
-- unknowns it visits are the summands of each left side.

onlyAbove : Pol → 𝔹
onlyAbove p = above p ∧ not (below p)

capsᵉ : ∀ {Ψ} → (EVar Ψ → Pol)
      → List (EExp Ψ) → List (EExp Ψ × EExp Ψ) → Subst Ψ Ψ → Subst Ψ Ψ
capsᵉ p []             l₀ σ = σ
capsᵉ p (evar i   ∷ l) l₀ σ =
  capsᵉ p l l₀ (if onlyAbove (p i)
                  then bindᵉ i (capᵉ (upperᵉ i (viewᵉ σ l₀))) σ else σ)
capsᵉ p (econst _ ∷ l) l₀ σ = capsᵉ p l l₀ σ
capsᵉ p (_ ·̂ₑ _   ∷ l) l₀ σ = capsᵉ p l l₀ σ
capsᵉ p (_ ⊔̂ₑ _   ∷ l) l₀ σ = capsᵉ p l l₀ σ

capsʳ : ∀ {Ψ} → (RVar Ψ → Pol)
      → List (RExp Ψ) → List (RExp Ψ × RExp Ψ) → Subst Ψ Ψ → Subst Ψ Ψ
capsʳ p []             l₀ σ = σ
capsʳ p (rvar i   ∷ l) l₀ σ =
  capsʳ p l l₀ (if onlyAbove (p i)
                  then bindʳ i (capʳ (upperʳ i (viewʳ σ l₀))) σ else σ)
capsʳ p (rconst _ ∷ l) l₀ σ = capsʳ p l l₀ σ
capsʳ p (_ ·̂ᵣ _   ∷ l) l₀ σ = capsʳ p l l₀ σ
capsʳ p (_ ⊔̂ᵣ _   ∷ l) l₀ σ = capsʳ p l l₀ σ
capsʳ p (∣ _ ∣̂ᵉ   ∷ l) l₀ σ = capsʳ p l l₀ σ

tightᵉ : ∀ {Ψ} → (EVar Ψ → Pol)
       → (l l₀ : List (EExp Ψ × EExp Ψ)) → Subst Ψ Ψ → Subst Ψ Ψ
tightᵉ p []             l₀ σ = σ
tightᵉ p ((ε , ε') ∷ l) l₀ σ = tightᵉ p l l₀ (capsᵉ p (sumsᵉ (ε [ σ ]ᵉ)) l₀ σ)

tightʳ : ∀ {Ψ} → (RVar Ψ → Pol)
       → (l l₀ : List (RExp Ψ × RExp Ψ)) → Subst Ψ Ψ → Subst Ψ Ψ
tightʳ p []             l₀ σ = σ
tightʳ p ((ρ , ρ') ∷ l) l₀ σ = tightʳ p l l₀ (capsʳ p (sumsʳ (ρ [ σ ]ʳ)) l₀ σ)

-- The grade orderings the subtyping demands decompose to. A
-- substitution leaves a head former alone, so the decomposition does
-- not depend on the assignment slack has reached.

atomsˢ : ∀ {Ψ} → List (OVType Ψ × OVType Ψ) → SubAtoms Ψ
atomsˢ []            = noAtoms
atomsˢ ((A , B) ∷ l) with subDec A B
... | just d  = atomsOf d ∪ᴬ atomsˢ l
... | nothing = atomsˢ l

-- Every ordering the closer reads: the residual's own, and those its
-- subtyping demands decompose to

ordsʳ : ∀ {Ψ} → Resid Ψ → List (RExp Ψ × RExp Ψ)
ordsʳ R = rs R ++ aordᵣ (atomsˢ (ss R))

ordsᵉ : ∀ {Ψ} → Resid Ψ → List (EExp Ψ × EExp Ψ)
ordsᵉ R = es R ++ aordₑ (atomsˢ (ss R))

-- The residual as the closer reads it under an assignment: its
-- orderings as bounds, a subtyping demand bounding through its
-- decomposition alone. Polarities are read off this.

seenᴿ : ∀ {Ψ} → Resid Ψ → Subst Ψ Ψ → Resid Ψ
seenᴿ R σ = resid (viewʳ σ (ordsʳ R)) (viewᵉ σ (ordsᵉ R))
                  (ts (R [ σ ]ᴿ)) [] (ds (R [ σ ]ᴿ))

slack¹ : ∀ {Ψ} → Resid Ψ → Subst Ψ Ψ → Subst Ψ Ψ
slack¹ R σ = tightʳ (polᵣ R') lʳ lʳ (tightᵉ (polₑ R') lᵉ lᵉ
               (slackʳ lʳ lʳ (slackᵉ lᵉ lᵉ σ)))
  where
    lʳ : List (RExp _ × RExp _)
    lʳ = ordsʳ R

    lᵉ : List (EExp _ × EExp _)
    lᵉ = ordsᵉ R

    -- the polarities the pass reads are those of the bounds as the
    -- assignment reached so far leaves them

    R' : Resid _
    R' = seenᴿ R σ

slack* : ∀ {Ψ} → ℕ → Resid Ψ → Subst Ψ Ψ → Subst Ψ Ψ
slack* nzero    R σ = σ
slack* (nsuc n) R σ = slack* n R (slack¹ R σ)

checkʳ : ∀ {Ψ} → (l : List (RExp Ψ × RExp Ψ)) → (δ : Subst Ψ ∅ˢ)
       → Maybe (∀ {ρ ρ'} → (ρ , ρ') ∈ l → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
checkʳ []             δ = just (λ ())
checkʳ ((ρ , ρ') ∷ l) δ with closed≾ᵣ (ρ [ δ ]ʳ) (ρ' [ δ ]ʳ) | checkʳ l δ
... | just p  | just f  = just (λ { (here refl) → p ; (there m) → f m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

checkᵉ : ∀ {Ψ} → (l : List (EExp Ψ × EExp Ψ)) → (δ : Subst Ψ ∅ˢ)
       → Maybe (∀ {ε ε'} → (ε , ε') ∈ l → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
checkᵉ []             δ = just (λ ())
checkᵉ ((ε , ε') ∷ l) δ with closed≾ₑ (ε [ δ ]ᵉ) (ε' [ δ ]ᵉ) | checkᵉ l δ
... | just p  | just f  = just (λ { (here refl) → p ; (there m) → f m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

-- A failed grade check names an atom the substitution refutes

checkʳ-nothing : ∀ {Ψ} → (l : List (RExp Ψ × RExp Ψ)) → (δ : Subst Ψ ∅ˢ)
               → checkʳ l δ ≡ nothing
               → Σ[ ρ ∈ RExp Ψ ] Σ[ ρ' ∈ RExp Ψ ]
                   (((ρ , ρ') ∈ l) × ¬ (∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ))
checkʳ-nothing []             δ ()
checkʳ-nothing ((ρ , ρ') ∷ l) δ eq with closed≾ᵣ (ρ [ δ ]ʳ) (ρ' [ δ ]ʳ) in e
checkʳ-nothing ((ρ , ρ') ∷ l) δ eq | nothing =
  ρ , ρ' , here refl , closed≾ᵣ-refute (ρ [ δ ]ʳ) (ρ' [ δ ]ʳ) e
checkʳ-nothing ((ρ , ρ') ∷ l) δ eq | just _ with checkʳ l δ in e'
checkʳ-nothing ((ρ , ρ') ∷ l) δ () | just _ | just _
checkʳ-nothing ((ρ , ρ') ∷ l) δ eq | just _ | nothing with checkʳ-nothing l δ e'
... | ρ₀ , ρ₀' , m , ¬p = ρ₀ , ρ₀' , there m , ¬p

checkᵉ-nothing : ∀ {Ψ} → (l : List (EExp Ψ × EExp Ψ)) → (δ : Subst Ψ ∅ˢ)
               → checkᵉ l δ ≡ nothing
               → Σ[ ε ∈ EExp Ψ ] Σ[ ε' ∈ EExp Ψ ]
                   (((ε , ε') ∈ l) × ¬ (∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ))
checkᵉ-nothing []             δ ()
checkᵉ-nothing ((ε , ε') ∷ l) δ eq with closed≾ₑ (ε [ δ ]ᵉ) (ε' [ δ ]ᵉ) in e
checkᵉ-nothing ((ε , ε') ∷ l) δ eq | nothing =
  ε , ε' , here refl , closed≾ₑ-refute (ε [ δ ]ᵉ) (ε' [ δ ]ᵉ) e
checkᵉ-nothing ((ε , ε') ∷ l) δ eq | just _ with checkᵉ l δ in e'
checkᵉ-nothing ((ε , ε') ∷ l) δ () | just _ | just _
checkᵉ-nothing ((ε , ε') ∷ l) δ eq | just _ | nothing with checkᵉ-nothing l δ e'
... | ε₀ , ε₀' , m , ¬p = ε₀ , ε₀' , there m , ¬p

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

-- At the empty scope a decomposition raises no atom on type variables,
-- so only its grade orderings are left to decide.

no-tvar : ∀ {X : Set} → TyVar ∅ˢ → X
no-tvar ()

checkˢ¹ : ∀ {Ψ} → (A B : OVType Ψ) → (δ : Subst Ψ ∅ˢ)
        → Maybe (∅ᴴ ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ)
checkˢ¹ A B δ with subDec (A [ δ ]ᵛ) (B [ δ ]ᵛ)
... | nothing = nothing
... | just d with checkʳ (aordᵣ (atomsOf d)) idˢ | checkᵉ (aordₑ (atomsOf d)) idˢ
...   | just g  | just k  =
        just (subst₂ (∅ᴴ ∣_<:̂ᵛ_) ([id]ᵛ (A [ δ ]ᵛ)) ([id]ᵛ (B [ δ ]ᵛ))
                     (intro d idˢ (holds (λ {α} m → no-tvar α) g k)))
...   | just _  | nothing = nothing
...   | nothing | _       = nothing

checkˢ : ∀ {Ψ} → (l : List (OVType Ψ × OVType Ψ)) → (δ : Subst Ψ ∅ˢ)
       → Maybe (∀ {A B} → (A , B) ∈ l → ∅ᴴ ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ)
checkˢ []             δ = just (λ ())
checkˢ ((A , B) ∷ l) δ with checkˢ¹ A B δ | checkˢ l δ
... | just p  | just f  = just (λ { (here refl) → p ; (there m) → f m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

-- At the ground substitution a disjunction is closed by whichever
-- disjunct holds: the grade side first, the eternality side after.

checkᵈ : ∀ {Ψ} → (l : List (OVType Ψ × RExp Ψ)) → (δ : Subst Ψ ∅ˢ)
       → Maybe (∀ {A ρ} → (A , ρ) ∈ l → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
checkᵈ []             δ = just (λ ())
checkᵈ ((A , ρ) ∷ l) δ with checkᵈ l δ
... | nothing = nothing
... | just f with closed≾ᵣ (ρ [ δ ]ʳ) ûᵣ
...   | just p  = just (λ { (here refl) → ≾ᵘ-ok p ; (there m) → f m })
...   | nothing with etDec (A [ δ ]ᵛ) in eq
...     | just []       =
          just (λ { (here refl) → et-ok (etDec-sound {Q = ∅ᴴ} (A [ δ ]ᵛ) eq (λ ()))
                  ; (there m)   → f m })
...     | just (α ∷ αs) = nothing
...     | nothing       = nothing

closeAt : ∀ {Ψ} → (R : Resid Ψ) → (δ : Subst Ψ ∅ˢ) → Maybe (∅ᴴ ⊩ᴿ R [ δ ])
closeAt R δ with checkʳ (rs R) δ | checkᵉ (es R) δ | checkᵗ (ts R) δ
               | checkˢ (ss R) δ | checkᵈ (ds R) δ
... | just f  | just g  | just k  | just b  | just d  = just (mk⊩ᴿ f g k b d)
... | just _  | just _  | just _  | just _  | nothing = nothing
... | just _  | just _  | just _  | nothing | _       = nothing
... | just _  | just _  | nothing | _       | _       = nothing
... | just _  | nothing | _       | _       | _       = nothing
... | nothing | _       | _       | _       | _       = nothing

-- A closed join, computed. The joins slack forms are left standing
-- until every variable in them is settled; at the empty scope that is
-- all of them.

settleᵉ : EExp ∅ˢ → EExp ∅ˢ
settleᵉ (evar ())
settleᵉ (econst c) = econst c
settleᵉ (ε ·̂ₑ ε')  = settleᵉ ε ·̂ₑ settleᵉ ε'
settleᵉ (ε ⊔̂ₑ ε')  = econst (evalᵉ ε ⊔ₑ evalᵉ ε')

settleʳ : RExp ∅ˢ → RExp ∅ˢ
settleʳ (rvar ())
settleʳ (rconst c) = rconst c
settleʳ (ρ ·̂ᵣ ρ')  = settleʳ ρ ·̂ᵣ settleʳ ρ'
settleʳ (ρ ⊔̂ᵣ ρ')  = rconst (evalʳ ρ ⊔ᵣ evalʳ ρ')
settleʳ ∣ ε ∣̂ᵉ     = ∣ settleᵉ ε ∣̂ᵉ

settleˢ : ∀ {Ψ} → Subst Ψ ∅ˢ → Subst Ψ ∅ˢ
settleˢ δ = sub (sTy δ) (λ i → settleʳ (sR δ i)) (λ i → settleᵉ (sE δ i))

-- The candidate substitution: slack, then the defaults, whose
-- polarities are read off the bounds slack leaves, then the joins
-- computed.

closeˢ : ∀ {Ψ} → Resid Ψ → Subst Ψ ∅ˢ
closeˢ {Ψ} R = settleˢ (σ ⨟ˢ groundˢ (seenᴿ R σ))
  where
    σ : Subst Ψ Ψ
    σ = slack* (Sz Ψ) R idˢ

close : ∀ {Ψ} → (R : Resid Ψ) → Maybe (Σ[ δ ∈ Subst Ψ ∅ˢ ] (∅ᴴ ⊩ᴿ R [ δ ]))
close R with closeAt R (closeˢ R)
... | just h  = just (closeˢ R , h)
... | nothing = nothing
