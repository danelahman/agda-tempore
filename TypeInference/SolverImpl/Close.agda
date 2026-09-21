------------------------------------------------------------------
-- Closes a residual into the empty scope                         --
--                                                                --
-- Slack sends a flexible grade variable to the combination of    --
-- its lower bounds — those of the orderings and those the        --
-- subtyping demands decompose to — by the supplied join, else by --
-- comparability; a bound the variable occurs in is declined.     --
-- What slack leaves is defaulted by polarity: the greatest grade --
-- where only lower bounds push, the unit otherwise.              --
--                                                                --
-- At the empty scope an expression is a constant, so the checks  --
-- are complete and only the choice of substitution is heuristic. --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_; yes; no)
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
  (join?ᵣ : Maybe (H.Joinᵣ S))                 -- optional binary join on `_≾ᵣ_`
  (join?ₑ : Maybe (H.Joinₑ S))                 -- optional binary join on `_≾ₑ_`
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.Open.Grounding S
  using (Grounding; grounding; ⟦_⟧ʳ; ⟦_⟧ᵉ; ∅ᴴ-⊨; ground-≾ᵣ; ground-≾ₑ)

open import TypeInference.SolverImpl.Core.Occurs S using (occʳ-r; occᵉ-e)
open import TypeInference.SolverImpl.Core.Rigid  S using (zip₂)
open import TypeInference.SolverImpl.Core.Size   S using (Sz)

open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Polarity S
open import TypeInference.SolverImpl.Normal   S _≾ᵣ?_ _≾ₑ?_ umin?ᵣ umin?ₑ

-- The unique grounding of the empty scope, and the constant an
-- expression of that scope evaluates to

θ∅ : Grounding ∅ˢ
θ∅ = grounding (λ ()) (λ ()) (λ ())

evalᵉ-⟦⟧ : (ε : EExp ∅ˢ) → evalᵉ ε ≡ ⟦ ε ⟧ᵉ θ∅
evalᵉ-⟦⟧ (evar ())
evalᵉ-⟦⟧ (econst c) = refl
evalᵉ-⟦⟧ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (evalᵉ-⟦⟧ ε) (evalᵉ-⟦⟧ ε')

evalʳ-⟦⟧ : (ρ : RExp ∅ˢ) → evalʳ ρ ≡ ⟦ ρ ⟧ʳ θ∅
evalʳ-⟦⟧ (rvar ())
evalʳ-⟦⟧ (rconst c) = refl
evalʳ-⟦⟧ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (evalʳ-⟦⟧ ρ) (evalʳ-⟦⟧ ρ')
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

-- The constant a variable-free expression evaluates to

valᵉ : ∀ {Ψ} → EExp Ψ → Maybe E
valᵉ (evar _)   = nothing
valᵉ (econst c) = just c
valᵉ (ε ·̂ₑ ε')  = zip₂ _·ₑ_ (valᵉ ε) (valᵉ ε')

valʳ : ∀ {Ψ} → RExp Ψ → Maybe R
valʳ (rvar _)   = nothing
valʳ (rconst c) = just c
valʳ (ρ ·̂ᵣ ρ')  = zip₂ _·ᵣ_ (valʳ ρ) (valʳ ρ')
valʳ ∣ ε ∣̂ᵉ     = mmap mapᵉ (valᵉ ε)

-- Two lower bounds on one unknown, combined: their join where the
-- instance supplies one and both are variable-free, else the larger of
-- two comparable bounds, else neither.

joinᵉ? : ∀ {Ψ} → Maybe Joinₑ → EExp Ψ → EExp Ψ → Maybe (EExp Ψ)
joinᵉ? nothing  ε ε' = nothing
joinᵉ? (just j) ε ε' = mmap econst (zip₂ (Joinₑ._⊔ₑ_ j) (valᵉ ε) (valᵉ ε'))

joinʳ? : ∀ {Ψ} → Maybe Joinᵣ → RExp Ψ → RExp Ψ → Maybe (RExp Ψ)
joinʳ? nothing  ρ ρ' = nothing
joinʳ? (just j) ρ ρ' = mmap rconst (zip₂ (Joinᵣ._⊔ᵣ_ j) (valʳ ρ) (valʳ ρ'))

cmpᵉ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Maybe (EExp Ψ)
cmpᵉ ε ε' with decide≾ₑ {Q = ∅ᴴ} ε ε' | decide≾ₑ {Q = ∅ᴴ} ε' ε
... | just _  | _       = just ε'
... | nothing | just _  = just ε
... | nothing | nothing = nothing

cmpʳ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Maybe (RExp Ψ)
cmpʳ ρ ρ' with decide≾ᵣ {Q = ∅ᴴ} ρ ρ' | decide≾ᵣ {Q = ∅ᴴ} ρ' ρ
... | just _  | _       = just ρ'
... | nothing | just _  = just ρ
... | nothing | nothing = nothing

lubᵉ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Maybe (EExp Ψ)
lubᵉ ε ε' with joinᵉ? join?ₑ ε ε'
... | just ε'' = just ε''
... | nothing  = cmpᵉ ε ε'

lubʳ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Maybe (RExp Ψ)
lubʳ ρ ρ' with joinʳ? join?ᵣ ρ ρ'
... | just ρ'' = just ρ''
... | nothing  = cmpʳ ρ ρ'

-- Every lower bound a list of orderings places on one unknown, and
-- their combination

lowerᵉ : ∀ {Ψ} → EVar Ψ → List (EExp Ψ × EExp Ψ) → Subst Ψ Ψ → List (EExp Ψ)
lowerᵉ i []             σ = []
lowerᵉ i ((ε , ε') ∷ l) σ with ε' [ σ ]ᵉ
... | evar j   = if ⌊ j ≟ᶠ i ⌋ then ε [ σ ]ᵉ ∷ lowerᵉ i l σ else lowerᵉ i l σ
... | econst _ = lowerᵉ i l σ
... | _ ·̂ₑ _   = lowerᵉ i l σ

lowerʳ : ∀ {Ψ} → RVar Ψ → List (RExp Ψ × RExp Ψ) → Subst Ψ Ψ → List (RExp Ψ)
lowerʳ i []             σ = []
lowerʳ i ((ρ , ρ') ∷ l) σ with ρ' [ σ ]ʳ
... | rvar j   = if ⌊ j ≟ᶠ i ⌋ then ρ [ σ ]ʳ ∷ lowerʳ i l σ else lowerʳ i l σ
... | rconst _ = lowerʳ i l σ
... | _ ·̂ᵣ _   = lowerʳ i l σ
... | ∣ _ ∣̂ᵉ   = lowerʳ i l σ

boundᵉ : ∀ {Ψ} → List (EExp Ψ) → Maybe (EExp Ψ)
boundᵉ []      = nothing
boundᵉ (ε ∷ l) with boundᵉ l
... | nothing = just ε
... | just ε' = lubᵉ ε ε'

boundʳ : ∀ {Ψ} → List (RExp Ψ) → Maybe (RExp Ψ)
boundʳ []      = nothing
boundʳ (ρ ∷ l) with boundʳ l
... | nothing = just ρ
... | just ρ' = lubʳ ρ ρ'

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
... | evar i   = slackᵉ l l₀ (bindᵉ i (boundᵉ (lowerᵉ i l₀ σ)) σ)
... | econst _ = slackᵉ l l₀ σ
... | _ ·̂ₑ _   = slackᵉ l l₀ σ

slackʳ : ∀ {Ψ} → (l l₀ : List (RExp Ψ × RExp Ψ)) → Subst Ψ Ψ → Subst Ψ Ψ
slackʳ []             l₀ σ = σ
slackʳ ((ρ , ρ') ∷ l) l₀ σ with ρ' [ σ ]ʳ
... | rvar i   = slackʳ l l₀ (bindʳ i (boundʳ (lowerʳ i l₀ σ)) σ)
... | rconst _ = slackʳ l l₀ σ
... | _ ·̂ᵣ _   = slackʳ l l₀ σ
... | ∣ _ ∣̂ᵉ   = slackʳ l l₀ σ

-- The grade orderings the subtyping demands decompose to. A
-- substitution leaves a head former alone, so the decomposition does
-- not depend on the assignment slack has reached.

atomsˢ : ∀ {Ψ} → List (OVType Ψ × OVType Ψ) → SubAtoms Ψ
atomsˢ []            = noAtoms
atomsˢ ((A , B) ∷ l) with subDec A B
... | just d  = atomsOf d ∪ᴬ atomsˢ l
... | nothing = atomsˢ l

slack¹ : ∀ {Ψ} → Resid Ψ → Subst Ψ Ψ → Subst Ψ Ψ
slack¹ R σ = slackʳ lʳ lʳ (slackᵉ lᵉ lᵉ σ)
  where
    a : SubAtoms _
    a = atomsˢ (ss R)

    lʳ : List (RExp _ × RExp _)
    lʳ = rs R ++ aordᵣ a

    lᵉ : List (EExp _ × EExp _)
    lᵉ = es R ++ aordₑ a

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

-- The candidate substitution: slack, then the defaults, whose
-- polarities are read off the residual slack leaves.

closeˢ : ∀ {Ψ} → Resid Ψ → Subst Ψ ∅ˢ
closeˢ {Ψ} R = σ ⨟ˢ groundˢ (R [ σ ]ᴿ)
  where
    σ : Subst Ψ Ψ
    σ = slack* (Sz Ψ) R idˢ

close : ∀ {Ψ} → (R : Resid Ψ) → Maybe (Σ[ δ ∈ Subst Ψ ∅ˢ ] (∅ᴴ ⊩ᴿ R [ δ ]))
close R with closeAt R (closeˢ R)
... | just h  = just (closeˢ R , h)
... | nothing = nothing
