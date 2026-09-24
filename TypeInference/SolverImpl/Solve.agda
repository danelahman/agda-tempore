------------------------------------------------------------------
-- The solver driver                                            --
--                                                              --
-- Walks a constraint, threading a state: type equations go to  --
-- the unification core, a subtyping atom is decomposed at      --
-- matching formers and residualised at a pair of type          --
-- variables, grade orderings, eternality demands and var-rule  --
-- disjunctions are residualised, and binders lift the state.   --
-- An expansion of the type unknowns is followed by decomposing --
-- the residual's subtyping demands again, so that they are     --
-- pairs of type variables and their grade orderings are        --
-- residualised with the others.                                --
--                                                              --
-- A successful witness is deferred, re-read at the state a     --
-- later component leaves behind rather than transported along  --
-- it.                                                          --
--                                                              --
-- At a rigid binder the state is lifted with a fresh residual. --
-- Before the scope closes, its subtyping demands are expanded  --
-- and decomposed again (`reexpand`), so that they are pairs of --
-- type variables, the atoms decided true are dropped, and the  --
-- unknowns local to the scope are sent to their principal      --
-- values (`Localise`); then                                    --
-- atoms free of the rigid are kept, one whose right side alone --
-- mentions it is kept at the unit rigid where the unit is      --
-- least, one whose left side alone mentions it is kept at the  --
-- top rigid, any other is discharged on the spot or, when it   --
-- mentions only the rigid and outer unknowns, deferred as a    --
-- new entry. The scope's own entries are carried out under the --
-- rigid, and an outer unknown's image must stay free of it.    --
-- After each close the entries are retried.                    --
--                                                              --
-- The outcome is a solution, a refutation, or stuck: a close   --
-- whose atom, neither kept nor deferred, or whose inner entry, --
-- mentions an unknown local to the scope.                      --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_; Dec; yes; no)


open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.Outcome

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Solve
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S
open import TypeInference.OpenSyntax.Instances S
  using (_+eⁿ_; _↑ᵉⁿ_; wkᵉⁿ-H; closed-≾ᵣ; closed-≾ₑ)

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ)

open import TypeInference.SolverImpl.Enum S using (AllOp; []; _∷_; all-lookup)

open import TypeInference.SolverImpl.Core.AList      S
open import TypeInference.SolverImpl.Core.Occurs     S using (occᵉ-e; occᵉ-r; occʳ-r)
open import TypeInference.SolverImpl.Core.Decorate   S using (expandSub)
open import TypeInference.SolverImpl.Core.Eqn        S
open import TypeInference.SolverImpl.Core.Rigid      S
open import TypeInference.SolverImpl.Core.Unify      S
open import TypeInference.SolverImpl.Core.UnifySound S using (unify-sound)

open import TypeInference.SolverImpl.Deferred S
open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.State  S
open import TypeInference.SolverImpl.Closed S using (valʳ?; valᵉ?; convʳ; convᵉ)
open import TypeInference.SolverImpl.Normal S
open import TypeInference.SolverImpl.Localise S
  using (Localised; localise; lσ; lR; lsnd; freeᵉ; freeʳ; Outerₑ; Outerᵣ; outerₑ?; outerᵣ?;
         evar?)

open OpEnum opEnum

Wit : ∀ {Θ} → (s : St Θ) → Constraint Θ → Set
Wit s C = ∀ {Ψ'} → (δ : Subst (Ψ s) Ψ') → (Q : Hyps Ψ')
        → Q ⊩ᴿ (res s) [ δ ] → (θ s ⨟ˢ δ) ⊨[ Q ] C

-- A witness is re-read at any later state

wit-mono : ∀ {Θ} → {s s' : St Θ} → s ⟶ s' → (C : Constraint Θ) → Wit s C → Wit s' C
wit-mono {s = s} m C w δ Q h =
  ⊨-resp-≐ˢ (⨟-congˡ (mtri m) δ) C
    (⊨-resp-≐ˢ (≐ˢ-sym (⨟-assoc (θ s) (mδ m) δ)) C (w (mδ m ⨟ˢ δ) Q (mres m δ Q h)))

-- An atom either strengthens away from the rigid and is kept, or must
-- be discharged where the rigid is still in scope; a decision against
-- `∅ᴴ` transports to any later hypothesis set and substitution.

pop⨟ʳ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (ρ : RExp (Φ +e)) → {ρ₀ : RExp Φ}
      → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → (δ : Subst Φ Φ')
      → ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≡ wkᵉ-r (ρ₀ [ δ ]ʳ)
pop⨟ʳ j ρ {ρ₀} q δ =
  trans (sym ([⨟]ʳ ρ (popˢ j) (δ ↑ᵉ)))
        (trans (cong (_[ δ ↑ᵉ ]ʳ) q) (wk-↑ᵉ-r δ ρ₀))

pop⨟ᵉ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (ε : EExp (Φ +e)) → {ε₀ : EExp Φ}
      → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → (δ : Subst Φ Φ')
      → ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ ≡ wkᵉ-e (ε₀ [ δ ]ᵉ)
pop⨟ᵉ j ε {ε₀} q δ =
  trans (sym ([⨟]ᵉ ε (popˢ j) (δ ↑ᵉ)))
        (trans (cong (_[ δ ↑ᵉ ]ᵉ) q) (wk-↑ᵉ-e δ ε₀))

pop⨟ᵛ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → {A₀ : OVType Φ}
      → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀ → (δ : Subst Φ Φ')
      → A [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ ≡ wkᵉ-v (A₀ [ δ ]ᵛ)
pop⨟ᵛ j A {A₀} q δ =
  trans (sym ([⨟]ᵛ A (popˢ j) (δ ↑ᵉ)))
        (trans (cong (_[ δ ↑ᵉ ]ᵛ) q) (wk-↑ᵉ-v δ A₀))

Atomʳ : ∀ {Φ} → EVar (Φ +e) → RExp (Φ +e) → RExp (Φ +e) → Set
Atomʳ {Φ} j ρ ρ' =
  Σ[ l₀ ∈ List (RExp Φ × RExp Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
       → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ)

Atomᵉ : ∀ {Φ} → EVar (Φ +e) → EExp (Φ +e) → EExp (Φ +e) → Set
Atomᵉ {Φ} j ε ε' =
  Σ[ l₀ ∈ List (EExp Φ × EExp Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ᵉ ≾̂ₑ τ' [ δ ]ᵉ)
       → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ)

Atomᵗ : ∀ {Φ} → EVar (Φ +e) → OVType (Φ +e) → Set
Atomᵗ {Φ} j A =
  Σ[ l₀ ∈ List (OVType Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {B} → B ∈ l₀ → Q ⊩ᴱ B [ δ ]ᵛ)
       → wkᵉ-H Q ⊩ᴱ A [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ)

Atomˢ : ∀ {Φ} → EVar (Φ +e) → OVType (Φ +e) → OVType (Φ +e) → Set
Atomˢ {Φ} j A B =
  Σ[ l₀ ∈ List (OVType Φ × OVType Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {X Y} → (X , Y) ∈ l₀ → Q ∣ X [ δ ]ᵛ <:̂ᵛ Y [ δ ]ᵛ)
       → wkᵉ-H Q ∣ A [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ <:̂ᵛ B [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ)

Atomᵈ : ∀ {Φ} → EVar (Φ +e) → OVType (Φ +e) → RExp (Φ +e) → Set
Atomᵈ {Φ} j A ρ =
  Σ[ l₀ ∈ List (OVType Φ × RExp Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {B τ} → (B , τ) ∈ l₀ → VarOK Q (B [ δ ]ᵛ) (τ [ δ ]ʳ))
       → VarOK (wkᵉ-H Q) (A [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ) (ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ))

-- An eternality demand that reduces to no atom at all. Wrapping the
-- verdict together with its proof keeps the case analysis of `atomᵗ`
-- visible from outside, which is what reasoning about it needs.

et₀? : ∀ {Φ} → (A : OVType Φ) → Maybe ({Q : Hyps Φ} → Q ⊩ᴱ A)
et₀? A with etDec A in e
... | just []      = just (λ {Q} → etDec-sound {Q = Q} A e (λ ()))
... | just (α ∷ _) = nothing
... | nothing      = nothing

-- An ordering with the rigid on one side only holds for every rigid
-- exactly when it holds at the extreme grade on that side, the side
-- being monotone in the rigid:
--
--   ∀j. lhs ≾ rhs(j)  ⟺  lhs ≾ rhs(u)   (`stripᵉ-unit`, the unit least)
--   ∀j. lhs(j) ≾ rhs  ⟺  lhs(⊤) ≾ rhs   (`stripᵉ-top`)
--
-- The rigid is sent to that grade, and what is left is kept. The top is
-- a grade of every monoid, the unit is least only in some, so only the
-- first reads the grade's `uₑ-least?`. An unknown local to the scope stands for a
-- function of the rigid, and is kept at the unit rigid; so the side
-- that `stripᵉ-top` keeps free of the rigid must mention no local
-- unknown either, only those the scope was entered with (`Outerₑ`).

stripʳ-unit : ∀ {Φ} → Maybe (Is-just uₑ-least?)
            → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
            → (ρ₀ : RExp Φ) → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → Maybe (Atomʳ j ρ ρ')
stripʳ-unit nothing    j ρ ρ' ρ₀ e₁ = nothing
stripʳ-unit (just ij)  j ρ ρ' ρ₀ e₁ with strʳ⁺ j (ρ' [ updᵉ j ûₑ ]ʳ)
... | nothing          = nothing
... | just (ρ₀' , e₂) =
      just ((ρ₀ , ρ₀') ∷ [] ,
            λ δ Q k → transᵣ (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
                                     (sym (pop⨟ʳ j ρ e₁ δ))
                                     (trans (sym (pop⨟ʳ j (ρ' [ updᵉ j ûₑ ]ʳ) e₂ δ))
                                            ([⨟]ʳ ρ' (updᵉ j ûₑ) (popˢ j ⨟ˢ (δ ↑ᵉ))))
                                     (⊩-wkᵉᵣ (k (here refl))))
                             (mono-substᵣ (updᵉ-below j ûₑ (popˢ j ⨟ˢ (δ ↑ᵉ)) (minₑ ij)) ρ'))

stripᵉ-unit : ∀ {Φ} → Maybe (Is-just uₑ-least?)
            → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
            → (ε₀ : EExp Φ) → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → Maybe (Atomᵉ j ε ε')
stripᵉ-unit nothing    j ε ε' ε₀ e₁ = nothing
stripᵉ-unit (just ij)  j ε ε' ε₀ e₁ with strᵉ⁺ j (ε' [ updᵉ j ûₑ ]ᵉ)
... | nothing          = nothing
... | just (ε₀' , e₂) =
      just ((ε₀ , ε₀') ∷ [] ,
            λ δ Q k → transₑ (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y)
                                     (sym (pop⨟ᵉ j ε e₁ δ))
                                     (trans (sym (pop⨟ᵉ j (ε' [ updᵉ j ûₑ ]ᵉ) e₂ δ))
                                            ([⨟]ᵉ ε' (updᵉ j ûₑ) (popˢ j ⨟ˢ (δ ↑ᵉ))))
                                     (⊩-wkᵉₑ (k (here refl))))
                             (mono-substₑ (updᵉ-below j ûₑ (popˢ j ⨟ˢ (δ ↑ᵉ)) (minₑ ij)) ε'))

stripʳ-top : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
           → (ρ₀' : RExp Φ) → ρ' [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀' → Maybe (Atomʳ j ρ ρ')
stripʳ-top O j ρ ρ' ρ₀' e₁ with outerᵣ? O ρ' | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ)
... | just _ | just (ρ₀ , e₂) =
      just ((ρ₀ , ρ₀') ∷ [] ,
            λ δ Q k → transᵣ (mono-substᵣ (updᵉ-above j (econst ⊤ₑ) (popˢ j ⨟ˢ (δ ↑ᵉ)) topₑ) ρ)
                             (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
                                     (trans (sym (pop⨟ʳ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ) e₂ δ))
                                            ([⨟]ʳ ρ (updᵉ j (econst ⊤ₑ)) (popˢ j ⨟ˢ (δ ↑ᵉ))))
                                     (sym (pop⨟ʳ j ρ' e₁ δ))
                                     (⊩-wkᵉᵣ (k (here refl)))))
... | _      | _                = nothing

stripᵉ-top : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
           → (ε₀' : EExp Φ) → ε' [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀' → Maybe (Atomᵉ j ε ε')
stripᵉ-top O j ε ε' ε₀' e₁ with outerₑ? O ε' | strᵉ⁺ j (ε [ updᵉ j (econst ⊤ₑ) ]ᵉ)
... | just _ | just (ε₀ , e₂) =
      just ((ε₀ , ε₀') ∷ [] ,
            λ δ Q k → transₑ (mono-substₑ (updᵉ-above j (econst ⊤ₑ) (popˢ j ⨟ˢ (δ ↑ᵉ)) topₑ) ε)
                             (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y)
                                     (trans (sym (pop⨟ᵉ j (ε [ updᵉ j (econst ⊤ₑ) ]ᵉ) e₂ δ))
                                            ([⨟]ᵉ ε (updᵉ j (econst ⊤ₑ)) (popˢ j ⨟ˢ (δ ↑ᵉ))))
                                     (sym (pop⨟ᵉ j ε' e₁ δ))
                                     (⊩-wkᵉₑ (k (here refl)))))
... | _      | _                = nothing

atomʳ : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
      → Maybe (Atomʳ j ρ ρ')
atomʳ O j ρ ρ' with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just (ρ₀ , e₁) | just (ρ₀' , e₂) =
      just ((ρ₀ , ρ₀') ∷ [] ,
            λ δ Q k → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
                             (sym (pop⨟ʳ j ρ e₁ δ)) (sym (pop⨟ʳ j ρ' e₂ δ))
                             (⊩-wkᵉᵣ (k (here refl))))
... | just (ρ₀ , e₁) | nothing          with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
...   | just p  = just ([] , λ δ Q k → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
...   | nothing = stripʳ-unit (Is-just? uₑ-least?) j ρ ρ' ρ₀ e₁
atomʳ O j ρ ρ' | nothing | just (ρ₀' , e₂) with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just p  = just ([] , λ δ Q k → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
... | nothing = stripʳ-top O j ρ ρ' ρ₀' e₂
atomʳ O j ρ ρ' | nothing | nothing with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just p  = just ([] , λ δ Q k → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

atomᵉ : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
      → Maybe (Atomᵉ j ε ε')
atomᵉ O j ε ε' with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just (ε₀ , e₁) | just (ε₀' , e₂) =
      just ((ε₀ , ε₀') ∷ [] ,
            λ δ Q k → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y)
                             (sym (pop⨟ᵉ j ε e₁ δ)) (sym (pop⨟ᵉ j ε' e₂ δ))
                             (⊩-wkᵉₑ (k (here refl))))
... | just (ε₀ , e₁) | nothing          with decide≾ₑ {Q = ∅ᴴ} ε ε'
...   | just p  = just ([] , λ δ Q k → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
...   | nothing = stripᵉ-unit (Is-just? uₑ-least?) j ε ε' ε₀ e₁
atomᵉ O j ε ε' | nothing | just (ε₀' , e₂) with decide≾ₑ {Q = ∅ᴴ} ε ε'
... | just p  = just ([] , λ δ Q k → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
... | nothing = stripᵉ-top O j ε ε' ε₀' e₂
atomᵉ O j ε ε' | nothing | nothing with decide≾ₑ {Q = ∅ᴴ} ε ε'
... | just p  = just ([] , λ δ Q k → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

atomᵗ : ∀ {Φ} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → Maybe (Atomᵗ j A)
atomᵗ j A with strᵛ⁺ j A
... | just (A₀ , e₁) =
      just (A₀ ∷ [] ,
            λ δ Q k → subst (wkᵉ-H Q ⊩ᴱ_) (sym (pop⨟ᵛ j A e₁ δ))
                            (⊩ᴱ-wkᵉ (k (here refl))))
... | nothing with et₀? A
...   | just p  = just ([] , λ δ Q k → ⊩ᴱ-subst ∅ᴴ-⊩ᴴ (p {∅ᴴ}))
...   | nothing = nothing

-- A subtyping demand is kept only when both sides strengthen away
-- from the rigid.

atomˢ : ∀ {Φ} → (j : EVar (Φ +e)) → (A B : OVType (Φ +e)) → Maybe (Atomˢ j A B)
atomˢ j A B with strᵛ⁺ j A | strᵛ⁺ j B
... | just (A₀ , e₁) | just (B₀ , e₂) =
      just ((A₀ , B₀) ∷ [] ,
            λ δ Q k → subst₂ (wkᵉ-H Q ∣_<:̂ᵛ_)
                             (sym (pop⨟ᵛ j A e₁ δ)) (sym (pop⨟ᵛ j B e₂ δ))
                             (<:̂ᵛ-wkᵉ (k (here refl))))
... | just _         | nothing = nothing
... | nothing        | _       = nothing

-- A disjunction is kept when its type and its grade both strengthen
-- away from the rigid. With the rigid in the grade only, it is kept
-- with the rigid at the top: the type does not depend on the rigid and
-- the disjunction is antitone in its grade, so
--
--   ∀j. Et A ∨ ρ(j) ≾ u  ⟺  Et A ∨ ρ(⊤) ≾ u.
--
-- A type mentioning the rigid is declined.

atomᵈ : ∀ {Φ} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → (ρ : RExp (Φ +e))
      → Maybe (Atomᵈ j A ρ)
atomᵈ j A ρ with strᵛ⁺ j A | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ)
... | just (A₀ , e₁) | just (ρ₀ , e₂) =
      just ((A₀ , ρ₀) ∷ [] ,
            λ δ Q k → VarOK-≡̂ (≡̂ᵛ-refl _)
                        (mono-substᵣ (updᵉ-above j (econst ⊤ₑ) (popˢ j ⨟ˢ (δ ↑ᵉ)) topₑ) ρ)
                        (subst₂ (VarOK (wkᵉ-H Q))
                                (sym (pop⨟ᵛ j A e₁ δ))
                                (trans (sym (pop⨟ʳ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ) e₂ δ))
                                       ([⨟]ʳ ρ (updᵉ j (econst ⊤ₑ)) (popˢ j ⨟ˢ (δ ↑ᵉ))))
                                (VarOK-wkᵉ (k (here refl)))))
... | just _         | nothing = nothing
... | nothing        | _       = nothing

-- An ordering no atom step keeps is deferred when it mentions only the
-- rigid and the unknowns the scope was entered with (`O⁺`, the rigid
-- among them), none local to the scope. It is read with the rigid
-- newest, and holds at a substitution lifted over the rigid.

Listʳ : ∀ {Φ} → EVar (Φ +e) → List (RExp (Φ +e) × RExp (Φ +e)) → Set
Listʳ {Φ} j l =
  Σ[ l₀ ∈ List (RExp Φ × RExp Φ) ] Σ[ d₀ ∈ List (RExp (Φ +e) × RExp (Φ +e)) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
       → (∀ {τ τ'} → (τ , τ') ∈ d₀ → wkᵉ-H Q ⊩ τ [ δ ↑ᵉ ]ʳ ≾̂ᵣ τ' [ δ ↑ᵉ ]ʳ)
       → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
            → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ))

Listᵉ : ∀ {Φ} → EVar (Φ +e) → List (EExp (Φ +e) × EExp (Φ +e)) → Set
Listᵉ {Φ} j l =
  Σ[ l₀ ∈ List (EExp Φ × EExp Φ) ] Σ[ d₀ ∈ List (EExp (Φ +e) × EExp (Φ +e)) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ᵉ ≾̂ₑ τ' [ δ ]ᵉ)
       → (∀ {τ τ'} → (τ , τ') ∈ d₀ → wkᵉ-H Q ⊩ τ [ δ ↑ᵉ ]ᵉ ≾̂ₑ τ' [ δ ↑ᵉ ]ᵉ)
       → (∀ {ε ε'} → (ε , ε') ∈ l
            → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ))

listʳ : ∀ {Θ Φ} → Subst Θ (Φ +e) → Subst (Θ +e) (Φ +e) → (j : EVar (Φ +e))
      → (l : List (RExp (Φ +e) × RExp (Φ +e))) → Maybe (Listʳ j l)
listʳ O O⁺ j []              = just ([] , [] , λ δ Q k d → λ ())
listʳ O O⁺ j ((ρ , ρ') ∷ l) with listʳ O O⁺ j l
... | nothing = nothing
... | just (l₀ , d₀ , f) with atomʳ O j ρ ρ'
...   | just (a , fa) =
        just (a ++ l₀ , d₀ ,
              λ δ Q k d → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                            ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) d m })
...   | nothing with outerᵣ? O⁺ ρ | outerᵣ? O⁺ ρ'
...     | just _ | just _ =
          just (l₀ , (ρ [ popˢ j ]ʳ , ρ' [ popˢ j ]ʳ) ∷ d₀ ,
                λ δ Q k d → λ { (here refl) → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
                                                     ([⨟]ʳ ρ (popˢ j) (δ ↑ᵉ))
                                                     ([⨟]ʳ ρ' (popˢ j) (δ ↑ᵉ))
                                                     (d (here refl))
                              ; (there m)   → f δ Q k (λ m' → d (there m')) m })
...     | _      | _      = nothing

listᵉ : ∀ {Θ Φ} → Subst Θ (Φ +e) → Subst (Θ +e) (Φ +e) → (j : EVar (Φ +e))
      → (l : List (EExp (Φ +e) × EExp (Φ +e))) → Maybe (Listᵉ j l)
listᵉ O O⁺ j []              = just ([] , [] , λ δ Q k d → λ ())
listᵉ O O⁺ j ((ε , ε') ∷ l) with listᵉ O O⁺ j l
... | nothing = nothing
... | just (l₀ , d₀ , f) with atomᵉ O j ε ε'
...   | just (a , fa) =
        just (a ++ l₀ , d₀ ,
              λ δ Q k d → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                            ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) d m })
...   | nothing with outerₑ? O⁺ ε | outerₑ? O⁺ ε'
...     | just _ | just _ =
          just (l₀ , (ε [ popˢ j ]ᵉ , ε' [ popˢ j ]ᵉ) ∷ d₀ ,
                λ δ Q k d → λ { (here refl) → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y)
                                                     ([⨟]ᵉ ε (popˢ j) (δ ↑ᵉ))
                                                     ([⨟]ᵉ ε' (popˢ j) (δ ↑ᵉ))
                                                     (d (here refl))
                              ; (there m)   → f δ Q k (λ m' → d (there m')) m })
...     | _      | _      = nothing

listᵗ : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (OVType (Φ +e)))
      → Maybe (Σ[ l₀ ∈ List (OVType Φ) ]
                 (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                    → (∀ {B} → B ∈ l₀ → Q ⊩ᴱ B [ δ ]ᵛ)
                    → (∀ {A} → A ∈ l → wkᵉ-H Q ⊩ᴱ A [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ)))
listᵗ j []      = just ([] , λ δ Q k → λ ())
listᵗ j (A ∷ l) with atomᵗ j A | listᵗ j l
... | just (a , fa) | just (l₀ , f) =
      just (a ++ l₀ ,
            λ δ Q k → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                        ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) m })
... | just _        | nothing = nothing
... | nothing       | _       = nothing

listˢ : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (OVType (Φ +e) × OVType (Φ +e)))
      → Maybe (Σ[ l₀ ∈ List (OVType Φ × OVType Φ) ]
                 (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                    → (∀ {X Y} → (X , Y) ∈ l₀ → Q ∣ X [ δ ]ᵛ <:̂ᵛ Y [ δ ]ᵛ)
                    → (∀ {A B} → (A , B) ∈ l
                         → wkᵉ-H Q ∣ A [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ
                                  <:̂ᵛ B [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ)))
listˢ j []             = just ([] , λ δ Q k → λ ())
listˢ j ((A , B) ∷ l) with atomˢ j A B | listˢ j l
... | just (a , fa) | just (l₀ , f) =
      just (a ++ l₀ ,
            λ δ Q k → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                        ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) m })
... | just _        | nothing = nothing
... | nothing       | _       = nothing

listᵈ : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (OVType (Φ +e) × RExp (Φ +e)))
      → Maybe (Σ[ l₀ ∈ List (OVType Φ × RExp Φ) ]
                 (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                    → (∀ {B τ} → (B , τ) ∈ l₀ → VarOK Q (B [ δ ]ᵛ) (τ [ δ ]ʳ))
                    → (∀ {A ρ} → (A , ρ) ∈ l
                         → VarOK (wkᵉ-H Q) (A [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵛ)
                                           (ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ))))
listᵈ j []             = just ([] , λ δ Q k → λ ())
listᵈ j ((A , ρ) ∷ l) with atomᵈ j A ρ | listᵈ j l
... | just (a , fa) | just (l₀ , f) =
      just (a ++ l₀ ,
            λ δ Q k → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                        ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) m })
... | just _        | nothing = nothing
... | nothing       | _       = nothing

-- An inner entry is carried out under one more binder, the rigid: it
-- must mention no unknown local to the scope

Outerᵒ : ∀ {Θ Φ} → Subst Θ Φ → Ords Φ → Set
Outerᵒ O o = (∀ {a} → a ∈ ors o → Outerᵣ O (proj₁ a) × Outerᵣ O (proj₂ a))
           × (∀ {a} → a ∈ oes o → Outerₑ O (proj₁ a) × Outerₑ O (proj₂ a))

both? : ∀ {A B : Set} → Maybe A → Maybe B → Maybe (A × B)
both? (just a) (just b) = just (a , b)
both? _        _        = nothing

outerᵒ? : ∀ {Θ Φ} → (O : Subst Θ Φ) → (o : Ords Φ) → Maybe (Outerᵒ O o)
outerᵒ? O o = both? (allOf (λ a → both? (outerᵣ? O (proj₁ a)) (outerᵣ? O (proj₂ a))) (ors o))
                    (allOf (λ a → both? (outerₑ? O (proj₁ a)) (outerₑ? O (proj₂ a))) (oes o))

OuterD : ∀ {Θ Φ} → Subst Θ Φ → List (Dfr Φ) → Set
OuterD O D = ∀ {E} → E ∈ D → Outerᵒ (O ↑ᵉⁿ nb E) (body E)

outerD? : ∀ {Θ Φ} → (O : Subst Θ Φ) → (D : List (Dfr Φ)) → Maybe (OuterD O D)
outerD? O = allOf (λ E → outerᵒ? (O ↑ᵉⁿ nb E) (body E))

liftᵈ : ∀ {Φ} → EVar (Φ +e) → Dfr (Φ +e) → Dfr Φ
liftᵈ j E = closeᵈ (E [ popˢ j ]ᵈ)

liftᵈ-sound : ∀ {Φ Φ'} {Q : Hyps Φ'} {δ : Subst Φ Φ'} → (j : EVar (Φ +e)) → (E : Dfr (Φ +e))
            → Q ⊩ᵈ liftᵈ j E [ δ ] → wkᵉ-H Q ⊩ᵈ E [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
liftᵈ-sound j E h = ⊩ᵈ-subst E (closeᵈ-sound (E [ popˢ j ]ᵈ) h)

-- The atoms are split three ways: those strengthened away from the
-- rigid, kept outside; those deferred, one new entry; and the inner
-- entries, each closed over the rigid: bound as a new outermost
-- binder where it occurs. An eternality demand, a subtyping demand or
-- a disjunction that cannot be kept refutes the scope; an ordering
-- that can be neither kept nor deferred, or an inner entry, that
-- mentions an unknown local to the scope leaves it stuck.

splitᴿ : ∀ {Θ Φ} → Subst Θ (Φ +e) → Subst (Θ +e) (Φ +e) → (j : EVar (Φ +e))
       → (R : Resid (Φ +e))
       → Outcome (Σ[ R₀ ∈ Resid Φ ]
                    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                       → Q ⊩ᴿ R₀ [ δ ] → wkᵉ-H Q ⊩ᴿ R [ popˢ j ⨟ˢ (δ ↑ᵉ) ]))
splitᴿ O O⁺ j R with listᵗ j (ts R) | listˢ j (ss R) | listᵈ j (ds R)
                   | listʳ O O⁺ j (rs R) | listᵉ O O⁺ j (es R) | outerD? O⁺ (dfs R)
... | just (lt , ft) | just (ls , fs) | just (ld , fd)
    | just (lr , dr , fr) | just (le , de , fe) | just _ =
      solved (resid lr le lt ls ld (closeᵈ (dfr nothing 0 (ords dr de)) ∷ map (liftᵈ j) (dfs R)) ,
              λ δ Q h → mk⊩ᴿ (fr δ Q (⊩rs h) (⊩ors (new δ Q h)))
                             (fe δ Q (⊩es h) (⊩oes (new δ Q h)))
                             (ft δ Q (⊩ts h)) (fs δ Q (⊩ss h)) (fd δ Q (⊩ds h))
                             (λ m → lifted δ Q h m))
  where
    R₀ = resid lr le lt ls ld (closeᵈ (dfr nothing 0 (ords dr de)) ∷ map (liftᵈ j) (dfs R))

    new : ∀ {Φ'} → (δ : Subst _ Φ') → (Q : Hyps Φ') → Q ⊩ᴿ R₀ [ δ ]
        → wkᵉ-H Q ⊩ᵈ dfr nothing 0 (ords dr de) [ δ ↑ᵉ ]
    new δ Q h = closeᵈ-sound (dfr nothing 0 (ords dr de)) (⊩dfs h (here refl))

    lifted : ∀ {Φ'} → (δ : Subst _ Φ') → (Q : Hyps Φ') → Q ⊩ᴿ R₀ [ δ ]
           → ∀ {E} → E ∈ dfs R → wkᵉ-H Q ⊩ᵈ E [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
    lifted δ Q h {E} m = liftᵈ-sound j E (⊩dfs h (there (∈-map⁺ (liftᵈ j) m)))
... | nothing | _       | _       | _      | _      | _       = refuted
... | just _  | nothing | _       | _      | _      | _       = refuted
... | just _  | just _  | nothing | _      | _      | _       = refuted
... | just _  | just _  | just _  | nothing | _     | _       = stuck
... | just _  | just _  | just _  | just _ | nothing | _      = stuck
... | just _  | just _  | just _  | just _ | just _ | nothing = stuck

threadOps : ∀ {Θ} → {f : Op → Constraint Θ}
          → ((s : St Θ) → (op : Op)
               → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (f op))))
          → (l : List Op) → (s : St Θ)
          → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × AllOp (λ op → Wit s' (f op)) l))
threadOps g []       s = solved (s , ⟶-id , [])
threadOps {f = f} g (op ∷ l) s with g s op
... | refuted = refuted
... | stuck   = stuck
... | solved (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁
...   | refuted = refuted
...   | stuck   = stuck
...   | solved (s₂ , m₂ , ws) = solved (s₂ , ⟶-⨟ m₁ m₂ , wit-mono m₂ (f op) w₁ ∷ ws)

-- The inner store, restricted to the outer unknowns, moves the rigid
-- back to the newest position

pop-key : ∀ {Ψ Φ} → (γ : Subst (Ψ +e) (Φ +e)) → {j : EVar (Φ +e)}
        → sE γ (newᵉ {Ψ}) ≡ evar j → {δ₀ : Subst Ψ Φ}
        → ((wkˢᵉ {Ψ} ⨟ˢ γ) ⨟ˢ popˢ j) ≐ˢ (δ₀ ⨟ˢ wkˢᵉ)
        → (γ ⨟ˢ popˢ j) ≐ˢ (δ₀ ↑ᵉ)
pop-key γ {j} eqj {δ₀} pδ =
  mk≐ˢ (λ α → trans (≐ᵗ pδ α) (wkˢᵉ-v (sTy δ₀ α)))
       (λ i → trans (≐ʳ pδ i) (wkˢᵉ-r (sR δ₀ i)))
       (λ { zero    → trans (cong (_[ popˢ j ]ᵉ) eqj) (popˢ-hit j)
          ; (suc i) → trans (≐ᵉ pδ i) (wkˢᵉ-e (sE δ₀ i)) })

-- Closing the scope: the first two refusals cannot happen, the third
-- is an escape, and the rest are `splitᴿ`'s.

popᵉ : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
     → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
     → (⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → Wit (st Φ θ'' R'' rg'') C
     → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (∀ᵉ C)))
popᵉ s C (scope nt nr nzero)    θ'' R'' rg'' m'' w'' = refuted
popᵉ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w''
  with evar? (sE (mδ m'') (newᵉ {Ψ s}))
... | nothing = refuted
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'')
                        | splitᴿ (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (mδ m'') j R''
...   | just (δ₀ , pδ) | solved (R₀ , tr) =
        solved (st (scope nt nr n) (θ s ⨟ˢ δ₀) (res s [ δ₀ ]ᴿ ∪ᴿ R₀) (transRig δ₀ (rig s)) ,
              mor δ₀ ≐ˢ-refl (λ δ Q h → ⊩ᴿ-subst (∪ᴿ-fst h)) ,
              λ δ Q h → ⊨-resp-≐ˢ (chain δ) C
                          (w'' (popˢ j ⨟ˢ (δ ↑ᵉ)) (wkᵉ-H Q) (tr δ Q (∪ᴿ-snd h))))
        where
          key' : (θ'' ⨟ˢ popˢ j) ≐ˢ ((θ s ⨟ˢ δ₀) ↑ᵉ)
          key' = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m'')) (popˢ j))
                 (≐ˢ-trans (⨟-assoc (θ s ↑ᵉ) (mδ m'') (popˢ j))
                 (≐ˢ-trans (⨟-congʳ (θ s ↑ᵉ) (pop-key (mδ m'') eqj pδ)) (⨟-↑ᵉ (θ s) δ₀)))

          chain : ∀ {Φ'} → (δ : Subst (scope nt nr n) Φ')
                → (θ'' ⨟ˢ (popˢ j ⨟ˢ (δ ↑ᵉ))) ≐ˢ (((θ s ⨟ˢ δ₀) ⨟ˢ δ) ↑ᵉ)
          chain δ = ≐ˢ-trans (≐ˢ-sym (⨟-assoc θ'' (popˢ j) (δ ↑ᵉ)))
                    (≐ˢ-trans (⨟-congˡ key' (δ ↑ᵉ)) (⨟-↑ᵉ (θ s ⨟ˢ δ₀) δ))
...   | just _         | refuted = refuted
...   | just _         | stuck   = stuck
...   | nothing        | _       = refuted

------------------------------------------------------------------------
-- Retrying the deferred conditions
--
-- An ordering of an entry is dropped when `decide≾` derives it, the
-- rigids opaque, from the residual's orderings: a derivation at fresh
-- rigids under the hypotheses weakened to them. It refutes when a
-- closed witness per rigid, the unit or the top, makes it a failing
-- closed ordering. An entry left with no ordering is dropped.

-- The residual's orderings as hypotheses

ordsOf : ∀ {Ψ} → Resid Ψ → Hyps Ψ
ordsOf R = hyps [] [] (rs R) (es R) []

ordsOf-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {δ : Subst Ψ Ψ'}
         → Q ⊩ᴿ R [ δ ] → Q ⊩ᴴ ordsOf R [ δ ]
ordsOf-⊩ h = mk⊩ᴴ (λ ()) (λ ()) (⊩rs h) (⊩es h) (λ ())

-- An ordering of an entry binding `k` rigids, at `δ`

Atʳ : ∀ {Ψ Ψ'} → (k : ℕ) → Hyps Ψ' → Subst Ψ Ψ' → RExp (Ψ +eⁿ k) × RExp (Ψ +eⁿ k) → Set
Atʳ k Q δ (x , y) = wkᵉⁿ-H k Q ⊩ x [ δ ↑ᵉⁿ k ]ʳ ≾̂ᵣ y [ δ ↑ᵉⁿ k ]ʳ

Atᵉ : ∀ {Ψ Ψ'} → (k : ℕ) → Hyps Ψ' → Subst Ψ Ψ' → EExp (Ψ +eⁿ k) × EExp (Ψ +eⁿ k) → Set
Atᵉ k Q δ (x , y) = wkᵉⁿ-H k Q ⊩ x [ δ ↑ᵉⁿ k ]ᵉ ≾̂ₑ y [ δ ↑ᵉⁿ k ]ᵉ

data Verdict {Ψ} {X : Set} (H : Hyps Ψ) (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set)
             (a : X) : Set where
  settled   : (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᴴ H [ δ ] → P Q δ a)
            → Verdict H P a
  refuted   : ((δ : Subst Ψ ∅ˢ) → ¬ P ∅ᴴ δ a) → Verdict H P a
  undecided : Verdict H P a

-- At the witnesses, a closed instance of an entry's ordering is one of
-- the ordering with its rigids instantiated

atWitʳ : ∀ {Ψ} → (k : ℕ) → (cs : List E) → (x y : RExp (Ψ +eⁿ k)) → (δ : Subst Ψ ∅ˢ)
       → Atʳ k ∅ᴴ δ (x , y) → ∅ᴴ ⊩ x [ wit k cs ]ʳ [ δ ]ʳ ≾̂ᵣ y [ wit k cs ]ʳ [ δ ]ʳ
atWitʳ k cs x y δ p =
  subst₂ (λ a b → ∅ᴴ ⊩ a ≾̂ᵣ b) (eq x) (eq y) (⊩-substᵣ (⊩ᴴ-wit k cs) p)
  where
    eq : (z : RExp _) → z [ δ ↑ᵉⁿ k ]ʳ [ wit k cs ]ʳ ≡ z [ wit k cs ]ʳ [ δ ]ʳ
    eq z = trans ([⨟]ʳ z (δ ↑ᵉⁿ k) (wit k cs))
                 (trans ([≐]ʳ (wit-⨟ δ k cs) z) (sym ([⨟]ʳ z (wit k cs) δ)))

atWitᵉ : ∀ {Ψ} → (k : ℕ) → (cs : List E) → (x y : EExp (Ψ +eⁿ k)) → (δ : Subst Ψ ∅ˢ)
       → Atᵉ k ∅ᴴ δ (x , y) → ∅ᴴ ⊩ x [ wit k cs ]ᵉ [ δ ]ᵉ ≾̂ₑ y [ wit k cs ]ᵉ [ δ ]ᵉ
atWitᵉ k cs x y δ p =
  subst₂ (λ a b → ∅ᴴ ⊩ a ≾̂ₑ b) (eq x) (eq y) (⊩-substₑ (⊩ᴴ-wit k cs) p)
  where
    eq : (z : EExp _) → z [ δ ↑ᵉⁿ k ]ᵉ [ wit k cs ]ᵉ ≡ z [ wit k cs ]ᵉ [ δ ]ᵉ
    eq z = trans ([⨟]ᵉ z (δ ↑ᵉⁿ k) (wit k cs))
                 (trans ([≐]ᵉ (wit-⨟ δ k cs) z) (sym ([⨟]ᵉ z (wit k cs) δ)))

witnessʳ : ∀ {Ψ} {H : Hyps Ψ} → (k : ℕ) → (x y : RExp (Ψ +eⁿ k)) → List (List E)
         → Verdict H (Atʳ k) (x , y)
witnessʳ k x y []         = undecided
witnessʳ k x y (cs ∷ css) with valʳ? (x [ wit k cs ]ʳ) in e | valʳ? (y [ wit k cs ]ʳ) in e'
... | just c  | just c' = pick (c ≾ᵣ? c')
  where
    pick : Dec (c ≾ᵣ c') → Verdict _ (Atʳ k) (x , y)
    pick (no ¬le) = refuted (λ δ p → ¬le (closed-≾ᵣ {ρ = x [ wit k cs ]ʳ} {ρ' = y [ wit k cs ]ʳ}
                                               (convʳ _ e) (convʳ _ e') δ (atWitʳ k cs x y δ p)))
    pick (yes _)  = witnessʳ k x y css
... | _       | _       = witnessʳ k x y css

witnessᵉ : ∀ {Ψ} {H : Hyps Ψ} → (k : ℕ) → (x y : EExp (Ψ +eⁿ k)) → List (List E)
         → Verdict H (Atᵉ k) (x , y)
witnessᵉ k x y []         = undecided
witnessᵉ k x y (cs ∷ css) with valᵉ? (x [ wit k cs ]ᵉ) in e | valᵉ? (y [ wit k cs ]ᵉ) in e'
... | just c  | just c' = pick (c ≾ₑ? c')
  where
    pick : Dec (c ≾ₑ c') → Verdict _ (Atᵉ k) (x , y)
    pick (no ¬le) = refuted (λ δ p → ¬le (closed-≾ₑ {ε = x [ wit k cs ]ᵉ} {ε' = y [ wit k cs ]ᵉ}
                                               (convᵉ _ e) (convᵉ _ e') δ (atWitᵉ k cs x y δ p)))
    pick (yes _)  = witnessᵉ k x y css
... | _       | _       = witnessᵉ k x y css

verdictʳ : ∀ {Ψ} → (H : Hyps Ψ) → (k : ℕ) → (a : RExp (Ψ +eⁿ k) × RExp (Ψ +eⁿ k))
         → Verdict H (Atʳ k) a
verdictʳ H k (x , y) with decide≾ᵣ {Q = wkᵉⁿ-H k H} x y
... | just p  = settled (λ δ h → ⊩-substᵣ (⊩ᴴ-↑ᵉⁿ k h) p)
... | nothing = witnessʳ k x y (witnesses k)

verdictᵉ : ∀ {Ψ} → (H : Hyps Ψ) → (k : ℕ) → (a : EExp (Ψ +eⁿ k) × EExp (Ψ +eⁿ k))
         → Verdict H (Atᵉ k) a
verdictᵉ H k (x , y) with decide≾ₑ {Q = wkᵉⁿ-H k H} x y
... | just p  = settled (λ δ h → ⊩-substₑ (⊩ᴴ-↑ᵉⁿ k h) p)
... | nothing = witnessᵉ k x y (witnesses k)

-- The orderings of a list that are not settled, or one refuted

record Sifted {Ψ} {X : Set} (H : Hyps Ψ) (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set)
              (l : List X) : Set where
  constructor sifted
  field
    left  : List X
    left⊆ : ∀ {a} → a ∈ left → a ∈ l
    back  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᴴ H [ δ ]
          → (∀ {a} → a ∈ left → P Q δ a) → ∀ {a} → a ∈ l → P Q δ a

NoWit : ∀ {Ψ} {X : Set} → (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set) → List X → Set
NoWit {Ψ} {X} P l = Σ[ a ∈ X ] ((a ∈ l) × ((δ : Subst Ψ ∅ˢ) → ¬ P ∅ᴴ δ a))

sift : ∀ {Ψ} {X : Set} {H : Hyps Ψ} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
     → ((a : X) → Verdict H P a) → (l : List X) → NoWit P l ⊎ Sifted H P l
sift v []      = inj₂ (sifted [] (λ ()) (λ δ h k → λ ()))
sift v (a ∷ l) with v a | sift v l
... | _           | inj₁ (b , m , r)         = inj₁ (b , there m , r)
... | refuted r   | inj₂ _                   = inj₁ (a , here refl , r)
... | settled p   | inj₂ (sifted l' sb bk) =
      inj₂ (sifted l' (λ m → there (sb m))
                   (λ δ h k → λ { (here refl) → p δ h ; (there m) → bk δ h k m }))
... | undecided   | inj₂ (sifted l' sb bk) =
      inj₂ (sifted (a ∷ l') (λ { (here refl) → here refl ; (there m) → there (sb m) })
                   (λ δ h k → λ { (here refl) → k (here refl)
                                ; (there m)   → bk δ h (λ m' → k (there m')) m }))

-- An entry with no ordering left is dropped

unlessEmpty : ∀ {Ψ} → Maybe Op → (k : ℕ) → Ords (Ψ +eⁿ k) → List (Dfr Ψ)
unlessEmpty l k (ords [] []) = []
unlessEmpty l k o            = dfr l k o ∷ []

unlessEmpty-back : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {l : Maybe Op} {k : ℕ}
                 → (o : Ords (Ψ +eⁿ k))
                 → (∀ {E'} → E' ∈ unlessEmpty l k o → Q ⊩ᵈ E' [ δ ]) → Q ⊩ᵈ dfr l k o [ δ ]
unlessEmpty-back (ords [] [])      f = mk⊩ᵒ (λ ()) (λ ())
unlessEmpty-back (ords (a ∷ r) e)  f = f (here refl)
unlessEmpty-back (ords [] (a ∷ e)) f = f (here refl)

unlessEmpty-fwd : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {l : Maybe Op} {k : ℕ}
                → (o : Ords (Ψ +eⁿ k))
                → Q ⊩ᵈ dfr l k o [ δ ] → ∀ {E'} → E' ∈ unlessEmpty l k o → Q ⊩ᵈ E' [ δ ]
unlessEmpty-fwd (ords [] [])      h ()
unlessEmpty-fwd (ords (a ∷ r) e)  h (here refl) = h
unlessEmpty-fwd (ords [] (a ∷ e)) h (here refl) = h

data Retried {Ψ} (H : Hyps Ψ) (E : Dfr Ψ) : Set where
  refutedᵈ : ((δ : Subst Ψ ∅ˢ) → ¬ (∅ᴴ ⊩ᵈ E [ δ ])) → Retried H E
  keptᵈ    : (D : List (Dfr Ψ))
           → (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᴴ H [ δ ]
                → (∀ {E'} → E' ∈ D → Q ⊩ᵈ E' [ δ ]) → Q ⊩ᵈ E [ δ ])
           → (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᵈ E [ δ ]
                → ∀ {E'} → E' ∈ D → Q ⊩ᵈ E' [ δ ])
           → Retried H E

retryᵈ : ∀ {Ψ} → (H : Hyps Ψ) → (E : Dfr Ψ) → Retried H E
retryᵈ H (dfr l k o) with sift (verdictʳ H k) (ors o) | sift (verdictᵉ H k) (oes o)
... | inj₁ (a , m , r) | _                = refutedᵈ (λ δ h → r δ (⊩ors h m))
... | inj₂ _           | inj₁ (a , m , r) = refutedᵈ (λ δ h → r δ (⊩oes h m))
... | inj₂ (sifted lr sr br) | inj₂ (sifted le se be) =
      keptᵈ (unlessEmpty l k (ords lr le))
            (λ δ h f → let g = unlessEmpty-back (ords lr le) f in
                       mk⊩ᵒ (br δ h (⊩ors g)) (be δ h (⊩oes g)))
            (λ δ h → unlessEmpty-fwd (ords lr le)
                       (mk⊩ᵒ (λ m → ⊩ors h (sr m)) (λ m → ⊩oes h (se m))))

record RetriedL {Ψ} (H : Hyps Ψ) (D : List (Dfr Ψ)) : Set where
  constructor retriedL
  field
    D'    : List (Dfr Ψ)
    backᴰ : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᴴ H [ δ ]
          → (∀ {E} → E ∈ D' → Q ⊩ᵈ E [ δ ]) → ∀ {E} → E ∈ D → Q ⊩ᵈ E [ δ ]
    fwdᴰ  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → (∀ {E} → E ∈ D → Q ⊩ᵈ E [ δ ]) → ∀ {E} → E ∈ D' → Q ⊩ᵈ E [ δ ]

RefutedL : ∀ {Ψ} → List (Dfr Ψ) → Set
RefutedL {Ψ} D = Σ[ E ∈ Dfr Ψ ] ((E ∈ D) × ((δ : Subst Ψ ∅ˢ) → ¬ (∅ᴴ ⊩ᵈ E [ δ ])))

retryᴰ : ∀ {Ψ} → (H : Hyps Ψ) → (D : List (Dfr Ψ)) → RefutedL D ⊎ RetriedL H D
retryᴰ H []      = inj₂ (retriedL [] (λ δ h g → λ ()) (λ δ g → λ ()))
retryᴰ H (E ∷ D) with retryᵈ H E | retryᴰ H D
... | refutedᵈ r     | _                    = inj₁ (E , here refl , r)
... | keptᵈ _ _ _    | inj₁ (E' , m , r)    = inj₁ (E' , there m , r)
... | keptᵈ Dₑ bₑ fₑ | inj₂ (retriedL D' b f) =
      inj₂ (retriedL (Dₑ ++ D')
              (λ δ h g → λ { (here refl) → bₑ δ h (λ m → g (∈-++⁺ˡ m))
                           ; (there m)   → b δ h (λ m' → g (∈-++⁺ʳ Dₑ m')) m })
              (λ δ g m → [ fₑ δ (g (here refl)) , f δ (λ m' → g (there m')) ]′ (∈-++⁻ Dₑ m)))

-- A residual with its deferred conditions replaced

withDfs : ∀ {Ψ} → Resid Ψ → List (Dfr Ψ) → Resid Ψ
withDfs R D = resid (rs R) (es R) (ts R) (ss R) (ds R) D

retry : ∀ {Θ} → (s : St Θ) → Maybe (Σ[ s' ∈ St Θ ] (s ⟶ s'))
retry s with retryᴰ (ordsOf (res s)) (dfs (res s))
... | inj₁ _                 = nothing
... | inj₂ (retriedL D' b f) =
      just (st (Ψ s) (θ s) (withDfs (res s) D') (rig s) ,
            mor idˢ (⨟-idʳ (θ s))
                (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ))
                             (mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h)
                                   (b δ (ordsOf-⊩ h) (⊩dfs h)))))

-- A scope's close, then a retry

thenRetry : ∀ {Θ} {s : St Θ} {C : Constraint Θ}
          → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C))
          → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C))
thenRetry refuted = refuted
thenRetry stuck   = stuck
thenRetry {C = C} (solved (s₁ , m₁ , w₁)) with retry s₁
... | nothing        = refuted
... | just (s₂ , m₂) = solved (s₂ , ⟶-⨟ m₁ m₂ , wit-mono m₂ C w₁)

-- The entries a clause leaves carry its operation

relabel : ∀ {Ψ} → Op → Dfr Ψ → Dfr Ψ
relabel op (dfr nothing  k o) = dfr (just op) k o
relabel op (dfr (just l) k o) = dfr (just l) k o

relabel-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (op : Op) → (E : Dfr Ψ)
          → Q ⊩ᵈ relabel op E [ δ ] → Q ⊩ᵈ E [ δ ]
relabel-⊩ op (dfr nothing  k o) h = h
relabel-⊩ op (dfr (just l) k o) h = h

labelled : ∀ {Θ} {s : St Θ} {C : Constraint Θ} → Op
         → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C))
         → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C))
labelled op refuted = refuted
labelled op stuck   = stuck
labelled {C = C} op (solved (s₁ , m₁ , w₁)) =
  solved (s₂ , ⟶-⨟ m₁ m₂ , wit-mono m₂ C w₁)
  where
    s₂ = st (Ψ s₁) (θ s₁) (withDfs (res s₁) (map (relabel op) (dfs (res s₁)))) (rig s₁)

    m₂ : s₁ ⟶ s₂
    m₂ = mor idˢ (⨟-idʳ (θ s₁))
             (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ))
                          (mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h)
                                (λ {E} m → relabel-⊩ op E (⊩dfs h (∈-map⁺ (relabel op) m)))))

-- Before a rigid scope closes, the atoms decided true are dropped, and
-- the unknowns local to it are sent to their principal values: those
-- free in no image of the unknowns the scope was entered with.

localiseˢ : ∀ {Θ} → (s : St Θ) → {s'' : St (Θ +e)} → ⇑ᵉˢ s ⟶ s''
          → Σ[ s₃ ∈ St (Θ +e) ] (s'' ⟶ s₃)
localiseˢ s {s''} m =
  st (Ψ s'') (θ s'' ⨟ˢ lσ L) (lR L) (rig s'') , mor (lσ L) ≐ˢ-refl (lsnd L)
  where
    L : Localised (mδ m) (res s'')
    L = localise (mδ m) (res s'')

-- The unifier's verdict, paired with the equation naming it, so
-- that the driver's own case analysis stays visible to a proof.

unifyAt : ∀ {Θ} → (rg : Rig Θ) → (es : Eqns Θ)
        → (x : Maybe (Σ[ Θ⁺ ∈ Scope ] AList Θ Θ⁺)) → unify rg es ≡ x
        → Maybe (Σ[ Θ⁺ ∈ Scope ] Σ[ ρ ∈ AList Θ Θ⁺ ] (unify rg es ≡ just (Θ⁺ , ρ)))
unifyAt rg es nothing         equ = nothing
unifyAt rg es (just (Θ⁺ , ρ)) equ = just (Θ⁺ , ρ , equ)

unify* : ∀ {Θ} → (rg : Rig Θ) → (es : Eqns Θ)
       → Maybe (Σ[ Θ⁺ ∈ Scope ] Σ[ ρ ∈ AList Θ Θ⁺ ] (unify rg es ≡ just (Θ⁺ , ρ)))
unify* rg es = unifyAt rg es (unify rg es) refl

unifyAt-nothing : ∀ {Θ} → (rg : Rig Θ) → (es : Eqns Θ)
                → (x : Maybe (Σ[ Θ⁺ ∈ Scope ] AList Θ Θ⁺)) → (equ : unify rg es ≡ x)
                → unifyAt rg es x equ ≡ nothing → unify rg es ≡ nothing
unifyAt-nothing rg es nothing  equ q = equ
unifyAt-nothing rg es (just _) equ ()

unify*-nothing : ∀ {Θ} → (rg : Rig Θ) → (es : Eqns Θ)
               → unify* rg es ≡ nothing → unify rg es ≡ nothing
unify*-nothing rg es q = unifyAt-nothing rg es (unify rg es) refl q

chain₂ᵛ : ∀ {Θ Ψ Ψ₁ Ψ₂} → (X : OVType Θ) → (σ : Subst Θ Ψ) → (δ : Subst Ψ Ψ₁)
        → (δ' : Subst Ψ₁ Ψ₂) → X [ σ ]ᵛ [ δ ]ᵛ [ δ' ]ᵛ ≡ X [ (σ ⨟ˢ δ) ⨟ˢ δ' ]ᵛ
chain₂ᵛ X σ δ δ' = trans (cong (_[ δ' ]ᵛ) ([⨟]ᵛ X σ δ)) ([⨟]ᵛ X (σ ⨟ˢ δ) δ')

-- Reading a residual back as a hypothesis set asks every subtyping
-- demand to decompose; one expansion of what is left, and the
-- decomposition that follows it, make it so.

reexpand : ∀ {Θ} → (s : St Θ) → Maybe (Σ[ s' ∈ St Θ ] (s ⟶ s'))
reexpand s with expandSub (ss (res s))
... | nothing       = nothing
... | just (Ψ' , δ) with subsList (ss (res s [ δ ]ᴿ))
...   | nothing = nothing
...   | just e  =
        just (st Ψ' (θ s ⨟ˢ δ) (atomiseᴿ (res s [ δ ]ᴿ) e) (transRig δ (rig s)) ,
              mor δ ≐ˢ-refl (λ δ' Q h → ⊩ᴿ-subst (atomiseᴿ-sound _ e h)))

solve : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ)
      → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C))

solve s ⊤̂ = solved (s , ⟶-id , λ δ Q h → tt)

solve s ⊥̂ = refuted

solve s (C ∧̂ D) with solve s C
... | refuted = refuted
... | stuck   = stuck
... | solved (s₁ , m₁ , w₁) with solve s₁ D
...   | refuted = refuted
...   | stuck   = stuck
...   | solved (s₂ , m₂ , w₂) =
        solved (s₂ , ⟶-⨟ m₁ m₂ , λ δ Q h → wit-mono m₂ C w₁ δ Q h , w₂ δ Q h)

solve s (A ≐ᵥ B) with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
... | nothing = refuted
... | just (Ψ⁺ , ρ , equ) with expandSub (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ))
...   | nothing = refuted
...   | just (Ψ' , δ) with subsList (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ))
...     | nothing = refuted
...     | just e =
        solved (st Ψ' (θ s ⨟ˢ ⟦ ρ ⟧ᴬ ⨟ˢ δ) (atomiseᴿ (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ) e)
                 (transRig δ (transRig ⟦ ρ ⟧ᴬ (rig s))) ,
              mor (⟦ ρ ⟧ᴬ ⨟ˢ δ) (≐ˢ-sym (⨟-assoc (θ s) ⟦ ρ ⟧ᴬ δ))
                  (λ δ' Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc ⟦ ρ ⟧ᴬ δ δ'))
                                          (⊩ᴿ-subst (⊩ᴿ-subst (atomiseᴿ-sound _ e h)))) ,
              λ δ' Q h → trans (sym (chain₂ᵛ A (θ s ⨟ˢ ⟦ ρ ⟧ᴬ) δ δ'))
                         (trans (cong (λ X → X [ δ ]ᵛ [ δ' ]ᵛ) pinned)
                                (chain₂ᵛ B (θ s ⨟ˢ ⟦ ρ ⟧ᴬ) δ δ')))
        where
          pinned : A [ θ s ⨟ˢ ⟦ ρ ⟧ᴬ ]ᵛ ≡ B [ θ s ⨟ˢ ⟦ ρ ⟧ᴬ ]ᵛ
          pinned = trans (sym ([⨟]ᵛ A (θ s) ⟦ ρ ⟧ᴬ))
                   (trans (proj₁ (unify-sound (rig s)
                                              (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) equ))
                          ([⨟]ᵛ B (θ s) ⟦ ρ ⟧ᴬ))

solve s (A ≾̂ᵥᶜ B) with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
... | nothing        = refuted
... | just (Ψ' , δ) with subDec (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ)
...   | nothing = refuted
...   | just d  with subsList (ss (res s [ δ ]ᴿ))
...     | nothing = refuted
...     | just e  =
        solved (st Ψ' (θ s ⨟ˢ δ) (atomiseᴿ (res s [ δ ]ᴿ) e ∪ᴿ atomsᴿ (atomsOf d))
                 (transRig δ (rig s)) ,
              mor δ ≐ˢ-refl (λ δ' Q h → ⊩ᴿ-subst (atomiseᴿ-sound _ e (∪ᴿ-fst h))) ,
              λ δ' Q h → subst₂ (Q ∣_<:̂ᵛ_) (chain₂ᵛ A (θ s) δ δ') (chain₂ᵛ B (θ s) δ δ')
                                (intro d δ' (holdsᴿ (atomsOf d) (∪ᴿ-snd h))))

solve s (ρ ≾̂ᵣᶜ ρ') =
  solved (st (Ψ s) (θ s) (pushʳ (ρ [ θ s ]ʳ) (ρ' [ θ s ]ʳ) (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailʳ h)) ,
        λ δ Q h → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y)
                         ([⨟]ʳ ρ (θ s) δ) ([⨟]ʳ ρ' (θ s) δ) (⊩rs h (here refl)))

solve s (ε ≾̂ₑᶜ ε') =
  solved (st (Ψ s) (θ s) (pushᵉ (ε [ θ s ]ᵉ) (ε' [ θ s ]ᵉ) (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵉ h)) ,
        λ δ Q h → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y)
                         ([⨟]ᵉ ε (θ s) δ) ([⨟]ᵉ ε' (θ s) δ) (⊩es h (here refl)))

solve s (Etᶜ A) =
  solved (st (Ψ s) (θ s) (pushᵗ (A [ θ s ]ᵛ) (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵗ h)) ,
        λ δ Q h → subst (Q ⊩ᴱ_) ([⨟]ᵛ A (θ s) δ) (⊩ts h (here refl)))

solve s (Et∨≾ᵘ A ρ) with decide≾ᵣ {Q = ∅ᴴ} (ρ [ θ s ]ʳ) ûᵣ
... | just p =
      solved (s , ⟶-id ,
            λ δ Q h → ≾ᵘ-ok (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([⨟]ʳ ρ (θ s) δ)
                                   (⊩-substᵣ ∅ᴴ-⊩ᴴ p)))
... | nothing =
      solved (st (Ψ s) (θ s) (pushᵈ (A [ θ s ]ᵛ) (ρ [ θ s ]ʳ) (res s)) (rig s) ,
            mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵈ h)) ,
            λ δ Q h → subst₂ (VarOK Q) ([⨟]ᵛ A (θ s) δ) ([⨟]ʳ ρ (θ s) δ)
                             (⊩ds h (here refl)))

solve {Θ} s (∃ᵗ C) with solve (s ↑ᵗˢ) C
... | refuted = refuted
... | stuck   = stuck
... | solved (s'' , m'' , w'') =
      solved (st (Ψ s'') (wkˢᵗ {Θ} ⨟ˢ θ s'') (res s'') (rig s'') ,
            mor (wkˢᵗ {Ψ s} ⨟ˢ mδ m'')
                (≐ˢ-trans (≐ˢ-sym (⨟-assoc (θ s) (wkˢᵗ {Ψ s}) (mδ m'')))
                 (≐ˢ-trans (⨟-congˡ (≐ˢ-sym (wkˢᵗ-↑ᵗ (θ s))) (mδ m''))
                 (≐ˢ-trans (⨟-assoc (wkˢᵗ {Θ}) (θ s ↑ᵗ) (mδ m''))
                           (⨟-congʳ (wkˢᵗ {Θ}) (mtri m'')))))
                (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc (wkˢᵗ {Ψ s}) (mδ m'') δ))
                                       (⊩ᴿ-subst (mres m'' δ Q h))) ,
            λ δ Q h → sTy (θ s'' ⨟ˢ δ) (newᵗ {Θ}) ,
                      ⊨-resp-≐ˢ (≐ˢ-sym (≐ˢ-trans
                                  (≐ˢ-,ᵗ (⨟-assoc (wkˢᵗ {Θ}) (θ s'') δ) _)
                                  (↑-,ᵗ (θ s'' ⨟ˢ δ))))
                                C (w'' δ Q h))

solve {Θ} s (∃ʳ C) with solve (s ↑ʳˢ) C
... | refuted = refuted
... | stuck   = stuck
... | solved (s'' , m'' , w'') =
      solved (st (Ψ s'') (wkˢʳ {Θ} ⨟ˢ θ s'') (res s'') (rig s'') ,
            mor (wkˢʳ {Ψ s} ⨟ˢ mδ m'')
                (≐ˢ-trans (≐ˢ-sym (⨟-assoc (θ s) (wkˢʳ {Ψ s}) (mδ m'')))
                 (≐ˢ-trans (⨟-congˡ (≐ˢ-sym (wkˢʳ-↑ʳ (θ s))) (mδ m''))
                 (≐ˢ-trans (⨟-assoc (wkˢʳ {Θ}) (θ s ↑ʳ) (mδ m''))
                           (⨟-congʳ (wkˢʳ {Θ}) (mtri m'')))))
                (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc (wkˢʳ {Ψ s}) (mδ m'') δ))
                                       (⊩ᴿ-subst (mres m'' δ Q h))) ,
            λ δ Q h → sR (θ s'' ⨟ˢ δ) (newʳ {Θ}) ,
                      ⊨-resp-≐ˢ (≐ˢ-sym (≐ˢ-trans
                                  (≐ˢ-,ʳ (⨟-assoc (wkˢʳ {Θ}) (θ s'') δ) _)
                                  (↑-,ʳ (θ s'' ⨟ˢ δ))))
                                C (w'' δ Q h))

solve {Θ} s (∃ᵉ C) with solve (s ↑ᵉˢ) C
... | refuted = refuted
... | stuck   = stuck
... | solved (s'' , m'' , w'') =
      solved (st (Ψ s'') (wkˢᵉ {Θ} ⨟ˢ θ s'') (res s'') (rig s'') ,
            mor (wkˢᵉ {Ψ s} ⨟ˢ mδ m'')
                (≐ˢ-trans (≐ˢ-sym (⨟-assoc (θ s) (wkˢᵉ {Ψ s}) (mδ m'')))
                 (≐ˢ-trans (⨟-congˡ (≐ˢ-sym (wkˢᵉ-↑ᵉ (θ s))) (mδ m''))
                 (≐ˢ-trans (⨟-assoc (wkˢᵉ {Θ}) (θ s ↑ᵉ) (mδ m''))
                           (⨟-congʳ (wkˢᵉ {Θ}) (mtri m'')))))
                (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc (wkˢᵉ {Ψ s}) (mδ m'') δ))
                                       (⊩ᴿ-subst (mres m'' δ Q h))) ,
            λ δ Q h → sE (θ s'' ⨟ˢ δ) (newᵉ {Θ}) ,
                      ⊨-resp-≐ˢ (≐ˢ-sym (≐ˢ-trans
                                  (≐ˢ-,ᵉ (⨟-assoc (wkˢᵉ {Θ}) (θ s'') δ) _)
                                  (↑-,ᵉ (θ s'' ⨟ˢ δ))))
                                C (w'' δ Q h))

solve s (∀ᵉ C) with solve (⇑ᵉˢ s) C
... | refuted = refuted
... | stuck   = stuck
... | solved (s'' , m'' , w'') with reexpand s''
...   | nothing = refuted
...   | just (s₃ , m₃) = thenRetry {C = ∀ᵉ C} (
        popᵉ s C (Ψ (proj₁ (localiseˢ s m₃'))) (θ (proj₁ (localiseˢ s m₃')))
                 (res (proj₁ (localiseˢ s m₃'))) (rig (proj₁ (localiseˢ s m₃')))
                 (⟶-⨟ m₃' (proj₂ (localiseˢ s m₃')))
                 (wit-mono (proj₂ (localiseˢ s m₃')) C (wit-mono m₃ C w'')))
  where
    m₃' = ⟶-⨟ m'' m₃

solve s (⋀ᵒᵖ f) with threadOps {f = f} (λ s' op → labelled {C = f op} op (solve s' (f op))) ops s
... | refuted = refuted
... | stuck   = stuck
... | solved (s' , m , ws) =
      solved (s' , m , λ δ Q h op → all-lookup ws (complete op) δ Q h)
