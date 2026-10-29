------------------------------------------------------------------
-- The solver driver                                            --
--                                                              --
-- The driver traverses a constraint, threading a state. A      --
-- subtyping atom is expanded and decomposed at matching        --
-- formers and residualised at a pair of type variables; grade  --
-- orderings are residualised; binders extend the state. A type --
-- equation is the pair of its subtyping atoms                  --
-- (`Constraints.Syntax`) and has no case of its own. An        --
-- eternality demand is decided by `etDec` when it is pushed:   --
-- it is refuted, or residualised as its atoms on type          --
-- variables (`solveEt`). A var-rule disjunction is dropped     --
-- where its grade is below the unit at the strength `full`     --
-- from no hypotheses; otherwise its type is decided: if never  --
-- eternal, the grade side is residualised as an ordering; if   --
-- eternal with no atom, the disjunction is dropped; otherwise  --
-- it is residualised (`solveDisj`). An expansion of the type   --
-- unknowns is followed by a second decomposition of the      --
-- residual's subtyping and eternality demands, which puts them --
-- on type variables and residualises their grade orderings     --
-- with the others.                                             --
--                                                              --
-- The witness of a success is deferred: it is read at the      --
-- state that a later component leaves, not transported along   --
-- it.                                                          --
--                                                              --
-- At a rigid binder the state is extended with a fresh         --
-- residual. Before the scope closes, its subtyping demands are --
-- expanded and its demands decomposed again (`reexpand`), the  --
-- atoms decided true are dropped, and the unknowns local to    --
-- the scope are assigned values that keep every instance       --
-- entering it (`Localise`). Then an atom free of the rigid is  --
-- kept; one that mentions the rigid is discharged where it     --
-- follows, at the strength `full`, from the orderings free of  --
-- the rigid; otherwise one whose right side alone mentions the --
-- rigid is kept at the unit rigid where the unit is least, one --
-- whose left side alone mentions it is kept at the top rigid,  --
-- and any other, when it mentions only the rigid and outer     --
-- unknowns, is deferred as a new entry. The                    --
-- scope's own entries are carried outward under the rigid, and --
-- the image of an outer unknown must remain free of it. After  --
-- each close the entries are retried.                          --
--                                                              --
-- The outcome is a solution, a refutation, or `stuck`: a close --
-- at which an atom that is neither kept nor deferred, or an    --
-- inner entry, mentions an unknown local to the scope.         --
--                                                              --
-- Contract. A solution carries its witness `Wit s' C`: every   --
-- instance discharging the new residual solves `C` (soundness, --
-- by construction, each move being a `_⟶_`). Every instance    --
-- that solves `C` from no hypotheses and discharges the old    --
-- residual factors through the new state and discharges its    --
-- residual, the rigids remaining variables (`solve-principal`, --
-- `PrincipalSolution`). A refutation leaves no instance that   --
-- solves `C`, discharges the residual and keeps the rigids     --
-- distinct variables (`solve-fail`). `stuck` carries no claim; --
-- it does not occur without a rigid binder (`solve-rigidFree`, --
-- `RigidFree`).                                                --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just; to-witness)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to Any-just)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_; Dec; yes; no)


open import Grades.Base
open import Grades.Hints using (SystemHints; module SystemHintsInterface)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.Outcome

open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Inference.SolverImpl.Solve
  (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S))
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open SystemHintsInterface hints
open Operations Ops

open import OpenCalculus.Syntax.Grades S
open import OpenCalculus.Syntax.Types  S
open import OpenCalculus.Syntax.GradeSubstitution S
open import OpenCalculus.Hypotheses   S
open import OpenCalculus.Hypotheses.Instances S
  using (closed-≾ᵣ; closed-≾ₑ)

open import OpenCalculus.Inference.Constraints.Syntax       S
open import OpenCalculus.Inference.Constraints.Satisfaction S
open import OpenCalculus.Inference.Constraints.Properties   S using (⊨-resp-≐ˢ)

open import OpenCalculus.Inference.SolverImpl.Enum S using (AllOp; []; _∷_; all-lookup)

open import OpenCalculus.Inference.SolverImpl.Core.Occurs   S using (occᵉ-e; occᵉ-r; occʳ-r)
open import OpenCalculus.Inference.SolverImpl.Core.Decorate S using (expandSub)
open import OpenCalculus.Inference.SolverImpl.Core.Rigid    S

open import OpenCalculus.Inference.SolverImpl.Deferred S hints
open import OpenCalculus.Inference.SolverImpl.Resid  S
open import OpenCalculus.Inference.SolverImpl.State  S
open import OpenCalculus.Inference.SolverImpl.Normal S hints
open import OpenCalculus.Inference.SolverImpl.Entail S hints
  using (decideᵣ; decideₑ; derive; full; closedᵣ?; closedₑ?; holdsᵣ; failsᵣ; holdsₑ; failsₑ)
open import OpenCalculus.Inference.SolverImpl.Localise S hints
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
-- hypotheses transports to any instance of them.

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

Stripʳ : ∀ {Φ} → EVar (Φ +e) → RExp (Φ +e) → RExp (Φ +e) → Set
Stripʳ {Φ} j ρ ρ' =
  Σ[ l₀ ∈ List (RExp Φ × RExp Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
       → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ)

Stripᵉ : ∀ {Φ} → EVar (Φ +e) → EExp (Φ +e) → EExp (Φ +e) → Set
Stripᵉ {Φ} j ε ε' =
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
-- Right to left is each rule's type (`Stripʳ`/`Stripᵉ`); left to right
-- is `stripʳ-unit-princ` and its siblings (`PrincipalSolution`).

stripʳ-unit : ∀ {Φ} → Maybe (Is-just uₑ-least?)
            → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
            → (ρ₀ : RExp Φ) → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → Maybe (Stripʳ j ρ ρ')
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
                             (mono-substᵣ (updᵉ-below j ûₑ (popˢ j ⨟ˢ (δ ↑ᵉ)) (minₑ (to-witness ij))) ρ'))

stripᵉ-unit : ∀ {Φ} → Maybe (Is-just uₑ-least?)
            → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
            → (ε₀ : EExp Φ) → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → Maybe (Stripᵉ j ε ε')
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
                             (mono-substₑ (updᵉ-below j ûₑ (popˢ j ⨟ˢ (δ ↑ᵉ)) (minₑ (to-witness ij))) ε'))

stripʳ-top : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
           → (ρ₀' : RExp Φ) → ρ' [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀' → Maybe (Stripʳ j ρ ρ')
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
           → (ε₀' : EExp Φ) → ε' [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀' → Maybe (Stripᵉ j ε ε')
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

-- An ordering that mentions the rigid is discharged where it follows,
-- at the strength `full`, from the hypotheses `H`, the orderings of the
-- scope free of the rigid; otherwise it is kept as `stripʳ-unit` or
-- `stripʳ-top` keeps it. The discharge holds for every rigid, the
-- hypotheses not mentioning it.

Atomʳ : ∀ {Φ} → EVar (Φ +e) → Hyps (Φ +e) → RExp (Φ +e) → RExp (Φ +e) → Set
Atomʳ {Φ} j H ρ ρ' =
  Σ[ l₀ ∈ List (RExp Φ × RExp Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → wkᵉ-H Q ⊩ᴴ H [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
       → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
       → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ)

Atomᵉ : ∀ {Φ} → EVar (Φ +e) → Hyps (Φ +e) → EExp (Φ +e) → EExp (Φ +e) → Set
Atomᵉ {Φ} j H ε ε' =
  Σ[ l₀ ∈ List (EExp Φ × EExp Φ) ]
    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
       → wkᵉ-H Q ⊩ᴴ H [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
       → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ᵉ ≾̂ₑ τ' [ δ ]ᵉ)
       → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ)

fromStripʳ : ∀ {Φ} {j : EVar (Φ +e)} {H : Hyps (Φ +e)} {ρ ρ' : RExp (Φ +e)} → Maybe (Stripʳ j ρ ρ') → Maybe (Atomʳ j H ρ ρ')
fromStripʳ (just (l₀ , f)) = just (l₀ , λ δ Q _ k → f δ Q k)
fromStripʳ nothing         = nothing

fromStripᵉ : ∀ {Φ} {j : EVar (Φ +e)} {H : Hyps (Φ +e)} {ε ε' : EExp (Φ +e)} → Maybe (Stripᵉ j ε ε') → Maybe (Atomᵉ j H ε ε')
fromStripᵉ (just (l₀ , f)) = just (l₀ , λ δ Q _ k → f δ Q k)
fromStripᵉ nothing         = nothing

atomʳ : ∀ {Θ Φ} → Subst Θ (Φ +e) → (H : Hyps (Φ +e)) → (j : EVar (Φ +e))
      → (ρ ρ' : RExp (Φ +e)) → Maybe (Atomʳ j H ρ ρ')
atomʳ O H j ρ ρ' with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just _         | just _           = nothing
... | just (ρ₀ , e₁) | nothing          with decideᵣ full H ρ ρ'
...   | just p  = just ([] , λ δ Q g k → ⊩-substᵣ g p)
...   | nothing = fromStripʳ {j = j} {H = H} {ρ = ρ} {ρ' = ρ'} (stripʳ-unit (Is-just? uₑ-least?) j ρ ρ' ρ₀ e₁)
atomʳ O H j ρ ρ' | nothing | just (ρ₀' , e₂) with decideᵣ full H ρ ρ'
... | just p  = just ([] , λ δ Q g k → ⊩-substᵣ g p)
... | nothing = fromStripʳ {j = j} {H = H} {ρ = ρ} {ρ' = ρ'} (stripʳ-top O j ρ ρ' ρ₀' e₂)
atomʳ O H j ρ ρ' | nothing | nothing with decideᵣ full H ρ ρ'
... | just p  = just ([] , λ δ Q g k → ⊩-substᵣ g p)
... | nothing = nothing

atomᵉ : ∀ {Θ Φ} → Subst Θ (Φ +e) → (H : Hyps (Φ +e)) → (j : EVar (Φ +e))
      → (ε ε' : EExp (Φ +e)) → Maybe (Atomᵉ j H ε ε')
atomᵉ O H j ε ε' with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just _         | just _           = nothing
... | just (ε₀ , e₁) | nothing          with decideₑ full H ε ε'
...   | just p  = just ([] , λ δ Q g k → ⊩-substₑ g p)
...   | nothing = fromStripᵉ {j = j} {H = H} {ε = ε} {ε' = ε'} (stripᵉ-unit (Is-just? uₑ-least?) j ε ε' ε₀ e₁)
atomᵉ O H j ε ε' | nothing | just (ε₀' , e₂) with decideₑ full H ε ε'
... | just p  = just ([] , λ δ Q g k → ⊩-substₑ g p)
... | nothing = fromStripᵉ {j = j} {H = H} {ε = ε} {ε' = ε'} (stripᵉ-top O j ε ε' ε₀' e₂)
atomᵉ O H j ε ε' | nothing | nothing with decideₑ full H ε ε'
... | just p  = just ([] , λ δ Q g k → ⊩-substₑ g p)
... | nothing = nothing

-- Whether an ordering is free of the rigid

freeʳ? : ∀ {Φ} → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
       → Dec (Is-just (strʳ⁺ j ρ) × Is-just (strʳ⁺ j ρ'))
freeʳ? j ρ ρ' with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just _  | just _  = yes (Any-just tt , Any-just tt)
... | just _  | nothing = no (λ { (_ , ()) })
... | nothing | _       = no (λ { (() , _) })

freeᵉ? : ∀ {Φ} → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
       → Dec (Is-just (strᵉ⁺ j ε) × Is-just (strᵉ⁺ j ε'))
freeᵉ? j ε ε' with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just _  | just _  = yes (Any-just tt , Any-just tt)
... | just _  | nothing = no (λ { (_ , ()) })
... | nothing | _       = no (λ { (() , _) })

-- The orderings of a list free of the rigid

freesʳ : ∀ {Φ} → EVar (Φ +e) → List (RExp (Φ +e) × RExp (Φ +e)) → List (RExp (Φ +e) × RExp (Φ +e))
freesʳ j []             = []
freesʳ j ((x , y) ∷ l) with freeʳ? j x y
... | yes _ = (x , y) ∷ freesʳ j l
... | no _  = freesʳ j l

freesᵉ : ∀ {Φ} → EVar (Φ +e) → List (EExp (Φ +e) × EExp (Φ +e)) → List (EExp (Φ +e) × EExp (Φ +e))
freesᵉ j []             = []
freesᵉ j ((x , y) ∷ l) with freeᵉ? j x y
... | yes _ = (x , y) ∷ freesᵉ j l
... | no _  = freesᵉ j l

freesʳ-∈ : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (RExp (Φ +e) × RExp (Φ +e)))
         → ∀ {ρ ρ'} → (ρ , ρ') ∈ freesʳ j l
         → ((ρ , ρ') ∈ l) × (Is-just (strʳ⁺ j ρ) × Is-just (strʳ⁺ j ρ'))
freesʳ-∈ j ((x , y) ∷ l) m with freeʳ? j x y
freesʳ-∈ j ((x , y) ∷ l) (here refl) | yes fr = here refl , fr
freesʳ-∈ j ((x , y) ∷ l) (there m)   | yes _  =
  there (proj₁ (freesʳ-∈ j l m)) , proj₂ (freesʳ-∈ j l m)
freesʳ-∈ j ((x , y) ∷ l) m           | no _   =
  there (proj₁ (freesʳ-∈ j l m)) , proj₂ (freesʳ-∈ j l m)

freesᵉ-∈ : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (EExp (Φ +e) × EExp (Φ +e)))
         → ∀ {ε ε'} → (ε , ε') ∈ freesᵉ j l
         → ((ε , ε') ∈ l) × (Is-just (strᵉ⁺ j ε) × Is-just (strᵉ⁺ j ε'))
freesᵉ-∈ j ((x , y) ∷ l) m with freeᵉ? j x y
freesᵉ-∈ j ((x , y) ∷ l) (here refl) | yes fr = here refl , fr
freesᵉ-∈ j ((x , y) ∷ l) (there m)   | yes _  =
  there (proj₁ (freesᵉ-∈ j l m)) , proj₂ (freesᵉ-∈ j l m)
freesᵉ-∈ j ((x , y) ∷ l) m           | no _   =
  there (proj₁ (freesᵉ-∈ j l m)) , proj₂ (freesᵉ-∈ j l m)

-- The orderings of a residual free of the rigid, as hypotheses

freeᴴ : ∀ {Φ} → EVar (Φ +e) → Resid (Φ +e) → Hyps (Φ +e)
freeᴴ j R = hyps [] [] (freesʳ j (rs R)) (freesᵉ j (es R)) [] []

-- An eternality demand is kept when its type strengthens away from the
-- rigid. A type that does not mentions a grade, so is eternal at no
-- instance (`atomᵗ-fail`).

atomᵗ : ∀ {Φ} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → Maybe (Atomᵗ j A)
atomᵗ j A with strᵛ⁺ j A
... | just (A₀ , e₁) =
      just (A₀ ∷ [] ,
            λ δ Q k → subst (wkᵉ-H Q ⊩ᴱ_) (sym (pop⨟ᵛ j A e₁ δ))
                            (⊩ᴱ-wkᵉ (k (here refl))))
... | nothing = nothing

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

-- An ordering free of the rigid is kept; one that mentions it is
-- decided by `atomʳ`. An ordering neither kept nor discharged is
-- deferred when it mentions only the rigid and the unknowns the scope
-- was entered with (`O⁺`, the rigid among them), none local to the
-- scope. It is read with the rigid newest, and holds at a substitution
-- lifted over the rigid. The orderings free of the rigid hold from
-- those kept alone.

Listʳ : ∀ {Φ} → EVar (Φ +e) → Hyps (Φ +e) → List (RExp (Φ +e) × RExp (Φ +e)) → Set
Listʳ {Φ} j H l =
  Σ[ l₀ ∈ List (RExp Φ × RExp Φ) ] Σ[ d₀ ∈ List (RExp (Φ +e) × RExp (Φ +e)) ]
    ((∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
        → wkᵉ-H Q ⊩ᴴ H [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
        → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
        → (∀ {τ τ'} → (τ , τ') ∈ d₀ → wkᵉ-H Q ⊩ τ [ δ ↑ᵉ ]ʳ ≾̂ᵣ τ' [ δ ↑ᵉ ]ʳ)
        → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
             → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ))
    × (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
        → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
        → ∀ {ρ ρ'} → (ρ , ρ') ∈ l → Is-just (strʳ⁺ j ρ) × Is-just (strʳ⁺ j ρ')
        → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ))

Listᵉ : ∀ {Φ} → EVar (Φ +e) → Hyps (Φ +e) → List (EExp (Φ +e) × EExp (Φ +e)) → Set
Listᵉ {Φ} j H l =
  Σ[ l₀ ∈ List (EExp Φ × EExp Φ) ] Σ[ d₀ ∈ List (EExp (Φ +e) × EExp (Φ +e)) ]
    ((∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
        → wkᵉ-H Q ⊩ᴴ H [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
        → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ᵉ ≾̂ₑ τ' [ δ ]ᵉ)
        → (∀ {τ τ'} → (τ , τ') ∈ d₀ → wkᵉ-H Q ⊩ τ [ δ ↑ᵉ ]ᵉ ≾̂ₑ τ' [ δ ↑ᵉ ]ᵉ)
        → (∀ {ε ε'} → (ε , ε') ∈ l
             → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ))
    × (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
        → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ᵉ ≾̂ₑ τ' [ δ ]ᵉ)
        → ∀ {ε ε'} → (ε , ε') ∈ l → Is-just (strᵉ⁺ j ε) × Is-just (strᵉ⁺ j ε')
        → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ))

-- A kept ordering free of the rigid holds where its strengthening does

keptʳ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e)) → {ρ₀ ρ₀' : RExp Φ}
      → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → ρ' [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀'
      → (δ : Subst Φ Φ') → (Q : Hyps Φ') → Q ⊩ ρ₀ [ δ ]ʳ ≾̂ᵣ ρ₀' [ δ ]ʳ
      → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ
keptʳ j ρ ρ' e₁ e₂ δ Q p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (sym (pop⨟ʳ j ρ e₁ δ)) (sym (pop⨟ʳ j ρ' e₂ δ)) (⊩-wkᵉᵣ p)

keptᵉ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e)) → {ε₀ ε₀' : EExp Φ}
      → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → ε' [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀'
      → (δ : Subst Φ Φ') → (Q : Hyps Φ') → Q ⊩ ε₀ [ δ ]ᵉ ≾̂ₑ ε₀' [ δ ]ᵉ
      → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ
keptᵉ j ε ε' e₁ e₂ δ Q p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (sym (pop⨟ᵉ j ε e₁ δ)) (sym (pop⨟ᵉ j ε' e₂ δ)) (⊩-wkᵉₑ p)

listʳ : ∀ {Θ Φ} → Subst Θ (Φ +e) → Subst (Θ +e) (Φ +e) → (H : Hyps (Φ +e)) → (j : EVar (Φ +e))
      → (l : List (RExp (Φ +e) × RExp (Φ +e))) → Maybe (Listʳ j H l)
listʳ O O⁺ H j []              = just ([] , [] , (λ δ Q g k d → λ ()) , (λ δ Q k → λ ()))
listʳ O O⁺ H j ((ρ , ρ') ∷ l) with listʳ O O⁺ H j l
... | nothing = nothing
... | just (l₀ , d₀ , f , g) with freeʳ? j ρ ρ'
...   | yes (a , b) =
        just ((proj₁ (to-witness a) , proj₁ (to-witness b)) ∷ l₀ , d₀ ,
              (λ δ Q h k d → λ { (here refl) → keptʳ j ρ ρ' (proj₂ (to-witness a)) (proj₂ (to-witness b)) δ Q
                                                     (k (here refl))
                               ; (there m)   → f δ Q h (λ m' → k (there m')) d m }) ,
              (λ δ Q k → λ { (here refl) _ → keptʳ j ρ ρ' (proj₂ (to-witness a)) (proj₂ (to-witness b)) δ Q
                                                     (k (here refl))
                           ; (there m)   fr → g δ Q (λ m' → k (there m')) m fr }))
...   | no nf with atomʳ O H j ρ ρ'
...     | just (a , fa) =
          just (a ++ l₀ , d₀ ,
                (λ δ Q h k d → λ { (here refl) → fa δ Q h (λ m → k (∈-++⁺ˡ m))
                                 ; (there m)   → f δ Q h (λ m' → k (∈-++⁺ʳ a m')) d m }) ,
                (λ δ Q k → λ { (here refl) fr → ⊥-elim (nf fr)
                             ; (there m)   fr → g δ Q (λ m' → k (∈-++⁺ʳ a m')) m fr }))
...     | nothing with outerᵣ? O⁺ ρ | outerᵣ? O⁺ ρ'
...       | just _ | just _ =
            just (l₀ , (ρ [ popˢ j ]ʳ , ρ' [ popˢ j ]ʳ) ∷ d₀ ,
                  (λ δ Q h k d → λ { (here refl) → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
                                                          ([⨟]ʳ ρ (popˢ j) (δ ↑ᵉ))
                                                          ([⨟]ʳ ρ' (popˢ j) (δ ↑ᵉ))
                                                          (d (here refl))
                                   ; (there m)   → f δ Q h k (λ m' → d (there m')) m }) ,
                  (λ δ Q k → λ { (here refl) fr → ⊥-elim (nf fr)
                               ; (there m)   fr → g δ Q k m fr }))
...       | _      | _      = nothing

listᵉ : ∀ {Θ Φ} → Subst Θ (Φ +e) → Subst (Θ +e) (Φ +e) → (H : Hyps (Φ +e)) → (j : EVar (Φ +e))
      → (l : List (EExp (Φ +e) × EExp (Φ +e))) → Maybe (Listᵉ j H l)
listᵉ O O⁺ H j []              = just ([] , [] , (λ δ Q g k d → λ ()) , (λ δ Q k → λ ()))
listᵉ O O⁺ H j ((ε , ε') ∷ l) with listᵉ O O⁺ H j l
... | nothing = nothing
... | just (l₀ , d₀ , f , g) with freeᵉ? j ε ε'
...   | yes (a , b) =
        just ((proj₁ (to-witness a) , proj₁ (to-witness b)) ∷ l₀ , d₀ ,
              (λ δ Q h k d → λ { (here refl) → keptᵉ j ε ε' (proj₂ (to-witness a)) (proj₂ (to-witness b)) δ Q
                                                     (k (here refl))
                               ; (there m)   → f δ Q h (λ m' → k (there m')) d m }) ,
              (λ δ Q k → λ { (here refl) _ → keptᵉ j ε ε' (proj₂ (to-witness a)) (proj₂ (to-witness b)) δ Q
                                                     (k (here refl))
                           ; (there m)   fr → g δ Q (λ m' → k (there m')) m fr }))
...   | no nf with atomᵉ O H j ε ε'
...     | just (a , fa) =
          just (a ++ l₀ , d₀ ,
                (λ δ Q h k d → λ { (here refl) → fa δ Q h (λ m → k (∈-++⁺ˡ m))
                                 ; (there m)   → f δ Q h (λ m' → k (∈-++⁺ʳ a m')) d m }) ,
                (λ δ Q k → λ { (here refl) fr → ⊥-elim (nf fr)
                             ; (there m)   fr → g δ Q (λ m' → k (∈-++⁺ʳ a m')) m fr }))
...     | nothing with outerₑ? O⁺ ε | outerₑ? O⁺ ε'
...       | just _ | just _ =
            just (l₀ , (ε [ popˢ j ]ᵉ , ε' [ popˢ j ]ᵉ) ∷ d₀ ,
                  (λ δ Q h k d → λ { (here refl) → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y)
                                                          ([⨟]ᵉ ε (popˢ j) (δ ↑ᵉ))
                                                          ([⨟]ᵉ ε' (popˢ j) (δ ↑ᵉ))
                                                          (d (here refl))
                                   ; (there m)   → f δ Q h k (λ m' → d (there m')) m }) ,
                  (λ δ Q k → λ { (here refl) fr → ⊥-elim (nf fr)
                               ; (there m)   fr → g δ Q k m fr }))
...       | _      | _      = nothing

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

OuterD : ∀ {Θ Φ} → Subst Θ Φ → List (QOrd Φ) → Set
OuterD O D = ∀ {E} → E ∈ D → Outerᵒ (O ↑ᵉⁿ rigids E) (body E)

outerD? : ∀ {Θ Φ} → (O : Subst Θ Φ) → (D : List (QOrd Φ)) → Maybe (OuterD O D)
outerD? O = allOf (λ E → outerᵒ? (O ↑ᵉⁿ rigids E) (body E))

liftᵈ : ∀ {Φ} → EVar (Φ +e) → QOrd (Φ +e) → QOrd Φ
liftᵈ j E = closeᵈ (E [ popˢ j ]ᵠ)

liftᵈ-sound : ∀ {Φ Φ'} {Q : Hyps Φ'} {δ : Subst Φ Φ'} → (j : EVar (Φ +e)) → (E : QOrd (Φ +e))
            → Q ⊩ᴼ liftᵈ j E [ δ ] → wkᵉ-H Q ⊩ᴼ E [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
liftᵈ-sound j E h = ⊩ᴼ-subst E (closeᵈ-sound (E [ popˢ j ]ᵠ) h)

-- The atoms are split three ways: those strengthened away from the
-- rigid, kept outside; those deferred, one new entry; and the inner
-- entries, each closed over the rigid: bound as a new outermost
-- binder where it occurs. An eternality demand, a subtyping demand or
-- a disjunction that cannot be kept refutes the scope; an ordering
-- that can be neither kept nor deferred, or an inner entry, that
-- mentions an unknown local to the scope leaves it stuck. What is kept
-- and deferred entails the scope's residual at a fresh rigid (its
-- type), is met by every instance entering the scope (`splitᴿ-princ`),
-- and a refusal is met by none (`splitᴿ-fail`).

splitᴿ : ∀ {Θ Φ} → Subst Θ (Φ +e) → Subst (Θ +e) (Φ +e) → (j : EVar (Φ +e))
       → (R : Resid (Φ +e))
       → Outcome (Σ[ R₀ ∈ Resid Φ ]
                    (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                       → Q ⊩ᴿ R₀ [ δ ] → wkᵉ-H Q ⊩ᴿ R [ popˢ j ⨟ˢ (δ ↑ᵉ) ]))
splitᴿ O O⁺ j R with listᵗ j (ts R) | listˢ j (ss R) | listᵈ j (ds R)
                   | listʳ O O⁺ (freeᴴ j R) j (rs R) | listᵉ O O⁺ (freeᴴ j R) j (es R)
                   | outerD? O⁺ (dfs R)
... | just (lt , ft) | just (ls , fs) | just (ld , fd)
    | just (lr , dr , fr , gr) | just (le , de , fe , ge) | just _ =
      solved (resid lr le lt ls ld (closeᵈ (qord nothing 0 (ords dr de)) ∷ map (liftᵈ j) (dfs R)) ,
              λ δ Q h → mk⊩ᴿ (fr δ Q (free δ Q h) (⊩rs h) (⊩ors (new δ Q h)))
                             (fe δ Q (free δ Q h) (⊩es h) (⊩oes (new δ Q h)))
                             (ft δ Q (⊩ts h)) (fs δ Q (⊩ss h)) (fd δ Q (⊩ds h))
                             (λ m → lifted δ Q h m))
  where
    R₀ = resid lr le lt ls ld (closeᵈ (qord nothing 0 (ords dr de)) ∷ map (liftᵈ j) (dfs R))

    new : ∀ {Φ'} → (δ : Subst _ Φ') → (Q : Hyps Φ') → Q ⊩ᴿ R₀ [ δ ]
        → wkᵉ-H Q ⊩ᴼ qord nothing 0 (ords dr de) [ δ ↑ᵉ ]
    new δ Q h = closeᵈ-sound (qord nothing 0 (ords dr de)) (⊩dfs h (here refl))

    free : ∀ {Φ'} → (δ : Subst _ Φ') → (Q : Hyps Φ') → Q ⊩ᴿ R₀ [ δ ]
         → wkᵉ-H Q ⊩ᴴ freeᴴ j R [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
    free δ Q h =
      mk⊩ᴴ (λ ()) (λ ())
           (λ m → gr δ Q (⊩rs h) (proj₁ (freesʳ-∈ j (rs R) m)) (proj₂ (freesʳ-∈ j (rs R) m)))
           (λ m → ge δ Q (⊩es h) (proj₁ (freesᵉ-∈ j (es R) m)) (proj₂ (freesᵉ-∈ j (es R) m)))
           (λ ()) (λ ())

    lifted : ∀ {Φ'} → (δ : Subst _ Φ') → (Q : Hyps Φ') → Q ⊩ᴿ R₀ [ δ ]
           → ∀ {E} → E ∈ dfs R → wkᵉ-H Q ⊩ᴼ E [ popˢ j ⨟ˢ (δ ↑ᵉ) ]
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
-- is an escape, and the rest are `splitᴿ`'s. Every instance entering
-- the scope factors through the closed state (`popᵉ-princ`); an escape
-- refutes every instance keeping the rigid an eigenvariable
-- (`popᵉ-escape`, `strSub-escape`), and so does every refusal
-- (`popᵉ-fail`).

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
-- An ordering of an entry is dropped when it is decided at the
-- strength `full`, the rigids opaque, from the residual's
-- orderings: a derivation at fresh rigids under the hypotheses
-- weakened to them. It refutes when a closed witness per rigid makes it
-- an ordering that fails at the strength `closed`, each rigid ranging
-- over the unit, the top and the grade system's candidates for the
-- ordering's degree and constants (`candidatesᵣ`, `candidatesₑ`). An
-- entry left with no ordering is dropped.
-- A retry keeps every instance (`retry-princ`), and a refusal refutes
-- every one (`retry-fail`). An entry kept claims nothing: with a rigid
-- on both sides, the witnesses decide nothing in general.

-- The residual's orderings as hypotheses

ordsOf : ∀ {Ψ} → Resid Ψ → Hyps Ψ
ordsOf R = hyps [] [] (rs R) (es R) [] []

ordsOf-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {δ : Subst Ψ Ψ'}
         → Q ⊩ᴿ R [ δ ] → Q ⊩ᴴ ordsOf R [ δ ]
ordsOf-⊩ h = mk⊩ᴴ (λ ()) (λ ()) (⊩rs h) (⊩es h) (λ ()) (λ ())

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
witnessʳ k x y (cs ∷ css) with closedᵣ? (x [ wit k cs ]ʳ) (y [ wit k cs ]ʳ)
... | just (failsᵣ n) = refuted (λ δ p → n δ (atWitʳ k cs x y δ p))
... | _               = witnessʳ k x y css

witnessᵉ : ∀ {Ψ} {H : Hyps Ψ} → (k : ℕ) → (x y : EExp (Ψ +eⁿ k)) → List (List E)
         → Verdict H (Atᵉ k) (x , y)
witnessᵉ k x y []         = undecided
witnessᵉ k x y (cs ∷ css) with closedₑ? (x [ wit k cs ]ᵉ) (y [ wit k cs ]ᵉ)
... | just (failsₑ n) = refuted (λ δ p → n δ (atWitᵉ k cs x y δ p))
... | _               = witnessᵉ k x y css

verdictʳ : ∀ {Ψ} → (H : Hyps Ψ) → (k : ℕ) → (a : RExp (Ψ +eⁿ k) × RExp (Ψ +eⁿ k))
         → Verdict H (Atʳ k) a
verdictʳ H k (x , y) with decideᵣ full (wkᵉⁿ-H k H) x y
... | just p  = settled (λ δ h → ⊩-substᵣ (⊩ᴴ-↑ᵉⁿ k h) p)
... | nothing = witnessʳ k x y (grid (candidatesᵣ x y) k)

verdictᵉ : ∀ {Ψ} → (H : Hyps Ψ) → (k : ℕ) → (a : EExp (Ψ +eⁿ k) × EExp (Ψ +eⁿ k))
         → Verdict H (Atᵉ k) a
verdictᵉ H k (x , y) with decideₑ full (wkᵉⁿ-H k H) x y
... | just p  = settled (λ δ h → ⊩-substₑ (⊩ᴴ-↑ᵉⁿ k h) p)
... | nothing = witnessᵉ k x y (grid (candidatesₑ x y) k)

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

unlessEmpty : ∀ {Ψ} → Maybe Op → (k : ℕ) → Ords (Ψ +eⁿ k) → List (QOrd Ψ)
unlessEmpty l k (ords [] []) = []
unlessEmpty l k o            = qord l k o ∷ []

unlessEmpty-back : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {l : Maybe Op} {k : ℕ}
                 → (o : Ords (Ψ +eⁿ k))
                 → (∀ {E'} → E' ∈ unlessEmpty l k o → Q ⊩ᴼ E' [ δ ]) → Q ⊩ᴼ qord l k o [ δ ]
unlessEmpty-back (ords [] [])      f = mk⊩ᵒ (λ ()) (λ ())
unlessEmpty-back (ords (a ∷ r) e)  f = f (here refl)
unlessEmpty-back (ords [] (a ∷ e)) f = f (here refl)

unlessEmpty-fwd : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {l : Maybe Op} {k : ℕ}
                → (o : Ords (Ψ +eⁿ k))
                → Q ⊩ᴼ qord l k o [ δ ] → ∀ {E'} → E' ∈ unlessEmpty l k o → Q ⊩ᴼ E' [ δ ]
unlessEmpty-fwd (ords [] [])      h ()
unlessEmpty-fwd (ords (a ∷ r) e)  h (here refl) = h
unlessEmpty-fwd (ords [] (a ∷ e)) h (here refl) = h

data Retried {Ψ} (H : Hyps Ψ) (E : QOrd Ψ) : Set where
  refutedᵈ : ((δ : Subst Ψ ∅ˢ) → ¬ (∅ᴴ ⊩ᴼ E [ δ ])) → Retried H E
  keptᵈ    : (D : List (QOrd Ψ))
           → (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᴴ H [ δ ]
                → (∀ {E'} → E' ∈ D → Q ⊩ᴼ E' [ δ ]) → Q ⊩ᴼ E [ δ ])
           → (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᴼ E [ δ ]
                → ∀ {E'} → E' ∈ D → Q ⊩ᴼ E' [ δ ])
           → Retried H E

retryᵈ : ∀ {Ψ} → (H : Hyps Ψ) → (E : QOrd Ψ) → Retried H E
retryᵈ H (qord l k o) with sift (verdictʳ H k) (ors o) | sift (verdictᵉ H k) (oes o)
... | inj₁ (a , m , r) | _                = refutedᵈ (λ δ h → r δ (⊩ors h m))
... | inj₂ _           | inj₁ (a , m , r) = refutedᵈ (λ δ h → r δ (⊩oes h m))
... | inj₂ (sifted lr sr br) | inj₂ (sifted le se be) =
      keptᵈ (unlessEmpty l k (ords lr le))
            (λ δ h f → let g = unlessEmpty-back (ords lr le) f in
                       mk⊩ᵒ (br δ h (⊩ors g)) (be δ h (⊩oes g)))
            (λ δ h → unlessEmpty-fwd (ords lr le)
                       (mk⊩ᵒ (λ m → ⊩ors h (sr m)) (λ m → ⊩oes h (se m))))

record RetriedL {Ψ} (H : Hyps Ψ) (D : List (QOrd Ψ)) : Set where
  constructor retriedL
  field
    D'    : List (QOrd Ψ)
    backᴰ : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ⊩ᴴ H [ δ ]
          → (∀ {E} → E ∈ D' → Q ⊩ᴼ E [ δ ]) → ∀ {E} → E ∈ D → Q ⊩ᴼ E [ δ ]
    fwdᴰ  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → (∀ {E} → E ∈ D → Q ⊩ᴼ E [ δ ]) → ∀ {E} → E ∈ D' → Q ⊩ᴼ E [ δ ]

RefutedL : ∀ {Ψ} → List (QOrd Ψ) → Set
RefutedL {Ψ} D = Σ[ E ∈ QOrd Ψ ] ((E ∈ D) × ((δ : Subst Ψ ∅ˢ) → ¬ (∅ᴴ ⊩ᴼ E [ δ ])))

retryᴰ : ∀ {Ψ} → (H : Hyps Ψ) → (D : List (QOrd Ψ)) → RefutedL D ⊎ RetriedL H D
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

withDfs : ∀ {Ψ} → Resid Ψ → List (QOrd Ψ) → Resid Ψ
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

relabel : ∀ {Ψ} → Op → QOrd Ψ → QOrd Ψ
relabel op (qord nothing  k o) = qord (just op) k o
relabel op (qord (just l) k o) = qord (just l) k o

relabel-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (op : Op) → (E : QOrd Ψ)
          → Q ⊩ᴼ relabel op E [ δ ] → Q ⊩ᴼ E [ δ ]
relabel-⊩ op (qord nothing  k o) h = h
relabel-⊩ op (qord (just l) k o) h = h

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
-- the unknowns local to it, those free in no image of the unknowns the
-- scope was entered with, are sent to values that keep every instance
-- entering the scope (`localise-princ`, `PrincipalSolution`).

localiseˢ : ∀ {Θ} → (s : St Θ) → {s'' : St (Θ +e)} → ⇑ᵉˢ s ⟶ s''
          → Σ[ s₃ ∈ St (Θ +e) ] (s'' ⟶ s₃)
localiseˢ {Θ} s {s''} m = localised (localise (mδ m) (res s''))
  where
    -- The state the localisation leaves
    localised : Localised (mδ m) (res s'') → Σ[ s₃ ∈ St (Θ +e) ] (s'' ⟶ s₃)
    localised L = st (Ψ s'') (θ s'' ⨟ˢ lσ L) (lR L) (rig s'') , mor (lσ L) ≐ˢ-refl (lsnd L)

-- The scope closed at the state the localisation leaves

closeᵉ : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e)) → {s₃ : St (Θ +e)}
       → (m : ⇑ᵉˢ s ⟶ s₃) → Wit s₃ C → Σ[ s₄ ∈ St (Θ +e) ] (s₃ ⟶ s₄)
       → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (∀ᵉ C)))
closeᵉ s C m w (s₄ , m₄) = popᵉ s C (Ψ s₄) (θ s₄) (res s₄) (rig s₄) (⟶-⨟ m m₄) (wit-mono m₄ C w)

chain₂ᵛ : ∀ {Θ Ψ Ψ₁ Ψ₂} → (X : OVType Θ) → (σ : Subst Θ Ψ) → (δ : Subst Ψ Ψ₁)
        → (δ' : Subst Ψ₁ Ψ₂) → X [ σ ]ᵛ [ δ ]ᵛ [ δ' ]ᵛ ≡ X [ (σ ⨟ˢ δ) ⨟ˢ δ' ]ᵛ
chain₂ᵛ X σ δ δ' = trans (cong (_[ δ' ]ᵛ) ([⨟]ᵛ X σ δ)) ([⨟]ᵛ X (σ ⨟ˢ δ) δ')

-- Reading a residual back as a hypothesis set asks every subtyping
-- demand to decompose; one expansion of what is left, and the
-- decomposition that follows it, make it so (`reexpand-dec`,
-- `reexpand-atomic`). Every instance factors through it
-- (`reexpand-princ`), and a failure refutes every instance
-- (`reexpand-fail`).

reexpand : ∀ {Θ} → (s : St Θ) → Maybe (Σ[ s' ∈ St Θ ] (s ⟶ s'))
reexpand s with expandSub (ss (res s))
... | nothing       = nothing
... | just (Ψ' , δ) with subsList (ss (res s [ δ ]ᴿ)) | etsDec (ts (res s [ δ ]ᴿ))
...   | nothing | _       = nothing
...   | just _  | nothing = nothing
...   | just e  | just t  =
        just (st Ψ' (θ s ⨟ˢ δ) (atomiseᴿ (res s [ δ ]ᴿ) e t) (transRig δ (rig s)) ,
              mor δ ≐ˢ-refl (λ δ' Q h → ⊩ᴿ-subst (atomiseᴿ-sound _ e t h)))

-- An eternality demand is decided by `etDec` when it is pushed: it is
-- refuted, or its atoms on type variables are pushed. The verdict is
-- passed with the equation naming it.

solveEt : ∀ {Θ} → (s : St Θ) → (A : OVType Θ)
        → (x : Maybe (List (TyVar (Ψ s)))) → etDec (A [ θ s ]ᵛ) ≡ x
        → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (Etᶜ A)))
solveEt s A nothing   e = refuted
solveEt s A (just αs) e =
  solved (st (Ψ s) (θ s) (pushᵗ αs (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵗ h)) ,
        λ δ Q h → subst (Q ⊩ᴱ_) ([⨟]ᵛ A (θ s) δ)
                        (etDec-intro (A [ θ s ]ᵛ) e δ
                                     (λ m → ⊩ts h (∈-++⁺ˡ (∈-map⁺ tvar m)))))

-- A var-rule disjunction whose grade is not decided below the unit has
-- its type decided likewise: never eternal, its grade side is pushed;
-- eternal with no atom, it is dropped; otherwise it is pushed.

solveDisj : ∀ {Θ} → (s : St Θ) → (A : OVType Θ) → (ρ : RExp Θ)
          → (x : Maybe (List (TyVar (Ψ s)))) → etDec (A [ θ s ]ᵛ) ≡ x
          → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (Et∨≾ᵘ A ρ)))
solveDisj s A ρ nothing       e =
  solved (st (Ψ s) (θ s) (pushʳ (ρ [ θ s ]ʳ) ûᵣ (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailʳ h)) ,
        λ δ Q h → ≾ᵘ-ok (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([⨟]ʳ ρ (θ s) δ) (⊩rs h (here refl))))
solveDisj s A ρ (just [])     e =
  solved (s , ⟶-id ,
        λ δ Q h → et-ok (subst (Q ⊩ᴱ_) ([⨟]ᵛ A (θ s) δ)
                               (etDec-intro (A [ θ s ]ᵛ) e δ (λ ()))))
solveDisj s A ρ (just (_ ∷ _)) e =
  solved (st (Ψ s) (θ s) (pushᵈ (A [ θ s ]ᵛ) (ρ [ θ s ]ʳ) (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵈ h)) ,
        λ δ Q h → subst₂ (VarOK Q) ([⨟]ᵛ A (θ s) δ) ([⨟]ʳ ρ (θ s) δ) (⊩ds h (here refl)))

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

solve s (A ≾̂ᵥᶜ B) with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
... | nothing        = refuted
... | just (Ψ' , δ) with subDec (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ)
...   | nothing = refuted
...   | just d  with subsList (ss (res s [ δ ]ᴿ)) | etsDec (ts (res s [ δ ]ᴿ))
...     | nothing | _       = refuted
...     | just _  | nothing = refuted
...     | just e  | just t  =
        solved (st Ψ' (θ s ⨟ˢ δ) (atomiseᴿ (res s [ δ ]ᴿ) e t ∪ᴿ atomsᴿ (atomsOf d))
                 (transRig δ (rig s)) ,
              mor δ ≐ˢ-refl (λ δ' Q h → ⊩ᴿ-subst (atomiseᴿ-sound _ e t (∪ᴿ-fst h))) ,
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

solve s (Etᶜ A) = solveEt s A (etDec (A [ θ s ]ᵛ)) refl

solve s (Et∨≾ᵘ A ρ) with decideᵣ full ∅ᴴ (ρ [ θ s ]ʳ) ûᵣ
... | just p =
      solved (s , ⟶-id ,
            λ δ Q h → ≾ᵘ-ok (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([⨟]ʳ ρ (θ s) δ)
                                   (⊩-substᵣ ∅ᴴ-⊩ᴴ p)))
... | nothing = solveDisj s A ρ (etDec (A [ θ s ]ᵛ)) refl

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
...   | just (s₃ , m₃) = thenRetry {C = ∀ᵉ C} (closeᵉ s C m₃' (wit-mono m₃ C w'') (localiseˢ s m₃'))
  where
    m₃' = ⟶-⨟ m'' m₃

solve s (⋀ᵒᵖ f) with threadOps {f = f} (λ s' op → labelled {C = f op} op (solve s' (f op))) ops s
... | refuted = refuted
... | stuck   = stuck
... | solved (s' , m , ws) =
      solved (s' , m , λ δ Q h op → all-lookup ws (complete op) δ Q h)
