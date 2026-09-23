------------------------------------------------------------------
-- The solver driver                                            --
--                                                              --
-- Walks a constraint, threading a state: type equations go to  --
-- the unification core, a subtyping atom is decomposed at      --
-- matching formers and residualised at a pair of type          --
-- variables, grade orderings, eternality demands and var-rule  --
-- disjunctions are residualised, and binders lift the state.   --
--                                                              --
-- A successful witness is deferred, re-read at the state a     --
-- later component leaves behind rather than transported along  --
-- it.                                                          --
--                                                              --
-- At a rigid binder the state is lifted with a fresh residual. --
-- Before the scope closes, the var-rule disjunctions with a    --
-- side decided true are dropped and the unknowns local to the  --
-- scope are sent to their principal values (`Localise`); then  --
-- atoms free of the rigid are kept, one whose right side alone --
-- mentions it is kept at the unit rigid where the unit is      --
-- least, one whose left side alone mentions it is kept at the  --
-- top rigid, any other is discharged on the spot, and an outer --
-- unknown's image must stay free of the rigid.                 --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)


open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Solve
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
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
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ)

open import TypeInference.SolverImpl.Enum S using (AllOp; []; _∷_; all-lookup)

open import TypeInference.SolverImpl.Core.AList      S
open import TypeInference.SolverImpl.Core.Occurs     S using (occᵉ-e; occᵉ-r; occʳ-r)
open import TypeInference.SolverImpl.Core.Decorate   S using (expandSub)
open import TypeInference.SolverImpl.Core.Eqn        S
open import TypeInference.SolverImpl.Core.Rigid      S
open import TypeInference.SolverImpl.Core.Unify      S
open import TypeInference.SolverImpl.Core.UnifySound S using (unify-sound)

open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.State  S
open import TypeInference.SolverImpl.Normal S umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Localise S umin?ᵣ umin?ₑ
  using (Localised; localise; lσ; lR; lsnd; freeᵉ; freeʳ)

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
-- first needs `UnitMin`. An unknown local to the scope stands for a
-- function of the rigid, and is kept at the unit rigid; so the side
-- that `stripᵉ-top` keeps free of the rigid must mention no local
-- unknown either, only those the scope was entered with (`O`).

Outerₑ : ∀ {Θ Φ} → Subst Θ Φ → EExp Φ → Set
Outerₑ O ε = ∀ {k} → occᵉ-e k ε ≡ true → freeᵉ k O ≡ true

Outerᵣ : ∀ {Θ Φ} → Subst Θ Φ → RExp Φ → Set
Outerᵣ O ρ = (∀ {k} → occᵉ-r k ρ ≡ true → freeᵉ k O ≡ true)
           × (∀ {k} → occʳ-r k ρ ≡ true → freeʳ k O ≡ true)

∨-elim : ∀ {P : Set} {b b' : 𝔹} → (b ≡ true → P) → (b' ≡ true → P) → b ∨ b' ≡ true → P
∨-elim {b = b} {b'} f g q with ∨-true b b' q
... | inj₁ r = f r
... | inj₂ r = g r

outerₑ? : ∀ {Θ Φ} → (O : Subst Θ Φ) → (ε : EExp Φ) → Maybe (Outerₑ O ε)
outerₑ? O (evar i) with freeᵉ i O in q
... | true  = just (λ {k} r → subst (λ x → freeᵉ x O ≡ true) (sym (true-dec (k ≟ᶠ i) r)) q)
... | false = nothing
outerₑ? O (econst c) = just (λ ())
outerₑ? O (ε ·̂ₑ ε') with outerₑ? O ε | outerₑ? O ε'
... | just f | just g = just (∨-elim f g)
... | _      | _      = nothing
outerₑ? O (ε ⊔̂ₑ ε') with outerₑ? O ε | outerₑ? O ε'
... | just f | just g = just (∨-elim f g)
... | _      | _      = nothing

outerᵣ? : ∀ {Θ Φ} → (O : Subst Θ Φ) → (ρ : RExp Φ) → Maybe (Outerᵣ O ρ)
outerᵣ? O (rvar i) with freeʳ i O in q
... | true  = just ((λ ()) ,
                    λ {k} r → subst (λ x → freeʳ x O ≡ true) (sym (true-dec (k ≟ᶠ i) r)) q)
... | false = nothing
outerᵣ? O (rconst c) = just ((λ ()) , (λ ()))
outerᵣ? O (ρ ·̂ᵣ ρ') with outerᵣ? O ρ | outerᵣ? O ρ'
... | just (f , f') | just (g , g') = just (∨-elim f g , ∨-elim f' g')
... | _             | _             = nothing
outerᵣ? O (ρ ⊔̂ᵣ ρ') with outerᵣ? O ρ | outerᵣ? O ρ'
... | just (f , f') | just (g , g') = just (∨-elim f g , ∨-elim f' g')
... | _             | _             = nothing
outerᵣ? O ∣ ε ∣̂ᵉ with outerₑ? O ε
... | just f  = just (f , (λ ()))
... | nothing = nothing

stripʳ-unit : ∀ {Φ} → Maybe UnitMinₑ → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
            → (ρ₀ : RExp Φ) → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → Maybe (Atomʳ j ρ ρ')
stripʳ-unit nothing   j ρ ρ' ρ₀ e₁ = nothing
stripʳ-unit (just um) j ρ ρ' ρ₀ e₁ with strʳ⁺ j (ρ' [ updᵉ j ûₑ ]ʳ)
... | nothing          = nothing
... | just (ρ₀' , e₂) =
      just ((ρ₀ , ρ₀') ∷ [] ,
            λ δ Q k → transᵣ (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
                                     (sym (pop⨟ʳ j ρ e₁ δ))
                                     (trans (sym (pop⨟ʳ j (ρ' [ updᵉ j ûₑ ]ʳ) e₂ δ))
                                            ([⨟]ʳ ρ' (updᵉ j ûₑ) (popˢ j ⨟ˢ (δ ↑ᵉ))))
                                     (⊩-wkᵉᵣ (k (here refl))))
                             (mono-substᵣ (updᵉ-below j ûₑ (popˢ j ⨟ˢ (δ ↑ᵉ)) (minₑ um)) ρ'))

stripᵉ-unit : ∀ {Φ} → Maybe UnitMinₑ → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
            → (ε₀ : EExp Φ) → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → Maybe (Atomᵉ j ε ε')
stripᵉ-unit nothing   j ε ε' ε₀ e₁ = nothing
stripᵉ-unit (just um) j ε ε' ε₀ e₁ with strᵉ⁺ j (ε' [ updᵉ j ûₑ ]ᵉ)
... | nothing          = nothing
... | just (ε₀' , e₂) =
      just ((ε₀ , ε₀') ∷ [] ,
            λ δ Q k → transₑ (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y)
                                     (sym (pop⨟ᵉ j ε e₁ δ))
                                     (trans (sym (pop⨟ᵉ j (ε' [ updᵉ j ûₑ ]ᵉ) e₂ δ))
                                            ([⨟]ᵉ ε' (updᵉ j ûₑ) (popˢ j ⨟ˢ (δ ↑ᵉ))))
                                     (⊩-wkᵉₑ (k (here refl))))
                             (mono-substₑ (updᵉ-below j ûₑ (popˢ j ⨟ˢ (δ ↑ᵉ)) (minₑ um)) ε'))

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
...   | nothing = stripʳ-unit umin?ₑ j ρ ρ' ρ₀ e₁
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
...   | nothing = stripᵉ-unit umin?ₑ j ε ε' ε₀ e₁
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
-- away from the rigid, and declined otherwise.

atomᵈ : ∀ {Φ} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → (ρ : RExp (Φ +e))
      → Maybe (Atomᵈ j A ρ)
atomᵈ j A ρ with strᵛ⁺ j A | strʳ⁺ j ρ
... | just (A₀ , e₁) | just (ρ₀ , e₂) =
      just ((A₀ , ρ₀) ∷ [] ,
            λ δ Q k → subst₂ (VarOK (wkᵉ-H Q))
                             (sym (pop⨟ᵛ j A e₁ δ)) (sym (pop⨟ʳ j ρ e₂ δ))
                             (VarOK-wkᵉ (k (here refl))))
... | just _         | nothing = nothing
... | nothing        | _       = nothing

listʳ : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (l : List (RExp (Φ +e) × RExp (Φ +e)))
      → Maybe (Σ[ l₀ ∈ List (RExp Φ × RExp Φ) ]
                 (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                    → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
                    → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
                         → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ
                                   ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ)))
listʳ O j []              = just ([] , λ δ Q k → λ ())
listʳ O j ((ρ , ρ') ∷ l) with atomʳ O j ρ ρ' | listʳ O j l
... | just (a , fa) | just (l₀ , f) =
      just (a ++ l₀ ,
            λ δ Q k → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                        ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) m })
... | just _        | nothing = nothing
... | nothing       | _       = nothing

listᵉ : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (l : List (EExp (Φ +e) × EExp (Φ +e)))
      → Maybe (Σ[ l₀ ∈ List (EExp Φ × EExp Φ) ]
                 (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                    → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ᵉ ≾̂ₑ τ' [ δ ]ᵉ)
                    → (∀ {ε ε'} → (ε , ε') ∈ l
                         → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ
                                   ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ)))
listᵉ O j []              = just ([] , λ δ Q k → λ ())
listᵉ O j ((ε , ε') ∷ l) with atomᵉ O j ε ε' | listᵉ O j l
... | just (a , fa) | just (l₀ , f) =
      just (a ++ l₀ ,
            λ δ Q k → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                        ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) m })
... | just _        | nothing = nothing
... | nothing       | _       = nothing

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

splitᴿ : ∀ {Θ Φ} → Subst Θ (Φ +e) → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
       → Maybe (Σ[ R₀ ∈ Resid Φ ]
                  (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                     → Q ⊩ᴿ R₀ [ δ ] → wkᵉ-H Q ⊩ᴿ R [ popˢ j ⨟ˢ (δ ↑ᵉ) ]))
splitᴿ O j R with listʳ O j (rs R) | listᵉ O j (es R) | listᵗ j (ts R)
              | listˢ j (ss R) | listᵈ j (ds R)
... | just (lr , fr) | just (le , fe) | just (lt , ft) | just (ls , fs)
    | just (ld , fd) =
      just (resid lr le lt ls ld ,
            λ δ Q h → mk⊩ᴿ (fr δ Q (⊩rs h)) (fe δ Q (⊩es h)) (ft δ Q (⊩ts h))
                           (fs δ Q (⊩ss h)) (fd δ Q (⊩ds h)))
... | just _ | just _ | just _  | just _  | nothing = nothing
... | just _ | just _ | just _  | nothing | _       = nothing
... | just _ | just _ | nothing | _       | _       = nothing
... | just _ | nothing | _      | _       | _       = nothing
... | nothing | _      | _      | _       | _       = nothing

threadOps : ∀ {Θ} → {f : Op → Constraint Θ}
          → ((s : St Θ) → (op : Op)
               → Maybe (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (f op))))
          → (l : List Op) → (s : St Θ)
          → Maybe (Σ[ s' ∈ St Θ ] ((s ⟶ s') × AllOp (λ op → Wit s' (f op)) l))
threadOps g []       s = just (s , ⟶-id , [])
threadOps {f = f} g (op ∷ l) s with g s op
... | nothing = nothing
... | just (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁
...   | nothing = nothing
...   | just (s₂ , m₂ , ws) = just (s₂ , ⟶-⨟ m₁ m₂ , wit-mono m₂ (f op) w₁ ∷ ws)

-- The image of the rigid, with the equation that names it: a
-- pattern-matching wrapper, so that `popᵉ`'s case analysis stays
-- visible to a proof about it.

evar? : ∀ {Φ} → (ε : EExp Φ) → Maybe (Σ[ j ∈ EVar Φ ] (ε ≡ evar j))
evar? (evar j)   = just (j , refl)
evar? (econst c) = nothing
evar? (ε ·̂ₑ ε')  = nothing
evar? (ε ⊔̂ₑ ε')  = nothing

-- Of the four failures below, only the atoms `splitᴿ` has to discharge
-- on the spot are an oracle's verdict; the rest cannot happen or are
-- refuted by `Core.Rigid`'s escape lemma.

popᵉ : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
     → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
     → (⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → Wit (st Φ θ'' R'' rg'') C
     → Maybe (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (∀ᵉ C)))
popᵉ s C (scope nt nr nzero)    θ'' R'' rg'' m'' w'' = nothing
popᵉ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w''
  with evar? (sE (mδ m'') (newᵉ {Ψ s}))
... | nothing = nothing
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') | splitᴿ (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') j R''
...   | just (δ₀ , pδ) | just (R₀ , tr) =
        just (st (scope nt nr n) (θ s ⨟ˢ δ₀) (res s [ δ₀ ]ᴿ ∪ᴿ R₀) (transRig δ₀ (rig s)) ,
              mor δ₀ ≐ˢ-refl (λ δ Q h → ⊩ᴿ-subst (∪ᴿ-fst h)) ,
              λ δ Q h → ⊨-resp-≐ˢ (chain δ) C
                          (w'' (popˢ j ⨟ˢ (δ ↑ᵉ)) (wkᵉ-H Q) (tr δ Q (∪ᴿ-snd h))))
        where
          -- the inner store, restricted to the outer unknowns, moves
          -- the rigid back to the newest position
          key : (mδ m'' ⨟ˢ popˢ j) ≐ˢ (δ₀ ↑ᵉ)
          key = mk≐ˢ (λ α → trans (≐ᵗ pδ α) (wkˢᵉ-v (sTy δ₀ α)))
                     (λ i → trans (≐ʳ pδ i) (wkˢᵉ-r (sR δ₀ i)))
                     (λ { zero    → trans (cong (_[ popˢ j ]ᵉ) eqj) (popˢ-hit j)
                        ; (suc i) → trans (≐ᵉ pδ i) (wkˢᵉ-e (sE δ₀ i)) })

          key' : (θ'' ⨟ˢ popˢ j) ≐ˢ ((θ s ⨟ˢ δ₀) ↑ᵉ)
          key' = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m'')) (popˢ j))
                 (≐ˢ-trans (⨟-assoc (θ s ↑ᵉ) (mδ m'') (popˢ j))
                 (≐ˢ-trans (⨟-congʳ (θ s ↑ᵉ) key) (⨟-↑ᵉ (θ s) δ₀)))

          chain : ∀ {Φ'} → (δ : Subst (scope nt nr n) Φ')
                → (θ'' ⨟ˢ (popˢ j ⨟ˢ (δ ↑ᵉ))) ≐ˢ (((θ s ⨟ˢ δ₀) ⨟ˢ δ) ↑ᵉ)
          chain δ = ≐ˢ-trans (≐ˢ-sym (⨟-assoc θ'' (popˢ j) (δ ↑ᵉ)))
                    (≐ˢ-trans (⨟-congˡ key' (δ ↑ᵉ)) (⨟-↑ᵉ (θ s ⨟ˢ δ₀) δ))
...   | just _         | nothing = nothing
...   | nothing        | _       = nothing

-- Before a rigid scope closes, the var-rule disjunctions with a side
-- decided true are dropped, and the unknowns local to it are sent to
-- their principal values: those free in no image of the unknowns the
-- scope was entered with.

localiseˢ : ∀ {Θ} {s₀ s'' : St Θ} → s₀ ⟶ s'' → Σ[ s₃ ∈ St Θ ] (s'' ⟶ s₃)
localiseˢ {s'' = s''} m =
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

solve : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ)
      → Maybe (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C))

solve s ⊤̂ = just (s , ⟶-id , λ δ Q h → tt)

solve s ⊥̂ = nothing

solve s (C ∧̂ D) with solve s C
... | nothing = nothing
... | just (s₁ , m₁ , w₁) with solve s₁ D
...   | nothing = nothing
...   | just (s₂ , m₂ , w₂) =
        just (s₂ , ⟶-⨟ m₁ m₂ , λ δ Q h → wit-mono m₂ C w₁ δ Q h , w₂ δ Q h)

solve s (A ≐ᵥ B) with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
... | nothing = nothing
... | just (Ψ⁺ , ρ , equ) with expandSub (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ))
...   | nothing = nothing
...   | just (Ψ' , δ) =
        just (st Ψ' (θ s ⨟ˢ ⟦ ρ ⟧ᴬ ⨟ˢ δ) (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ)
                 (transRig δ (transRig ⟦ ρ ⟧ᴬ (rig s))) ,
              mor (⟦ ρ ⟧ᴬ ⨟ˢ δ) (≐ˢ-sym (⨟-assoc (θ s) ⟦ ρ ⟧ᴬ δ))
                  (λ δ' Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc ⟦ ρ ⟧ᴬ δ δ'))
                                          (⊩ᴿ-subst (⊩ᴿ-subst h))) ,
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
... | nothing        = nothing
... | just (Ψ' , δ) with subDec (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ)
...   | nothing = nothing
...   | just d  =
        just (st Ψ' (θ s ⨟ˢ δ) (res s [ δ ]ᴿ ∪ᴿ atomsᴿ (atomsOf d))
                 (transRig δ (rig s)) ,
              mor δ ≐ˢ-refl (λ δ' Q h → ⊩ᴿ-subst (∪ᴿ-fst h)) ,
              λ δ' Q h → subst₂ (Q ∣_<:̂ᵛ_) (chain₂ᵛ A (θ s) δ δ') (chain₂ᵛ B (θ s) δ δ')
                                (intro d δ' (holdsᴿ (atomsOf d) (∪ᴿ-snd h))))

solve s (ρ ≾̂ᵣᶜ ρ') =
  just (st (Ψ s) (θ s) (pushʳ (ρ [ θ s ]ʳ) (ρ' [ θ s ]ʳ) (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailʳ h)) ,
        λ δ Q h → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y)
                         ([⨟]ʳ ρ (θ s) δ) ([⨟]ʳ ρ' (θ s) δ) (⊩rs h (here refl)))

solve s (ε ≾̂ₑᶜ ε') =
  just (st (Ψ s) (θ s) (pushᵉ (ε [ θ s ]ᵉ) (ε' [ θ s ]ᵉ) (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵉ h)) ,
        λ δ Q h → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y)
                         ([⨟]ᵉ ε (θ s) δ) ([⨟]ᵉ ε' (θ s) δ) (⊩es h (here refl)))

solve s (Etᶜ A) =
  just (st (Ψ s) (θ s) (pushᵗ (A [ θ s ]ᵛ) (res s)) (rig s) ,
        mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵗ h)) ,
        λ δ Q h → subst (Q ⊩ᴱ_) ([⨟]ᵛ A (θ s) δ) (⊩ts h (here refl)))

solve s (Et∨≾ᵘ A ρ) with decide≾ᵣ {Q = ∅ᴴ} (ρ [ θ s ]ʳ) ûᵣ
... | just p =
      just (s , ⟶-id ,
            λ δ Q h → ≾ᵘ-ok (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([⨟]ʳ ρ (θ s) δ)
                                   (⊩-substᵣ ∅ᴴ-⊩ᴴ p)))
... | nothing =
      just (st (Ψ s) (θ s) (pushᵈ (A [ θ s ]ᵛ) (ρ [ θ s ]ʳ) (res s)) (rig s) ,
            mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailᵈ h)) ,
            λ δ Q h → subst₂ (VarOK Q) ([⨟]ᵛ A (θ s) δ) ([⨟]ʳ ρ (θ s) δ)
                             (⊩ds h (here refl)))

solve {Θ} s (∃ᵗ C) with solve (s ↑ᵗˢ) C
... | nothing = nothing
... | just (s'' , m'' , w'') =
      just (st (Ψ s'') (wkˢᵗ {Θ} ⨟ˢ θ s'') (res s'') (rig s'') ,
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
... | nothing = nothing
... | just (s'' , m'' , w'') =
      just (st (Ψ s'') (wkˢʳ {Θ} ⨟ˢ θ s'') (res s'') (rig s'') ,
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
... | nothing = nothing
... | just (s'' , m'' , w'') =
      just (st (Ψ s'') (wkˢᵉ {Θ} ⨟ˢ θ s'') (res s'') (rig s'') ,
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
... | nothing = nothing
... | just (s'' , m'' , w'') =
      popᵉ s C (Ψ (proj₁ (localiseˢ m''))) (θ (proj₁ (localiseˢ m'')))
               (res (proj₁ (localiseˢ m''))) (rig (proj₁ (localiseˢ m'')))
               (⟶-⨟ m'' (proj₂ (localiseˢ m''))) (wit-mono (proj₂ (localiseˢ m'')) C w'')

solve s (⋀ᵒᵖ f) with threadOps {f = f} (λ s' op → solve s' (f op)) ops s
... | nothing = nothing
... | just (s' , m , ws) =
      just (s' , m , λ δ Q h op → all-lookup ws (complete op) δ Q h)

-- Reading a residual back as a hypothesis set asks every subtyping
-- demand to decompose; one expansion of what is left makes it so.

reexpand : ∀ {Θ} → (s : St Θ) → Maybe (Σ[ s' ∈ St Θ ] (s ⟶ s'))
reexpand s with expandSub (ss (res s))
... | nothing       = nothing
... | just (Ψ' , δ) =
      just (st Ψ' (θ s ⨟ˢ δ) (res s [ δ ]ᴿ) (transRig δ (rig s)) ,
            mor δ ≐ˢ-refl (λ δ' Q h → ⊩ᴿ-subst h))
