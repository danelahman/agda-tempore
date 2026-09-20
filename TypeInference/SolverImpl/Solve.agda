------------------------------------------------------------------
-- Walks a constraint, threading a state: type equations go to   --
-- the unification core, grade orderings and eternality          --
-- demands are residualised, and binders lift the state.         --
-- A successful witness is deferred, re-read at the state a      --
-- later component leaves behind rather than transported         --
-- along it, making conjunction transport-free.                  --
-- At a rigid binder the state is lifted with a fresh residual:  --
-- atoms free of the rigid are kept, one mentioning it is        --
-- discharged on the spot, and an outer unknown's image must     --
-- stay free of it.                                              --
------------------------------------------------------------------

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (tt)

open import Relation.Binary.Definitions using (Decidable)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Solve
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

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ; ≐ˢ-sym; ≐ˢ-,ᵗ; ≐ˢ-,ʳ; ≐ˢ-,ᵉ)

open import TypeInference.SolverImpl.Enum S using (AllOp; []; _∷_; all-lookup)

open import TypeInference.SolverImpl.Core.AList      S
open import TypeInference.SolverImpl.Core.Eqn        S
open import TypeInference.SolverImpl.Core.Rigid      S
open import TypeInference.SolverImpl.Core.Unify      S
open import TypeInference.SolverImpl.Core.UnifySound S using (unify-sound)

open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.State  S
open import TypeInference.SolverImpl.Normal S _≾ᵣ?_ _≾ₑ?_ umin?ᵣ umin?ₑ

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

-- An eternality demand that reduces to no atom at all. Wrapping the
-- verdict together with its proof keeps the case analysis of `atomᵗ`
-- visible from outside, which is what reasoning about it needs.

et₀? : ∀ {Φ} → (A : OVType Φ) → Maybe ({Q : Hyps Φ} → Q ⊩ᴱ A)
et₀? A with etDec A in e
... | just []      = just (λ {Q} → etDec-sound {Q = Q} A e (λ ()))
... | just (α ∷ _) = nothing
... | nothing      = nothing

atomʳ : ∀ {Φ} → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e)) → Maybe (Atomʳ j ρ ρ')
atomʳ j ρ ρ' with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just (ρ₀ , e₁) | just (ρ₀' , e₂) =
      just ((ρ₀ , ρ₀') ∷ [] ,
            λ δ Q k → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
                             (sym (pop⨟ʳ j ρ e₁ δ)) (sym (pop⨟ʳ j ρ' e₂ δ))
                             (⊩-wkᵉᵣ (k (here refl))))
... | just _         | nothing          with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
...   | just p  = just ([] , λ δ Q k → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
...   | nothing = nothing
atomʳ j ρ ρ' | nothing | _ with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just p  = just ([] , λ δ Q k → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

atomᵉ : ∀ {Φ} → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e)) → Maybe (Atomᵉ j ε ε')
atomᵉ j ε ε' with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just (ε₀ , e₁) | just (ε₀' , e₂) =
      just ((ε₀ , ε₀') ∷ [] ,
            λ δ Q k → subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y)
                             (sym (pop⨟ᵉ j ε e₁ δ)) (sym (pop⨟ᵉ j ε' e₂ δ))
                             (⊩-wkᵉₑ (k (here refl))))
... | just _         | nothing          with decide≾ₑ {Q = ∅ᴴ} ε ε'
...   | just p  = just ([] , λ δ Q k → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
...   | nothing = nothing
atomᵉ j ε ε' | nothing | _ with decide≾ₑ {Q = ∅ᴴ} ε ε'
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

listʳ : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (RExp (Φ +e) × RExp (Φ +e)))
      → Maybe (Σ[ l₀ ∈ List (RExp Φ × RExp Φ) ]
                 (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                    → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ʳ ≾̂ᵣ τ' [ δ ]ʳ)
                    → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
                         → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ
                                   ≾̂ᵣ ρ' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ʳ)))
listʳ j []              = just ([] , λ δ Q k → λ ())
listʳ j ((ρ , ρ') ∷ l) with atomʳ j ρ ρ' | listʳ j l
... | just (a , fa) | just (l₀ , f) =
      just (a ++ l₀ ,
            λ δ Q k → λ { (here refl) → fa δ Q (λ m → k (∈-++⁺ˡ m))
                        ; (there m)   → f δ Q (λ m' → k (∈-++⁺ʳ a m')) m })
... | just _        | nothing = nothing
... | nothing       | _       = nothing

listᵉ : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (EExp (Φ +e) × EExp (Φ +e)))
      → Maybe (Σ[ l₀ ∈ List (EExp Φ × EExp Φ) ]
                 (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                    → (∀ {τ τ'} → (τ , τ') ∈ l₀ → Q ⊩ τ [ δ ]ᵉ ≾̂ₑ τ' [ δ ]ᵉ)
                    → (∀ {ε ε'} → (ε , ε') ∈ l
                         → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ
                                   ≾̂ₑ ε' [ popˢ j ⨟ˢ (δ ↑ᵉ) ]ᵉ)))
listᵉ j []              = just ([] , λ δ Q k → λ ())
listᵉ j ((ε , ε') ∷ l) with atomᵉ j ε ε' | listᵉ j l
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

splitᴿ : ∀ {Φ} → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
       → Maybe (Σ[ R₀ ∈ Resid Φ ]
                  (∀ {Φ'} → (δ : Subst Φ Φ') → (Q : Hyps Φ')
                     → Q ⊩ᴿ R₀ [ δ ] → wkᵉ-H Q ⊩ᴿ R [ popˢ j ⨟ˢ (δ ↑ᵉ) ]))
splitᴿ j R with listʳ j (rs R) | listᵉ j (es R) | listᵗ j (ts R)
... | just (lr , fr) | just (le , fe) | just (lt , ft) =
      just (resid lr le lt ,
            λ δ Q h → mk⊩ᴿ (fr δ Q (⊩rs h)) (fe δ Q (⊩es h)) (ft δ Q (⊩ts h)))
... | just _         | just _         | nothing        = nothing
... | just _         | nothing        | _              = nothing
... | nothing        | _              | _              = nothing

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
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') | splitᴿ j R''
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
... | just (Ψ⁺ , ρ , equ) =
      just (st Ψ⁺ (θ s ⨟ˢ ⟦ ρ ⟧ᴬ) (res s [ ⟦ ρ ⟧ᴬ ]ᴿ) (transRig ⟦ ρ ⟧ᴬ (rig s)) ,
            mor ⟦ ρ ⟧ᴬ ≐ˢ-refl (λ δ Q h → ⊩ᴿ-subst h) ,
            λ δ Q h → trans (sym ([⨟]ᵛ A (θ s ⨟ˢ ⟦ ρ ⟧ᴬ) δ))
                      (trans (cong (_[ δ ]ᵛ) pinned) ([⨟]ᵛ B (θ s ⨟ˢ ⟦ ρ ⟧ᴬ) δ)))
      where
        pinned : A [ θ s ⨟ˢ ⟦ ρ ⟧ᴬ ]ᵛ ≡ B [ θ s ⨟ˢ ⟦ ρ ⟧ᴬ ]ᵛ
        pinned = trans (sym ([⨟]ᵛ A (θ s) ⟦ ρ ⟧ᴬ))
                 (trans (proj₁ (unify-sound (rig s)
                                            (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) equ))
                        ([⨟]ᵛ B (θ s) ⟦ ρ ⟧ᴬ))

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
      just (st (Ψ s) (θ s) (pushʳ (ρ [ θ s ]ʳ) ûᵣ (res s)) (rig s) ,
            mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) (tailʳ h)) ,
            λ δ Q h → ≾ᵘ-ok (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([⨟]ʳ ρ (θ s) δ)
                                   (⊩rs h (here refl))))

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
... | just (s'' , m'' , w'') = popᵉ s C (Ψ s'') (θ s'') (res s'') (rig s'') m'' w''

solve s (⋀ᵒᵖ f) with threadOps {f = f} (λ s' op → solve s' (f op)) ops s
... | nothing = nothing
... | just (s' , m , ws) =
      just (s' , m , λ δ Q h op → all-lookup ws (complete op) δ Q h)
