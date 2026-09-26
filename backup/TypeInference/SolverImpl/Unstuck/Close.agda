------------------------------------------------------------------
-- Closing a scope with no local unknown left is never stuck      --
--                                                                --
-- `splitᴿ` is stuck only on an ordering it can neither keep nor  --
-- defer, or on an inner entry, that mentions an unknown local to --
-- the scope. When every side of every ordering, and every inner  --
-- entry, mentions only unknowns the scope was entered with, each --
-- ordering is kept or deferred and each entry is carried out:    --
-- the close is solved or refuted. A rigid binder whose body is   --
-- not stuck, and whose localised residual has no local unknown   --
-- left, is then not stuck either. That residual has none when    --
-- the residual entering `localise` satisfies a predicate its     --
-- stages keep and that leaves none at a fixed point (`Fixpoint`).--
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using () renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.Outcome

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Unstuck.Close
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  where

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Instances S using (_↑ᵉⁿ_; ≐ˢ-↑ᵉⁿ)

open import TypeInference.Constraints.Syntax S using (Constraint; ∀ᵉ_)

open import TypeInference.SolverImpl.Deferred S using (Dfr; Ords; nb; body; ors; oes; allOf)
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.State    S
open import TypeInference.SolverImpl.Localise S
  using (Outerₑ; Outerᵣ; outerₑ?; outerᵣ?; localise; lσ; lR; lfix; evar?)
open import TypeInference.SolverImpl.Core.Rigid S using (strSub)
open import TypeInference.SolverImpl.Core.Unify S using (Rig)
open import TypeInference.SolverImpl.Solve    S opEnum
  using (splitᴿ; listᵗ; listˢ; listᵈ; listʳ; listᵉ; atomʳ; atomᵉ; Outerᵒ; outerᵒ?; OuterD; outerD?; both?;
         solve; popᵉ; thenRetry; reexpand; localiseˢ; Wit)
open import TypeInference.SolverImpl.Invariants.Outer S using (freeᵉ-≐; freeʳ-≐)
open import TypeInference.SolverImpl.Invariants S opEnum using (outerₑ?-ok; outerᵣ?-ok)
open import TypeInference.SolverImpl.Unstuck.Steps S using (allOf-ok)
open import TypeInference.SolverImpl.Unstuck.Rounds S using (AllIn; allIn; OuterO; oo-rs; oo-es; Keeps?)
open import TypeInference.SolverImpl.Unstuck.Fixpoint S using (localise-allIn)

------------------------------------------------------------------------
-- No unknown local to the scope in an ordering or an inner entry

record NoLocal {Θ Φ} (O : Subst Θ Φ) (R : Resid Φ) : Set where
  constructor noLocal
  field
    nl-rs  : ∀ {a} → a ∈ rs R → Outerᵣ O (proj₁ a) × Outerᵣ O (proj₂ a)
    nl-es  : ∀ {a} → a ∈ es R → Outerₑ O (proj₁ a) × Outerₑ O (proj₂ a)
    nl-dfs : OuterD O (dfs R)

open NoLocal public

------------------------------------------------------------------------
-- The tests succeed

both?-ok : ∀ {A B : Set} → (x : Maybe A) → (y : Maybe B)
         → (x ≡ nothing → ⊥) → (y ≡ nothing → ⊥) → both? x y ≡ nothing → ⊥
both?-ok (just _) (just _) f g ()
both?-ok nothing  y        f g q = f refl
both?-ok (just _) nothing  f g q = g refl

outerᵒ?-ok : ∀ {Θ Φ} {O : Subst Θ Φ} → (o : Ords Φ) → Outerᵒ O o → outerᵒ? O o ≡ nothing → ⊥
outerᵒ?-ok {O = O} o (hr , he) =
  both?-ok _ _
    (allOf-ok _ (ors o) (λ {a} m → both?-ok (outerᵣ? O (proj₁ a)) (outerᵣ? O (proj₂ a))
                                     (outerᵣ?-ok (proj₁ a) (proj₁ (hr m)))
                                     (outerᵣ?-ok (proj₂ a) (proj₂ (hr m)))))
    (allOf-ok _ (oes o) (λ {a} m → both?-ok (outerₑ? O (proj₁ a)) (outerₑ? O (proj₂ a))
                                     (outerₑ?-ok (proj₁ a) (proj₁ (he m)))
                                     (outerₑ?-ok (proj₂ a) (proj₂ (he m)))))

outerD?-ok : ∀ {Θ Φ} {O : Subst Θ Φ} → (D : List (Dfr Φ)) → OuterD O D → outerD? O D ≡ nothing → ⊥
outerD?-ok {O = O} D h =
  allOf-ok (λ E → outerᵒ? (O ↑ᵉⁿ nb E) (body E)) D (λ {E} m → outerᵒ?-ok (body E) (h m))

-- An ordering over the entering unknowns is kept or deferred

listʳ-ok : ∀ {Θ Φ} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e)) → (j : EVar (Φ +e))
         → (l : List (RExp (Φ +e) × RExp (Φ +e)))
         → (∀ {a} → a ∈ l → Outerᵣ O⁺ (proj₁ a) × Outerᵣ O⁺ (proj₂ a))
         → listʳ O O⁺ j l ≡ nothing → ⊥
listʳ-ok O O⁺ j []             h ()
listʳ-ok O O⁺ j ((ρ , ρ') ∷ l) h with listʳ O O⁺ j l in e
... | nothing = λ _ → listʳ-ok O O⁺ j l (λ m → h (there m)) e
... | just (l₀ , d₀ , f) with atomʳ O j ρ ρ'
...   | just _  = λ ()
...   | nothing with outerᵣ? O⁺ ρ in e₁ | outerᵣ? O⁺ ρ' in e₂
...     | just _  | just _  = λ ()
...     | nothing | _       = λ _ → outerᵣ?-ok ρ (proj₁ (h (here refl))) e₁
...     | just _  | nothing = λ _ → outerᵣ?-ok ρ' (proj₂ (h (here refl))) e₂

listᵉ-ok : ∀ {Θ Φ} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e)) → (j : EVar (Φ +e))
         → (l : List (EExp (Φ +e) × EExp (Φ +e)))
         → (∀ {a} → a ∈ l → Outerₑ O⁺ (proj₁ a) × Outerₑ O⁺ (proj₂ a))
         → listᵉ O O⁺ j l ≡ nothing → ⊥
listᵉ-ok O O⁺ j []             h ()
listᵉ-ok O O⁺ j ((ε , ε') ∷ l) h with listᵉ O O⁺ j l in e
... | nothing = λ _ → listᵉ-ok O O⁺ j l (λ m → h (there m)) e
... | just (l₀ , d₀ , f) with atomᵉ O j ε ε'
...   | just _  = λ ()
...   | nothing with outerₑ? O⁺ ε in e₁ | outerₑ? O⁺ ε' in e₂
...     | just _  | just _  = λ ()
...     | nothing | _       = λ _ → outerₑ?-ok ε (proj₁ (h (here refl))) e₁
...     | just _  | nothing = λ _ → outerₑ?-ok ε' (proj₂ (h (here refl))) e₂

------------------------------------------------------------------------
-- The close

splitᴿ-unstuck : ∀ {Θ Φ} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
               → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
               → NoLocal O⁺ R → ¬ (splitᴿ O O⁺ j R ≡ stuck)
splitᴿ-unstuck O O⁺ j R nl
  with listᵗ j (ts R) | listˢ j (ss R) | listᵈ j (ds R)
     | listʳ O O⁺ j (rs R) in er | listᵉ O O⁺ j (es R) in ee | outerD? O⁺ (dfs R) in ed
... | just _  | just _  | just _  | just _  | just _  | just _  = λ ()
... | nothing | _       | _       | _       | _       | _       = λ ()
... | just _  | nothing | _       | _       | _       | _       = λ ()
... | just _  | just _  | nothing | _       | _       | _       = λ ()
... | just _  | just _  | just _  | nothing | _       | _       =
      λ _ → listʳ-ok O O⁺ j (rs R) (nl-rs nl) er
... | just _  | just _  | just _  | just _  | nothing | _       =
      λ _ → listᵉ-ok O O⁺ j (es R) (nl-es nl) ee
... | just _  | just _  | just _  | just _  | just _  | nothing =
      λ _ → outerD?-ok (dfs R) (nl-dfs nl) ed

------------------------------------------------------------------------
-- The test for the entering unknowns reads the images only

module _ {Θ Φ} {O O' : Subst Θ Φ} (p : O ≐ˢ O') where

  outerₑ-≐ : (ε : EExp Φ) → Outerₑ O ε → Outerₑ O' ε
  outerₑ-≐ ε o {k} q = trans (sym (freeᵉ-≐ p k)) (o q)

  outerᵣ-≐ : (ρ : RExp Φ) → Outerᵣ O ρ → Outerᵣ O' ρ
  outerᵣ-≐ ρ (oe , or) = (λ {k} q → trans (sym (freeᵉ-≐ p k)) (oe q))
                       , (λ {k} q → trans (sym (freeʳ-≐ p k)) (or q))

noLocal-≐ : ∀ {Θ Φ} {O O' : Subst Θ Φ} {R : Resid Φ} → O ≐ˢ O' → NoLocal O R → NoLocal O' R
noLocal-≐ p (noLocal r e d) =
  noLocal (λ {a} m → outerᵣ-≐ p (proj₁ a) (proj₁ (r m)) , outerᵣ-≐ p (proj₂ a) (proj₂ (r m)))
          (λ {a} m → outerₑ-≐ p (proj₁ a) (proj₁ (e m)) , outerₑ-≐ p (proj₂ a) (proj₂ (e m)))
          (λ {E} m → (λ {a} m' → outerᵣ-≐ (≐ˢ-↑ᵉⁿ p (nb E)) (proj₁ a) (proj₁ (proj₁ (d m) m'))
                                , outerᵣ-≐ (≐ˢ-↑ᵉⁿ p (nb E)) (proj₂ a) (proj₂ (proj₁ (d m) m')))
                   , (λ {a} m' → outerₑ-≐ (≐ˢ-↑ᵉⁿ p (nb E)) (proj₁ a) (proj₁ (proj₂ (d m) m'))
                                , outerₑ-≐ (≐ˢ-↑ᵉⁿ p (nb E)) (proj₂ a) (proj₂ (proj₂ (d m) m'))))

------------------------------------------------------------------------
-- A rigid binder

popᵉ-unstuck : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
             → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
             → (m'' : ⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → (w'' : Wit (st Φ θ'' R'' rg'') C)
             → NoLocal (mδ m'') R'' → ¬ (popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ stuck)
popᵉ-unstuck s C (scope nt nr nzero)    θ'' R'' rg'' m'' w'' nl = λ ()
popᵉ-unstuck s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' nl
  with evar? (sE (mδ m'') (newᵉ {Ψ s}))
... | nothing = λ ()
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'')
                        | splitᴿ (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (mδ m'') j R'' in e
...   | just _  | solved _ = λ ()
...   | just _  | refuted  = λ ()
...   | just _  | stuck    = λ _ → splitᴿ-unstuck _ _ j R'' nl e
...   | nothing | _        = λ ()

thenRetry-unstuck : ∀ {Θ} {s : St Θ} {C : Constraint Θ}
                  → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
                  → ¬ (x ≡ stuck) → ¬ (thenRetry {C = C} x ≡ stuck)
thenRetry-unstuck refuted    h = λ ()
thenRetry-unstuck stuck      h = λ _ → h refl
thenRetry-unstuck {C = C} (solved (s₁ , m₁ , w₁)) h with retry s₁
  where open import TypeInference.SolverImpl.Solve S opEnum using (retry)
... | nothing = λ ()
... | just _  = λ ()

-- The residual a clause's scope is localised to, at the close

Closed : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e)) → Set
Closed s C = ∀ {r s₃} {m₃ : proj₁ r ⟶ s₃}
           → solve (⇑ᵉˢ s) C ≡ solved r → reexpand (proj₁ r) ≡ just (s₃ , m₃)
           → NoLocal (mδ (⟶-⨟ (proj₁ (proj₂ r)) m₃))
                     (lR (localise (mδ (⟶-⨟ (proj₁ (proj₂ r)) m₃)) (res s₃)))

solve-∀ᵉ-unstuck : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
                 → ¬ (solve (⇑ᵉˢ s) C ≡ stuck) → Closed s C → ¬ (solve s (∀ᵉ C) ≡ stuck)
solve-∀ᵉ-unstuck s C body cl with solve (⇑ᵉˢ s) C in e
... | refuted = λ ()
... | stuck   = λ _ → body refl
... | solved r@(s'' , m'' , w'') with reexpand s'' in e₃
...   | nothing        = λ ()
...   | just (s₃ , m₃) =
        thenRetry-unstuck _
          (popᵉ-unstuck s C _ _ _ _ _ _
            (noLocal-≐ (≐ˢ-sym (lfix (localise (mδ (⟶-⨟ m'' m₃)) (res s₃)))) (cl {r} refl e₃)))

------------------------------------------------------------------------
-- A residual over the entering unknowns has no local one; `localise`
-- leaves such a residual for a predicate its stages keep

allIn→noLocal : ∀ {Θ Φ} {O : Subst Θ Φ} {R : Resid Φ} → AllIn O R → NoLocal O R
allIn→noLocal (allIn r e d f) =
  noLocal r e (λ m → (λ {a} m' → oo-rs (f m) m') , (λ {a} m' → oo-es (f m) m'))

-- A clause's close is not stuck when, at every close the body reaches,
-- some predicate the stages of `localise` keep holds of the residual

closed-by : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
          → (∀ {r s₃} {m₃ : proj₁ r ⟶ s₃}
             → solve (⇑ᵉˢ s) C ≡ solved r → reexpand (proj₁ r) ≡ just (s₃ , m₃)
             → Σ[ Pu ∈ (Resid (Ψ s₃) → Set) ]
                 (Keeps? (mδ (⟶-⨟ (proj₁ (proj₂ r)) m₃)) (res s₃) Pu × Pu (res s₃)))
          → Closed s C
closed-by s C h e e₃ with h e e₃
... | Pu , K , pu = allIn→noLocal (localise-allIn _ _ Pu K pu)
