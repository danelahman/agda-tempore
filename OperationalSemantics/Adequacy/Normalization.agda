------------------------------------------------------------------------
-- Weak-head normalization: the fundamental lemma.                    --
--                                                                    --
-- The language has no recursion, so termination is syntactic.        --
-- Reducibility is needed, since substitution can grow a term.        --
--                                                                    --
-- The `handle` case is an induction on the scrutinee's `CRed`        --
-- derivation: each `HANDLE-OP` consumes one resumption premise.      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Normalization (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import OperationalSemantics.Adequacy.Bind           Spec
open import OperationalSemantics.Adequacy.Environment    Spec
open import OperationalSemantics.Adequacy.Evaluation     Spec
open import OperationalSemantics.Adequacy.Handle         Spec
open import OperationalSemantics.Adequacy.Reducibility   Spec
open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import Syntax.Substitutions.At        Spec
open import Syntax.Substitutions.Clauses   Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec

-- Induction on the typing derivation, mutually for values and computations.
-- Five computation cases are split off here, each stated as its own lemma
-- taking the induction hypotheses it needs — for a binding subterm, at *every*
-- environment, since the state the subterm is reached at is not the one the
-- case starts from. Sequencing is `Adequacy.Bind`'s `seq-CRed`.

-- Unboxing: read the store. `env-Cˢ-unbox` sends the action to an `unbox` at
-- the cell the environment sends this one to, `UNBOX` reads that cell, and the
-- value read — the raw read at the cell's declared payload type, subsumed once
-- along the composite the action accumulates — is reducible at the current
-- state.

FL-unbox : ∀ {St Γ A A₀ D ρ σ ε} → (γ : Env St Γ) → Rel-Env γ
         → (x : [ ρ ] A₀ ∈[ σ ] Γ) → (rel : σ ≾ᵣ ρ) → (p : A₀ <:ᵛ A)
         → (M : Γ ∷ A ⊢C⦂ D ‼ ε)
         → (∀ {St'} → (γ' : Env St' (Γ ∷ A)) → Rel-Env γ'
              → CRed' D ε St' (env-C γ' M))
         --------------------------------------------------------------
         → CRed' D ε St (env-C γ (unbox x rel p M))

FL-unbox {St = St} {A = A} {A₀ = A₀} {ρ = ρ} {σ = σ} γ pγ x rel p M pM =
  CRed-≡ᶜ (sym (env-Cˢ-unbox γ [] x rel p M rel₁ p₁))
          (CRed-expand UNBOX (pM (γ ∷ᵉ U) (pγ , pU)))
  where
    rel₁ = env-cell-rel γ [] (σ , x) rel
    p₁   = <:ᵛ-trans (env-cell-typ γ [] (σ , x)) p

    Y = unbox-lookup St (rvar-pos (env-cell γ [] (σ , x))) rel₁

    U = subV Y p₁

    store : VRed (rvar-type (env-cell γ [] (σ , x))) St Y
    store = env-cell-val γ pγ (σ , x) _ (env-cell-push γ [] (σ , x)) rel₁

    pU : VRed A St U
    pU = VRed-sub p₁ Y store

-- Matching: `MATCH` fires at any scrutinee, substituting its two projections
-- in the *opposite* order from the environment — the rule replaces `B` (its
-- value weakened past `A`) and then `A`, the action replaces `A` with `B`
-- riding in the suffix and then `B`. That is exactly `sub-swap-C`, at the
-- empty suffix, where both orders' casts and boundary variables reduce.

FL-match : ∀ {St Γ A B D ε} → (γ : Env St Γ) → Rel-Env γ
         → (V : Γ ⊢V⦂ A |×| B) → (M : Γ ∷ A ∷ B ⊢C⦂ D ‼ ε)
         → VRed (A |×| B) St (env-V γ V)
         → (∀ {St'} → (γ' : Env St' (Γ ∷ A ∷ B)) → Rel-Env γ'
              → CRed' D ε St' (env-C γ' M))
         --------------------------------------------------------------
         → CRed' D ε St (env-C γ (match V `in M))

FL-match {St = St} {A = A} {B = B} γ pγ V M (p₁ , p₂) pM =
  subst (CRed' _ _ St) (sym (env-Cˢ-match γ [] V M))
    (CRed-expand MATCH
      (CRed-≡ᶜ (sym step) (pM ((γ ∷ᵉ U₁) ∷ᵉ U₂) ((pγ , p₁) , p₂))))
  where
    M₀ = env-Cˢ γ ([] ∷ A ∷ B) M

    U₁ = fstᵛ (env-V γ V)
    U₂ = sndᵛ (env-V γ V)

    step : (M₀ [ split-[] ↦ V-rename wk-ren U₂ ]c) [ split-[] ↦ U₁ ]c
         ≡ env-C ((γ ∷ᵉ U₁) ∷ᵉ U₂) M
    step = sub-swap-C [] M₀ U₂ U₁

-- Handling: `env-Cˢ-handle` splits the action, `handle-CRed` runs the scrutinee
-- and then the clauses and the sequel.
--
-- The sequel premise is `FL-C`'s at `(γ ⟨ q ⟩ᵉ) ∷ᵉ V`, as for sequencing.
--
-- For the clause premise, `HANDLE-OP` fires a clause at `St₁` and `BOX`
-- allocates the resumption, so the clause is reached at
-- `St₁ ∷ₛ V₀` with its continuation binder *being* the fresh cell:
-- that environment is `liftᵉ V₀ ((γ ⟨ q ⟩ᵉ) ∷ᵉ W)` — the barrier lock matched
-- by the `⊤ᵣ`-reach the premise supplies, `_∷ᵉ_` the operation's parameter, and
-- `liftᵉ` the cell. Its `Rel-Env` is `((pγ , pW) , bv)`, whose last component
-- is exactly the `Boxed-VRed` argument `handle-CRed` supplies.

FL-handle : ∀ {St Γ A B ε₁ ε₂} → (γ : Env St Γ) → Rel-Env γ
          → (M : Γ ⊢C⦂ A ‼ ε₁)
          → (H : Fam B (Γ ⟨ ⊤ᵣ ⟩))
          → (N : Γ ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
          → CRed' A ε₁ St (env-C γ M)
          → (∀ {St'} {op : Op} {ε₃ : E}
               → (γ' : Env St' (Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ]
                                      (type-of-gtype (arity op) ⇒ B ‼ ε₃)))
               → Rel-Env γ'
               → CRed' B (op-grade op ·ₑ ε₃) St' (env-C γ' (H op ε₃)))
          → (∀ {St'} → (γ' : Env St' (Γ ⟨ mapᵉ ε₁ ⟩ ∷ A)) → Rel-Env γ'
               → CRed' B ε₂ St' (env-C γ' N))
          --------------------------------------------------------------
          → CRed' B (ε₁ ·ₑ ε₂) St (env-C γ (handle M `with H `in N))

FL-handle {St = St} {Γ = Γ} {A = A} {B = B} {ε₁ = ε₁} γ pγ M H N pM pH pN =
  subst (CRed' _ _ St) (sym (env-Cˢ-handle γ [] M H N))
    (handle-CRed Hγ (env-Cˢ γ ([] ⟨ mapᵉ ε₁ ⟩ ∷ A) N) pM clause sequel)
  where
    Hγ : Fam B (toCtx St ⟨ ⊤ᵣ ⟩)
    Hγ = env-Hˢ γ [] H

    clause : Clause-Prem B St Hγ
    clause {St₁} {op} {ε₃} q V₀ bv W pW =
      subst (CRed' _ _ _) (sym (env-Hˢ-fired γ q H V₀ W))
        (pH (liftᵉ V₀ ((γ ⟨ q ⟩ᵉ) ∷ᵉ W)) ((pγ , pW) , bv))

    sequel : Seq-Prem (env-Cˢ γ ([] ⟨ mapᵉ ε₁ ⟩ ∷ A) N)
    sequel q V pV =
      subst (CRed' _ _ _) (sym (env-Cˢ-head (γ ⟨ q ⟩ᵉ) N V))
            (pN ((γ ⟨ q ⟩ᵉ) ∷ᵉ V) (pγ , pV))

-- Boxing: `BOX` allocates, and the reduct already lives over the *new* state's
-- context — so the environment must keep the binder as the fresh cell rather than
-- substitute for it, which is `liftᵉ`. The reduct then
-- *is* the action at `liftᵉ V₀ γ`, and its `Rel-Env` is the boxed value's
-- reducibility at every state the lock permits — which is the first hypothesis,
-- at the environment `γ ⟨ q ⟩ᵉ` (whose action at the empty suffix is
-- `V-rename (unbox-ren q)`, both casts being `refl` there).

FL-box : ∀ {St Γ A D ρ ε} → (γ : Env St Γ) → Rel-Env γ
       → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A) → (M : Γ ∷ [ ρ ] A ⊢C⦂ D ‼ ε)
       → (∀ {St'} → (γ' : Env St' (Γ ⟨ ρ ⟩)) → Rel-Env γ'
            → VRed A St' (env-V γ' V))
       → (∀ {St'} → (γ' : Env St' (Γ ∷ [ ρ ] A)) → Rel-Env γ'
            → CRed' D ε St' (env-C γ' M))
       --------------------------------------------------------------
       → CRed' D ε St (env-C γ (box V M))

FL-box {St = St} {Γ = Γ} {A = A} {ρ = ρ} γ pγ V M pV pM =
  subst (CRed' _ _ St) (sym (env-Cˢ-box γ [] V M))
    (CRed-expand BOX (pM (liftᵉ V₀ γ) (pγ , cell)))
  where
    V' = env-Vˢ γ ([] ⟨ ρ ⟩) V
    V₀ = V-rename (eq-ren (sym (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}))) V'

    -- the two `eq-ren`s the allocation and the lookup insert cancel
    cancel : ∀ {St'} → (q : St ⊑ₛ[ ρ ] St')
           → V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V₀
           ≡ V-rename (unbox-ren q) V'
    cancel q =
      trans
        (sym (V-rename-∘ (eq-ren (sym ++ᶜ-identityˡ))
                            (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V'))
        (V-rename-≡
          (≐ʳ-trans
            (≐ʳ-sym (∘ʳ-assoc-≐ʳ (eq-ren (sym ++ᶜ-identityˡ))
                                (eq-ren ++ᶜ-identityˡ) (unbox-ren q)))
            (∘ʳ-idˡ-≐ʳ (unbox-ren q)
              (≐ʳ-trans
                (eq-ren-∘-≐ʳ (sym (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}))
                            ++ᶜ-identityˡ)
                (eq-ren-≐ʳ _ refl))))
          V')

    cell : ∀ {St'} → (q : St ⊑ₛ[ ρ ] St')
         → VRed A St' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V₀)
    cell q = VRed-≡ᵛ A (sym (cancel q)) (pV (γ ⟨ q ⟩ᵉ) pγ)

-- Performing: already a weak head normal form, so this is `cred-op` at the empty
-- run. Its resumption premise is the induction hypothesis at the environment a
-- `resume` amounts to — the lock the operation is performed under, matched by
-- the resumption's own reach, and the arity value on top — which the action
-- *is*, both of `env-Cˢ`'s casts being `refl` at the empty suffix.

FL-perform : ∀ {St Γ A ε} {op : Op} → (γ : Env St Γ) → Rel-Env γ
           → (V : Γ ⊢V⦂ type-of-gtype (param op))
           → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                    ⊢C⦂ A ‼ ε)
           → VRed (type-of-gtype (param op)) St (env-V γ V)
           → (∀ {St'} → (γ' : Env St' (Γ ⟨ mapᵉ (op-grade op) ⟩
                                         ∷ type-of-gtype (arity op)))
                → Rel-Env γ' → CRed' A ε St' (env-C γ' M))
           --------------------------------------------------------------
           → CRed' A (op-grade op ·ₑ ε) St (env-C γ (perform op V M))

FL-perform {St = St} {Γ = Γ} {op = op} γ pγ V M pV pM =
  subst (CRed' _ _ _) (sym (env-Cˢ-perform γ [] V M))
    (cred-op refl ε* (VRed→VRedᵍ (param op) (env-V γ V) pV)
      (λ q W' pW' →
         subst (CRed' _ _ _) (resumeq q W')
           (pM ((γ ⟨ q ⟩ᵉ) ∷ᵉ W') (pγ , VRedᵍ→VRed (arity op) W' pW'))))
  where
    ρ  = mapᵉ (op-grade op)
    Ar = type-of-gtype (arity op)
    M₀ = env-Cˢ γ ([] ⟨ ρ ⟩ ∷ Ar) M

    -- the action at the resumption's environment *is* the resumption, once the
    -- two `++ᶜ`-associativity casts are seen to be the identity
    resumeq : ∀ {St₂ : 𝕊 []} → (q : St ⊑ₛ[ ρ ] St₂)
            → (W' : toCtx St₂ ⊢V⦂ Ar)
            → env-C ((γ ⟨ q ⟩ᵉ) ∷ᵉ W') M ≡ resume q M₀ W'
    resumeq q W' =
      cong (λ z → (C-rename (cong-∷-ren (unbox-ren q)) z) [ split-[] ↦ W' ]c)
        (trans (castᶜ-irr (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) ([] ∷ Ar)))
                          refl _)
               (cong (env-Cˢ γ ([] ⟨ ρ ⟩ ∷ Ar))
                     (castᶜ-irr (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) ([] ∷ Ar)) refl M)))

mutual

  -- The value half. Nothing is asked at a base, unit or empty type; a pair is
  -- the pair of the actions' projections; a variable is `env-var`; a
  -- subsumption is `VRed-sub`.
  --
  -- At a lambda the environment moves to the state the Kripke clause offers and
  -- gains the argument (`reachᵉ`, `_∷ᵉ_`) — and that is the whole reason the
  -- reach is *recorded* in the environment: the clause supplies no store for
  -- the later state, and a recorded reach needs none. The action is a `lam`,
  -- so `APP` reduces the clause's application to that body.

  FL-V : ∀ {St Γ A} → (γ : Env St Γ) → Rel-Env γ
       → (V : Γ ⊢V⦂ A)
       -------------------------------
       → VRed A St (env-V γ V)

  FL-V γ pγ (var f x)  = env-var γ pγ x f
  FL-V γ pγ (const c)  = tt
  FL-V γ pγ ⋆          = tt
  FL-V γ pγ true       = tt
  FL-V γ pγ false      = tt

  FL-V {A = A |×| B} γ pγ ⦉ V , W ⦊ =
      VRed-≡ᵛ A (sym (cong fstᵛ (env-Vˢ-pair γ [] V W))) (FL-V γ pγ V)
    , VRed-≡ᵛ B (sym (cong sndᵛ (env-Vˢ-pair γ [] V W))) (FL-V γ pγ W)

  FL-V {A = A ⇒ (B ‼ ε)} γ pγ (lam M) q W pW =
    subst (λ z → CRed' B ε _ (reach-val q z · W)) (sym (env-Vˢ-lam γ [] M))
      (CRed-expand APP (FL-C (reachᵉ γ q ∷ᵉ W) (pγ , pW) M))

  FL-V {A = A} γ pγ (subV V p) =
    VRed-≡ᵛ A (sym (env-Vˢ-sub γ [] V)) (VRed-sub p (env-V γ V) (FL-V γ pγ V))

  -- The computation half. `return` is a weak head normal form; subsumption,
  -- application and `delay` are head expansion off their own rule; `absurd` is
  -- vacuous, since no value of the empty type lives over a state context.
  --
  -- Application instantiates the function's Kripke clause at the state it
  -- already stands in, and `delay` at the reach the lock it passes gives. In
  -- both, the renaming the clause inserts is identity-like, so the reduct is
  -- the action itself up to `_≡_`.

  FL-C : ∀ {St Γ A ε} → (γ : Env St Γ) → Rel-Env γ
       → (M : Γ ⊢C⦂ A ‼ ε)
       -------------------------------
       → CRed' A ε St (env-C γ M)

  FL-C γ pγ (return V) =
    subst (CRed' _ _ _) (sym (env-Cˢ-ret γ [] V)) (cred-ret refl ε* (FL-V γ pγ V))

  FL-C γ pγ (subC M (p ‼ₛ q)) =
    subst (CRed' _ _ _) (sym (env-Cˢ-sub γ [] M))
      (CRed'-sub p q (FL-C γ pγ M))

  FL-C γ pγ (absurd V) = ⊥-elim (empty-not-value (env-V γ V))

  -- `if` is head expansion along whichever run the scrutinee licenses: over a
  -- state context a boolean reaches one of the two branches
  -- (`bool-canonical`).

  FL-C γ pγ (if V `then M `else N) with bool-canonical (env-V γ V)
  ... | inj₁ rs =
    subst (CRed' _ _ _) (sym (env-Cˢ-if γ [] V M N))
      (CRed-expand* rs (FL-C γ pγ M))
  ... | inj₂ rs =
    subst (CRed' _ _ _) (sym (env-Cˢ-if γ [] V M N))
      (CRed-expand* rs (FL-C γ pγ N))

  FL-C γ pγ (V · W) =
    subst (CRed' _ _ _) (sym (env-Cˢ-app γ [] V W))
      (subst (λ z → CRed' _ _ _ (z · env-V γ W))
             (V-rename-id-≡ reach-renᵘ-id-≐ʳ (env-V γ V))
             (FL-V γ pγ V reach-id (env-V γ W) (FL-V γ pγ W)))

  FL-C {St = St} γ pγ (delay τ M) =
    subst (CRed' _ _ _) (sym (env-Cˢ-delay γ [] M))
      (CRed-expand DELAY
        (CRed-≡ᶜ
          (C-rename-id-≡ unbox-ren-delay-≐ʳ (env-Cˢ γ ([] ⟨ of-natʳ τ ⟩) M))
          (subst (CRed' _ _ _) eqδ (FL-C (γ ⟨ delay-reach ⟩ᵉ) pγ M))))
    where
      eqδ = cong (C-rename (unbox-ren (delay-reach {of-natʳ τ} {St})))
              (trans
                (castᶜ-irr (sym (++ᶜ-assoc (toCtx St) ([] ⟨ of-natʳ τ ⟩) []))
                           refl _)
                (cong (env-Cˢ γ ([] ⟨ of-natʳ τ ⟩))
                      (castᶜ-irr (++ᶜ-assoc _ ([] ⟨ of-natʳ τ ⟩) []) refl M)))

  -- Sequencing: `env-Cˢ-seq` splits the action, `seq-CRed` runs the scrutinee and
  -- then the sequel. The environment the sequel needs is `(γ ⟨ q ⟩ᵉ) ∷ᵉ V` — and
  -- `env-Cˢ (γ ⟨ q ⟩ᵉ) ([] ∷ A)` *is* `C-rename (cong-∷-ren (unbox-ren q))` of the
  -- action at suffix `[] ⟨ mapᵉ ε₁ ⟩ ∷ A`, definitionally (both of `env-Cˢ`'s
  -- casts are `refl` at the empty suffix), so only `env-Cˢ-head` is needed.

  FL-C {St = St} {ε = ε} γ pγ (_⨟_ {A = A} {ε = ε₁} M N) =
    subst (CRed' _ _ St) (sym (env-Cˢ-seq γ [] M N))
      (seq-CRed (env-Cˢ γ ([] ⟨ mapᵉ ε₁ ⟩ ∷ A) N) (FL-C γ pγ M)
        (λ q V pV →
           subst (CRed' _ _ _) (sym (env-Cˢ-head (γ ⟨ q ⟩ᵉ) N V))
                 (FL-C ((γ ⟨ q ⟩ᵉ) ∷ᵉ V) (pγ , pV) N)))

  FL-C γ pγ (handle M `with H `in N) =
    FL-handle γ pγ M H N (FL-C γ pγ M)
      (λ γ' pγ' → FL-C γ' pγ' (H _ _)) (λ γ' pγ' → FL-C γ' pγ' N)

  FL-C γ pγ (match V `in M) =
    FL-match γ pγ V M (FL-V γ pγ V) (λ γ' pγ' → FL-C γ' pγ' M)

  FL-C γ pγ (perform op V M) =
    FL-perform γ pγ V M (FL-V γ pγ V) (λ γ' pγ' → FL-C γ' pγ' M)

  FL-C γ pγ (box V M) =
    FL-box γ pγ V M (λ γ' pγ' → FL-V γ' pγ' V) (λ γ' pγ' → FL-C γ' pγ' M)

  FL-C γ pγ (unbox x rel p M) =
    FL-unbox γ pγ x rel p M (λ γ' pγ' → FL-C γ' pγ' M)

-- A reducible computation halts: its run *is* the evaluation, and which of the
-- two shapes it halts in is which `CRed` constructor it is. The reducibility
-- of the components plays no part — normalization is all that is read off.

CRed-halts : ∀ {s} {P : VPred s} {A ε} {e : shapeᵛ A ≡ s} {St : 𝕊 []}
           → {M : toCtx St ⊢C⦂ A ‼ ε}
           → CRed s P e ε St M
           --------------------
           → Halts (⟨ St , M ⟩)

CRed-halts (cred-ret _ rs _)  = halts-ret (ret-whnf _ _ _ rs)
CRed-halts (cred-op _ rs _ _) = halts-op (op-whnf _ _ _ _ _ _ rs)

-- A closed program is reducible at the empty state: `Γ = []`, `St = ∅`, and
-- `toCtx ∅` has no variables to make reducible (`SRed-∅`).

normalize : ∀ {A ε} → (M : Prog A ε) → CRed' A ε ∅ M
normalize M = subst (CRed' _ _ ∅) (env-C-id M) (FL-C ⌊ ∅ ⌋ SRed-∅ M)

-- Hence every closed program reaches a weak head normal form: it returns a
-- value, or it gets stuck on an unhandled operation.

halts : ∀ {A ε} → (M : Prog A ε) → Halts (⟨ ∅ , M ⟩)
halts M = CRed-halts (normalize M)
