------------------------------------------------------------------------
-- Weak-head normalization: the fundamental lemma.                    --
--                                                                    --
-- Recursion is primitive recursion on a natural number or a list,    --
-- so a `recℕ` terminates by induction on the numeral its scrutinee   --
-- runs to, a `recL` by induction on the reducibility of its          --
-- scrutinee's decomposition; everything else terminates              --
-- syntactically. Reducibility is needed, since substitution can grow --
-- a term.                                                            --
--                                                                    --
-- The `handle` case is an induction on the scrutinee's `CRed`        --
-- derivation: each `HANDLE-OP` consumes one resumption premise.      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (inj₁; inj₂; [_,_]′)
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

-- Sum elimination: the scrutinee's reducibility names its injection and gives
-- the payload's reducibility; `case+-run` reaches that branch with the payload
-- substituted, which is the action at the environment extended by it.

FL-case+ : ∀ {St Γ A B D ε} → (γ : Env St Γ) → Rel-Env γ
         → (V : Γ ⊢V⦂ A |+| B)
         → (M : Γ ∷ A ⊢C⦂ D ‼ ε) → (N : Γ ∷ B ⊢C⦂ D ‼ ε)
         → VRed (A |+| B) St (env-V γ V)
         → (∀ {St'} → (γ' : Env St' (Γ ∷ A)) → Rel-Env γ'
              → CRed' D ε St' (env-C γ' M))
         → (∀ {St'} → (γ' : Env St' (Γ ∷ B)) → Rel-Env γ'
              → CRed' D ε St' (env-C γ' N))
         --------------------------------------------------------------
         → CRed' D ε St (env-C γ (case+ V `inl M `inr N))

FL-case+ {St = St} {A = A} {B = B} {D = D} {ε = ε} γ pγ V M N pV pM pN =
  subst (CRed' _ _ St) (sym (env-Cˢ-case+ γ [] V M N))
    (go (case+-run U M₀ N₀) pV)
  where
    U  = env-V γ V
    M₀ = env-Cˢ γ ([] ∷ A) M
    N₀ = env-Cˢ γ ([] ∷ B) N

    go : ∀ {s}
       → [ (λ W → ⟨ St , case+ U `inl M₀ `inr N₀ ⟩ ↝* ⟨ St , M₀ [ split-[] ↦ W ]c ⟩)
         , (λ W → ⟨ St , case+ U `inl M₀ `inr N₀ ⟩ ↝* ⟨ St , N₀ [ split-[] ↦ W ]c ⟩)
         ]′ s
       → VRed⊎ (VRed A St) (VRed B St) s
       → CRed' D ε St (case+ U `inl M₀ `inr N₀)
    go rs (red-inl {W} pW) = CRed-expand* rs (pM (γ ∷ᵉ W) (pγ , pW))
    go rs (red-inr {W} pW) = CRed-expand* rs (pN (γ ∷ᵉ W) (pγ , pW))

-- Primitive recursion: induction on the scrutinee, which over a state context
-- is a numeral up to subsumption. At a successor `RECℕ-SUCC` sequences the
-- recursion at the predecessor, reducible by induction, with one unfolding of
-- the step; `seq-CRed` runs the two. The unfolding at the sequel's reach and
-- result is the action at the environment the step's context describes: the
-- barrier entered at the current state (`barrier-reach`, the renaming the
-- unfolding crosses it by), the predecessor, the reach, and the result.

FL-recℕ : ∀ {St Γ B ε} → (γ : Env St Γ) → Rel-Env γ
        → (V : Γ ⊢V⦂ Nat) → (M : Γ ⊢C⦂ B ‼ ε)
        → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
        → (p : ε ·ₑ ε ≾ₑ ε)
        → CRed' B ε St (env-C γ M)
        → (∀ {St'} → (γ' : Env St' ((Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B))
             → Rel-Env γ' → CRed' B ε St' (env-C γ' N))
        --------------------------------------------------------------
        → CRed' B ε St (env-C γ (recℕ V M N p))

FL-recℕ {St = St} {B = B} {ε = ε} γ pγ V M N p pM pN =
  subst (CRed' _ _ St) (sym (env-Cˢ-recℕ γ [] V M N p)) (go (env-V γ V))
  where
    M₀ = env-C γ M
    N₀ = env-Cˢ γ (([] ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B) N

    go : (U : toCtx St ⊢V⦂ Nat) → CRed' B ε St (recℕ U M₀ N₀ p)
    go (var f x)     = ⊥-elim (Nat-not-in-toCtx x)
    go zero          = CRed-expand RECℕ-ZERO pM
    go (subV U Natₛ) = CRed-expand SUB-RECℕ (go U)
    go (succ W)      =
      CRed-expand RECℕ-SUCC
        (CRed'-sub (<:ᵛ-refl B) p (seq-CRed (recℕ-step W N₀) (go W) cont))
      where
        cont : ∀ {St₁ : 𝕊 []} → (q : St ⊑ₛ[ mapᵉ ε ] St₁)
             → (U : toCtx St₁ ⊢V⦂ B) → VRed B St₁ U
             → CRed' B ε St₁
                 ((C-rename (cong-∷-ren (unbox-ren q)) (recℕ-step W N₀))
                    [ split-[] ↦ U ]c)
        cont q U pU =
          subst (CRed' _ _ _)
            (cong (λ z → (C-rename (cong-∷-ren (unbox-ren q))
                            (z [ split-∷ (split-⟨⟩ split-[]) ↦ W ]c))
                           [ split-[] ↦ U ]c)
                  (C-rename-≡ (cong-ren-≐ʳ (([] ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B)
                                           barrier-reach-≐ʳ) N₀))
            (pN ((((γ ⟨ barrier-reach ⟩ᵉ) ∷ᵉ W) ⟨ q ⟩ᵉ) ∷ᵉ U) ((pγ , tt) , pU))

-- List elimination: `CASEL` reduces at the scrutinee's decomposition, whose
-- reducibility names the branch; the `cons` branch substitutes the head and
-- the tail in the opposite order from the environment, as for `match`.

FL-caseL : ∀ {St Γ A D ε} → (γ : Env St Γ) → Rel-Env γ
         → (V : Γ ⊢V⦂ |List| A)
         → (M : Γ ⊢C⦂ D ‼ ε) → (N : Γ ∷ A ∷ |List| A ⊢C⦂ D ‼ ε)
         → VRed (|List| A) St (env-V γ V)
         → CRed' D ε St (env-C γ M)
         → (∀ {St'} → (γ' : Env St' (Γ ∷ A ∷ |List| A)) → Rel-Env γ'
              → CRed' D ε St' (env-C γ' N))
         --------------------------------------------------------------
         → CRed' D ε St (env-C γ (caseL V `nil M `cons N))

FL-caseL {St = St} {A = A} {D = D} {ε = ε} γ pγ V M N pV pM pN =
  subst (CRed' _ _ St) (sym (env-Cˢ-caseL γ [] V M N))
    (CRed-expand CASEL (go (listᵛ (env-V γ V)) pV))
  where
    M₀ = env-C γ M
    N₀ = env-Cˢ γ ([] ∷ A ∷ |List| A) N

    go : (l : ListView (toCtx St) A) → VRedL (VRed A St) l
       → CRed' D ε St (caseL-reduct l M₀ N₀)
    go (inj₁ tt)      red-nil          = pM
    go (inj₂ (W , L)) (red-cons pW pL) =
      CRed-≡ᶜ (sym (sub-swap-C [] N₀ L W)) (pN ((γ ∷ᵉ W) ∷ᵉ L) ((pγ , pW) , pL))

-- Primitive recursion on lists: induction on the reducibility of the
-- scrutinee's decomposition. At a head and a tail `RECL` sequences the
-- recursion at the tail, reducible by induction, with one unfolding of the
-- step, as for `recℕ`; the environment the unfolding describes is the barrier,
-- the head, the tail, the reach and the result.

FL-recL : ∀ {St Γ A B ε} → (γ : Env St Γ) → Rel-Env γ
        → (V : Γ ⊢V⦂ |List| A) → (M : Γ ⊢C⦂ B ‼ ε)
        → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
        → (p : ε ·ₑ ε ≾ₑ ε)
        → VRed (|List| A) St (env-V γ V)
        → CRed' B ε St (env-C γ M)
        → (∀ {St'} → (γ' : Env St' ((Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B))
             → Rel-Env γ' → CRed' B ε St' (env-C γ' N))
        --------------------------------------------------------------
        → CRed' B ε St (env-C γ (recL V M N p))

FL-recL {St = St} {A = A} {B = B} {ε = ε} γ pγ V M N p pV pM pN =
  subst (CRed' _ _ St) (sym (env-Cˢ-recL γ [] V M N p))
    (CRed-expand RECL (go (listᵛ (env-V γ V)) pV))
  where
    M₀ = env-C γ M
    N₀ = env-Cˢ γ (([] ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B) N

    go : (l : ListView (toCtx St) A) → VRedL (VRed A St) l
       → CRed' B ε St (recL-reduct l M₀ N₀ p)
    go (inj₁ tt)      red-nil          = pM
    go (inj₂ (W , L)) (red-cons pW pL) =
      CRed'-sub (<:ᵛ-refl B) p
        (seq-CRed (recL-step W L N₀) rec cont)
      where
        rec : CRed' B ε St (recL L M₀ N₀ p)
        rec = CRed-expand RECL (go (listᵛ L) pL)

        cont : ∀ {St₁ : 𝕊 []} → (q : St ⊑ₛ[ mapᵉ ε ] St₁)
             → (U : toCtx St₁ ⊢V⦂ B) → VRed B St₁ U
             → CRed' B ε St₁
                 ((C-rename (cong-∷-ren (unbox-ren q)) (recL-step W L N₀))
                    [ split-[] ↦ U ]c)
        cont q U pU =
          subst (CRed' _ _ _)
            (cong (λ z → (C-rename (cong-∷-ren (unbox-ren q))
                            ((z [ split-∷ (split-⟨⟩ (split-∷ split-[])) ↦ W ]c)
                                [ split-∷ (split-⟨⟩ split-[]) ↦ L ]c))
                           [ split-[] ↦ U ]c)
                  (C-rename-≡ (cong-ren-≐ʳ (([] ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B)
                                           barrier-reach-≐ʳ) N₀))
            (pN (((((γ ⟨ barrier-reach ⟩ᵉ) ∷ᵉ W) ∷ᵉ L) ⟨ q ⟩ᵉ) ∷ᵉ U)
                (((pγ , pW) , pL) , pU))

-- Handling: `env-Cˢ-handle` splits the action, `handle-CRed` runs the scrutinee
-- and then the clauses and the sequel.
--
-- The sequel premise is `FL-C`'s at `(γ ⟨ q ⟩ᵉ) ∷ᵉ V`, as for sequencing.
--
-- The clause premise is reached at `St₁ ∷ₛ V₀`, its continuation binder being
-- the fresh cell: the environment `liftᵉ V₀ ((γ ⟨ q ⟩ᵉ) ∷ᵉ W)`, with
-- `Rel-Env` `((pγ , pW) , bv)`.

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

-- Boxing: `BOX` allocates, and the reduct lives over the new state's context, so
-- the environment keeps the binder as the fresh cell (`liftᵉ`) rather than
-- substituting for it. The reduct is the action at `liftᵉ V₀ γ`, and its
-- `Rel-Env` is the boxed value's reducibility at every state the lock permits.

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

  -- The value half. Nothing is asked at a base, unit, boolean, natural-number
  -- or empty type; a pair is the pair of the actions' projections; an
  -- injection is its payload; a variable is `env-var`; a subsumption is
  -- `VRed-sub`.
  --
  -- At a lambda the environment moves to the state the Kripke clause offers and
  -- gains the argument (`reachᵉ`, `_∷ᵉ_`). The action is a `lam`, so `APP`
  -- reduces the clause's application to that body.

  FL-V : ∀ {St Γ A} → (γ : Env St Γ) → Rel-Env γ
       → (V : Γ ⊢V⦂ A)
       -------------------------------
       → VRed A St (env-V γ V)

  FL-V γ pγ (var f x)  = env-var γ pγ x f
  FL-V γ pγ (const c)  = tt
  FL-V γ pγ ⋆          = tt
  FL-V γ pγ true       = tt
  FL-V γ pγ false      = tt
  FL-V γ pγ zero       = tt
  FL-V γ pγ (succ V)   = tt

  FL-V {A = A |×| B} γ pγ ⦉ V , W ⦊ =
      VRed-≡ᵛ A (sym (cong fstᵛ (env-Vˢ-pair γ [] V W))) (FL-V γ pγ V)
    , VRed-≡ᵛ B (sym (cong sndᵛ (env-Vˢ-pair γ [] V W))) (FL-V γ pγ W)

  FL-V {A = A |+| B} γ pγ (inl V) =
    subst (VRed (A |+| B) _) (sym (env-Vˢ-inl γ [] V)) (red-inl (FL-V γ pγ V))

  FL-V {A = A |+| B} γ pγ (inr V) =
    subst (VRed (A |+| B) _) (sym (env-Vˢ-inr γ [] V)) (red-inr (FL-V γ pγ V))

  FL-V {A = |List| A} γ pγ nil =
    subst (VRed (|List| A) _) (sym (env-Vˢ-nil γ [])) red-nil

  FL-V {A = |List| A} γ pγ (cons V W) =
    subst (VRed (|List| A) _) (sym (env-Vˢ-cons γ [] V W))
      (red-cons (FL-V γ pγ V) (FL-V γ pγ W))

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

  -- `cmp` is head expansion off `CMP`, whose reduct returns a boolean.

  FL-C γ pγ (cmp ⋈ V W et) =
    subst (CRed' _ _ _) (sym (env-Cˢ-cmp γ [] ⋈ V W et))
      (CRed-expand {e₀ = refl} CMP (cred-ret refl ε* tt))

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

  -- `caseℕ` likewise (`nat-canonical`); the successor branch receives the
  -- predecessor, reducible as every natural number is.

  FL-C γ pγ (caseℕ V `zero M `succ N) with nat-canonical (env-V γ V)
  ... | inj₁ rs =
    subst (CRed' _ _ _) (sym (env-Cˢ-caseℕ γ [] V M N))
      (CRed-expand* rs (FL-C γ pγ M))
  ... | inj₂ (W , rs) =
    subst (CRed' _ _ _) (sym (env-Cˢ-caseℕ γ [] V M N))
      (CRed-expand* rs (FL-C (γ ∷ᵉ W) (pγ , tt) N))

  FL-C γ pγ (V · W) =
    subst (CRed' _ _ _) (sym (env-Cˢ-app γ [] V W))
      (subst (λ z → CRed' _ _ _ (z · env-V γ W))
             (V-rename-id-≡ reach-renᵘ-id-≐ʳ (env-V γ V))
             (FL-V γ pγ V reach-id (env-V γ W) (FL-V γ pγ W)))

  FL-C {St = St} γ pγ (delay τ M) =
    subst (CRed' _ _ _) (sym (env-Cˢ-delay γ [] M))
      (CRed-expand DELAY
        (CRed-≡ᶜ
          (C-rename-id-≡ unbox-ren-delay-≐ʳ (env-Cˢ γ ([] ⟨ of-durʳ τ ⟩) M))
          (subst (CRed' _ _ _) eqδ (FL-C (γ ⟨ delay-reach ⟩ᵉ) pγ M))))
    where
      eqδ = cong (C-rename (unbox-ren (delay-reach {of-durʳ τ} {St})))
              (trans
                (castᶜ-irr (sym (++ᶜ-assoc (toCtx St) ([] ⟨ of-durʳ τ ⟩) []))
                           refl _)
                (cong (env-Cˢ γ ([] ⟨ of-durʳ τ ⟩))
                      (castᶜ-irr (++ᶜ-assoc _ ([] ⟨ of-durʳ τ ⟩) []) refl M)))

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

  FL-C γ pγ (recℕ V M N p) =
    FL-recℕ γ pγ V M N p (FL-C γ pγ M) (λ γ' pγ' → FL-C γ' pγ' N)

  FL-C γ pγ (caseL V `nil M `cons N) =
    FL-caseL γ pγ V M N (FL-V γ pγ V) (FL-C γ pγ M) (λ γ' pγ' → FL-C γ' pγ' N)

  FL-C γ pγ (recL V M N p) =
    FL-recL γ pγ V M N p (FL-V γ pγ V) (FL-C γ pγ M) (λ γ' pγ' → FL-C γ' pγ' N)

  FL-C γ pγ (match V `in M) =
    FL-match γ pγ V M (FL-V γ pγ V) (λ γ' pγ' → FL-C γ' pγ' M)

  FL-C γ pγ (case+ V `inl M `inr N) =
    FL-case+ γ pγ V M N (FL-V γ pγ V)
      (λ γ' pγ' → FL-C γ' pγ' M) (λ γ' pγ' → FL-C γ' pγ' N)

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
