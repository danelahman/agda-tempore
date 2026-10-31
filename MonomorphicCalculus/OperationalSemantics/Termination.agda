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
-- A handler's case is an induction on the scrutinee's `CRed`         --
-- derivation: each `HANDLE-OP` consumes one resumption premise.      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Termination (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.OperationalSemantics.Termination.Bind Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Environment Spec
open import MonomorphicCalculus.OperationalSemantics.Evaluation Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Handle Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Reducibility Spec
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.Syntax.Substitution.At         Spec
open import MonomorphicCalculus.Syntax.Substitution.Clauses    Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec

-- Induction on the typing derivation, mutually for values and computations.
-- Five computation cases are split off as lemmas taking the induction
-- hypotheses they need: for a binding subterm, at every environment, since the
-- state the subterm is reached at is not the one the case starts from.
-- Sequencing is `Termination.Bind`'s `seq-CRed`.

-- Unboxing: read the store. `env-Cˢ-unbox` sends the action to an `unbox` at
-- the cell the environment sends this one to, `UNBOX` reads that cell, and the
-- value read (the raw read at the cell's declared payload type, subsumed once
-- along the composite the action accumulates) is reducible at the current
-- state.

fund-unbox : ∀ {𝕊 Γ A A₀ D ρ σ ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
           → (x : [ ρ ] A₀ ∈[ σ ] Γ) → (rel : σ ≾ᵣ ρ) → (p : A₀ <:ᵛ A)
           → (M : Γ ∷ A ⊢ᶜ⦂ D ! ε)
           → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ∷ A)) → Rel-Env γ'
                → CRed' D ε 𝕊' (env-C γ' M))
           --------------------------------------------------------------
           → CRed' D ε 𝕊 (env-C γ (unbox x rel p M))

fund-unbox {𝕊 = 𝕊} {A = A} {A₀ = A₀} {ρ = ρ} {σ = σ} γ pγ x rel p M pM =
  CRed-≡ᶜ (sym (env-Cˢ-unbox γ [] x rel p M rel₁ p₁))
          (CRed-expand UNBOX (pM (γ ∷ᵉ U) (pγ , pU)))
  where
    rel₁ = env-cell-rel γ [] (σ , x) rel
    p₁   = <:ᵛ-trans (env-cell-typ γ [] (σ , x)) p

    Y = unbox-lookup 𝕊 (rvar-pos (env-cell γ [] (σ , x))) rel₁

    U = subV Y p₁

    store : VRed (rvar-type (env-cell γ [] (σ , x))) 𝕊 Y
    store = env-cell-val γ pγ (σ , x) _ (env-cell-push γ [] (σ , x)) rel₁

    pU : VRed A 𝕊 U
    pU = VRed-sub p₁ Y store

-- Matching: `MATCH` fires at any scrutinee, substituting its two projections
-- in the opposite order from the environment: the rule replaces `B` (its
-- value weakened past `A`) and then `A`, the action replaces `A` with `B`
-- riding in the suffix and then `B`. That is `sub-swap-C` at the empty
-- suffix, where both orders' casts and boundary variables reduce.

fund-match : ∀ {𝕊 Γ A B D ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
           → (V : Γ ⊢ᵛ⦂ A |×| B) → (M : Γ ∷ A ∷ B ⊢ᶜ⦂ D ! ε)
           → VRed (A |×| B) 𝕊 (env-V γ V)
           → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ∷ A ∷ B)) → Rel-Env γ'
                → CRed' D ε 𝕊' (env-C γ' M))
           --------------------------------------------------------------
           → CRed' D ε 𝕊 (env-C γ (match V `with M))

fund-match {𝕊 = 𝕊} {A = A} {B = B} γ pγ V M (p₁ , p₂) pM =
  subst (CRed' _ _ 𝕊) (sym (env-Cˢ-match γ [] V M))
    (CRed-expand MATCH
      (CRed-≡ᶜ (sym step) (pM ((γ ∷ᵉ U₁) ∷ᵉ U₂) ((pγ , p₁) , p₂))))
  where
    M₀ = env-Cˢ γ ([] ∷ A ∷ B) M

    U₁ = fstᵛ (env-V γ V)
    U₂ = sndᵛ (env-V γ V)

    step : (M₀ [ split-[] ↦ V-rename wk-ren U₂ ]c) [ split-[] ↦ U₁ ]c
         ≡ env-C ((γ ∷ᵉ U₁) ∷ᵉ U₂) M
    step = sub-swap-C [] M₀ U₂ U₁

-- Sum elimination: `MATCH+` reduces at the scrutinee's decomposition, whose
-- reducibility names the branch and gives the payload's; that branch with the
-- payload substituted is the action at the environment extended by it.

fund-match+ : ∀ {𝕊 Γ A B D ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
            → (V : Γ ⊢ᵛ⦂ A |+| B)
            → (M : Γ ∷ A ⊢ᶜ⦂ D ! ε) → (N : Γ ∷ B ⊢ᶜ⦂ D ! ε)
            → VRed (A |+| B) 𝕊 (env-V γ V)
            → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ∷ A)) → Rel-Env γ'
                 → CRed' D ε 𝕊' (env-C γ' M))
            → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ∷ B)) → Rel-Env γ'
                 → CRed' D ε 𝕊' (env-C γ' N))
            --------------------------------------------------------------
            → CRed' D ε 𝕊 (env-C γ (match+ V `inl M `inr N))

fund-match+ {𝕊 = 𝕊} {A = A} {B = B} {D = D} {ε = ε} γ pγ V M N pV pM pN =
  subst (CRed' _ _ 𝕊) (sym (env-Cˢ-match+ γ [] V M N))
    (CRed-expand MATCH+ (go (injᵛ (env-V γ V)) pV))
  where
    M₀ = env-Cˢ γ ([] ∷ A) M
    N₀ = env-Cˢ γ ([] ∷ B) N

    go : (s : (toCtx 𝕊 ⊢ᵛ⦂ A) ⊎ (toCtx 𝕊 ⊢ᵛ⦂ B)) → VRed⊎ (VRed A 𝕊) (VRed B 𝕊) s
       → CRed' D ε 𝕊 (match+-reduct s M₀ N₀)
    go _ (red-inl {W} pW) = pM (γ ∷ᵉ W) (pγ , pW)
    go _ (red-inr {W} pW) = pN (γ ∷ᵉ W) (pγ , pW)

-- Primitive recursion: induction on the scrutinee, which over a state context
-- is a numeral up to subsumption. At a successor `RECℕ-SUCC` sequences the
-- recursion at the predecessor, reducible by induction, with one unfolding of
-- the step; `seq-CRed` runs the two. The unfolding at the sequel's reach and
-- result is the action at the environment the step's context describes: the
-- barrier entered at the current state (`barrier-reach`, the renaming the
-- unfolding crosses it by), the predecessor, the reach, and the result.

fund-recℕ : ∀ {𝕊 Γ B ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
          → (V : Γ ⊢ᵛ⦂ nat) → (M : Γ ⊢ᶜ⦂ B ! ε)
          → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
          → (p : ε ·ₑ ε ≾ₑ ε)
          → CRed' B ε 𝕊 (env-C γ M)
          → (∀ {𝕊'} → (γ' : Env 𝕊' ((Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B))
               → Rel-Env γ' → CRed' B ε 𝕊' (env-C γ' N))
          --------------------------------------------------------------
          → CRed' B ε 𝕊 (env-C γ (recℕ V M N p))

fund-recℕ {𝕊 = 𝕊} {B = B} {ε = ε} γ pγ V M N p pM pN =
  subst (CRed' _ _ 𝕊) (sym (env-Cˢ-recℕ γ [] V M N p)) (go (env-V γ V))
  where
    M₀ = env-C γ M
    N₀ = env-Cˢ γ (([] ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) N

    go : (U : toCtx 𝕊 ⊢ᵛ⦂ nat) → CRed' B ε 𝕊 (recℕ U M₀ N₀ p)
    go (var f x)     = ⊥-elim (nat-not-in-toCtx x)
    go zero          = CRed-expand RECℕ-ZERO pM
    go (subV U natₛ) = CRed-expand SUB-RECℕ (go U)
    go (succ W)      =
      CRed-expand RECℕ-SUCC
        (CRed'-sub (<:ᵛ-refl B) p (seq-CRed (recℕ-step W N₀) (go W) cont))
      where
        cont : ∀ {𝕊₁ : State []} → (q : 𝕊 ⊑ₛ[ ∣ ε ∣ᵉ ] 𝕊₁)
             → (U : toCtx 𝕊₁ ⊢ᵛ⦂ B) → VRed B 𝕊₁ U
             → CRed' B ε 𝕊₁
                 ((C-rename (cong-∷-ren (unbox-ren q)) (recℕ-step W N₀))
                    [ split-[] ↦ U ]c)
        cont q U pU =
          subst (CRed' _ _ _)
            (cong (λ z → (C-rename (cong-∷-ren (unbox-ren q))
                            (z [ split-∷ (split-⟨⟩ split-[]) ↦ W ]c))
                           [ split-[] ↦ U ]c)
                  (C-rename-≡ (cong-ren-≐ʳ (([] ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B)
                                           barrier-reach-≐ʳ) N₀))
            (pN ((((γ ⟨ barrier-reach ⟩ᵉ) ∷ᵉ W) ⟨ q ⟩ᵉ) ∷ᵉ U) ((pγ , tt) , pU))

-- List elimination: `MATCHL` reduces at the scrutinee's decomposition, whose
-- reducibility names the branch; the `cons` branch substitutes the head and
-- the tail in the opposite order from the environment, as for `match`.

fund-matchL : ∀ {𝕊 Γ A D ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
            → (V : Γ ⊢ᵛ⦂ list A)
            → (M : Γ ⊢ᶜ⦂ D ! ε) → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ D ! ε)
            → VRed (list A) 𝕊 (env-V γ V)
            → CRed' D ε 𝕊 (env-C γ M)
            → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ∷ A ∷ list A)) → Rel-Env γ'
                 → CRed' D ε 𝕊' (env-C γ' N))
            --------------------------------------------------------------
            → CRed' D ε 𝕊 (env-C γ (matchL V `nil M `cons N))

fund-matchL {𝕊 = 𝕊} {A = A} {D = D} {ε = ε} γ pγ V M N pV pM pN =
  subst (CRed' _ _ 𝕊) (sym (env-Cˢ-matchL γ [] V M N))
    (CRed-expand MATCHL (go (listᵛ (env-V γ V)) pV))
  where
    M₀ = env-C γ M
    N₀ = env-Cˢ γ ([] ∷ A ∷ list A) N

    go : (l : ListView (toCtx 𝕊) A) → VRedL (VRed A 𝕊) l
       → CRed' D ε 𝕊 (matchL-reduct l M₀ N₀)
    go (inj₁ tt)      red-nil          = pM
    go (inj₂ (W , L)) (red-cons pW pL) =
      CRed-≡ᶜ (sym (sub-swap-C [] N₀ L W)) (pN ((γ ∷ᵉ W) ∷ᵉ L) ((pγ , pW) , pL))

-- Primitive recursion on lists: induction on the reducibility of the
-- scrutinee's decomposition. At a head and a tail `RECL` sequences the
-- recursion at the tail, reducible by induction, with one unfolding of the
-- step, as for `recℕ`; the environment the unfolding describes is the barrier,
-- the head, the tail, the reach and the result.

fund-recL : ∀ {𝕊 Γ A B ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
          → (V : Γ ⊢ᵛ⦂ list A) → (M : Γ ⊢ᶜ⦂ B ! ε)
          → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
          → (p : ε ·ₑ ε ≾ₑ ε)
          → VRed (list A) 𝕊 (env-V γ V)
          → CRed' B ε 𝕊 (env-C γ M)
          → (∀ {𝕊'} → (γ' : Env 𝕊' ((Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B))
               → Rel-Env γ' → CRed' B ε 𝕊' (env-C γ' N))
          --------------------------------------------------------------
          → CRed' B ε 𝕊 (env-C γ (recL V M N p))

fund-recL {𝕊 = 𝕊} {A = A} {B = B} {ε = ε} γ pγ V M N p pV pM pN =
  subst (CRed' _ _ 𝕊) (sym (env-Cˢ-recL γ [] V M N p))
    (CRed-expand RECL (go (listᵛ (env-V γ V)) pV))
  where
    M₀ = env-C γ M
    N₀ = env-Cˢ γ (([] ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) N

    go : (l : ListView (toCtx 𝕊) A) → VRedL (VRed A 𝕊) l
       → CRed' B ε 𝕊 (recL-reduct l M₀ N₀ p)
    go (inj₁ tt)      red-nil          = pM
    go (inj₂ (W , L)) (red-cons pW pL) =
      CRed'-sub (<:ᵛ-refl B) p
        (seq-CRed (recL-step W L N₀) rec cont)
      where
        rec : CRed' B ε 𝕊 (recL L M₀ N₀ p)
        rec = CRed-expand RECL (go (listᵛ L) pL)

        cont : ∀ {𝕊₁ : State []} → (q : 𝕊 ⊑ₛ[ ∣ ε ∣ᵉ ] 𝕊₁)
             → (U : toCtx 𝕊₁ ⊢ᵛ⦂ B) → VRed B 𝕊₁ U
             → CRed' B ε 𝕊₁
                 ((C-rename (cong-∷-ren (unbox-ren q)) (recL-step W L N₀))
                    [ split-[] ↦ U ]c)
        cont q U pU =
          subst (CRed' _ _ _)
            (cong (λ z → (C-rename (cong-∷-ren (unbox-ren q))
                            ((z [ split-∷ (split-⟨⟩ (split-∷ split-[])) ↦ W ]c)
                                [ split-∷ (split-⟨⟩ split-[]) ↦ L ]c))
                           [ split-[] ↦ U ]c)
                  (C-rename-≡ (cong-ren-≐ʳ (([] ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B)
                                           barrier-reach-≐ʳ) N₀))
            (pN (((((γ ⟨ barrier-reach ⟩ᵉ) ∷ᵉ W) ∷ᵉ L) ⟨ q ⟩ᵉ) ∷ᵉ U)
                (((pγ , pW) , pL) , pU))

-- Handlers: `env-Vˢ-handler` splits the action, and `handler-CRed` runs the
-- handling at the use it is given, from the clause and sequel premises.
--
-- The sequel premise is `fund-c`'s at `(γ ⟨ q ⟩ᵉ) ∷ᵉ V`, as for sequencing.
--
-- The clause premise is reached at `𝕊₁ ∷ₛ V₀`, its continuation binder being
-- the fresh cell: the environment `liftᵉ V₀ ((γ ⟨ q ⟩ᵉ) ∷ᵉ W)`, with
-- `Rel-Env` `((pγ , pW) , bv)`.

fund-handler : ∀ {𝕊 Γ A B ε₁ ε₂} → (γ : Env 𝕊 Γ) → Rel-Env γ
             → (N : Γ ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂)
             → (H : Fam B (Γ ⟨ ⊤ᵣ ⟩))
             → (∀ {𝕊'} {op : Op} {ε₃ : E}
                  → (γ' : Env 𝕊' (Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                    ∷ [ ∣ op-grade op ∣ᵉ ]
                                        (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)))
                  → Rel-Env γ'
                  → CRed' B (op-grade op ·ₑ ε₃) 𝕊' (env-C γ' (H op ε₃)))
             → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A)) → Rel-Env γ'
                  → CRed' B ε₂ 𝕊' (env-C γ' N))
             → ∀ {s A₀ ε₀ B₀ ε₀'} {U : toCtx 𝕊 ⊢ᵛ⦂ (A₀ ! ε₀) ⇛ (B₀ ! ε₀')}
             → Use (env-V γ (handler N H)) U
             → {e : shapeᵛ A₀ ≡ s} → {M : toCtx 𝕊 ⊢ᶜ⦂ A₀ ! ε₀}
             → CRedˢ' s e ε₀ 𝕊 M
             --------------------------------------------------------------
             → CRed' B₀ (ε₀ ·ₑ ε₀') 𝕊 (handle M `with U)

fund-handler {𝕊 = 𝕊} {Γ = Γ} {A = A} {B = B} {ε₁ = ε₁} γ pγ N H pH pN u pM =
  handler-CRed clause sequel (subst (λ z → Use z _) (env-Vˢ-handler γ [] N H) u) pM
  where
    Hγ : Fam B (toCtx 𝕊 ⟨ ⊤ᵣ ⟩)
    Hγ = env-Hˢ γ [] H

    clause : Clause-Prem B 𝕊 Hγ
    clause {𝕊₁} {op} {ε₃} q V₀ bv W pW =
      subst (CRed' _ _ _) (sym (env-Hˢ-fired γ q H V₀ W))
        (pH (liftᵉ V₀ ((γ ⟨ q ⟩ᵉ) ∷ᵉ W)) ((pγ , pW) , bv))

    sequel : Seq-Prem (env-Cˢ γ ([] ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A) N)
    sequel q V pV =
      subst (CRed' _ _ _) (sym (env-Cˢ-head (γ ⟨ q ⟩ᵉ) N V))
            (pN ((γ ⟨ q ⟩ᵉ) ∷ᵉ V) (pγ , pV))

-- Boxing: `BOX` allocates, and the reduct lives over the new state's context, so
-- the environment keeps the binder as the fresh cell (`liftᵉ`) rather than
-- substituting for it. The reduct is the action at `liftᵉ V₀ γ`, and its
-- `Rel-Env` is the boxed value's reducibility at every state the lock permits.

fund-box : ∀ {𝕊 Γ A D ρ ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
         → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A) → (M : Γ ∷ [ ρ ] A ⊢ᶜ⦂ D ! ε)
         → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ⟨ ρ ⟩)) → Rel-Env γ'
              → VRed A 𝕊' (env-V γ' V))
         → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ∷ [ ρ ] A)) → Rel-Env γ'
              → CRed' D ε 𝕊' (env-C γ' M))
         --------------------------------------------------------------
         → CRed' D ε 𝕊 (env-C γ (box _ V M))

fund-box {𝕊 = 𝕊} {Γ = Γ} {A = A} {ρ = ρ} γ pγ V M pV pM =
  subst (CRed' _ _ 𝕊) (sym (env-Cˢ-box γ [] V M))
    (CRed-expand BOX (pM (liftᵉ V₀ γ) (pγ , cell)))
  where
    V' = env-Vˢ γ ([] ⟨ ρ ⟩) V
    V₀ = V-rename (eq-ren (sym (++ᶜ-identityˡ {toCtx 𝕊 ⟨ ρ ⟩}))) V'

    -- the two `eq-ren`s the allocation and the lookup insert cancel
    cancel : ∀ {𝕊'} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
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
                (eq-ren-∘-≐ʳ (sym (++ᶜ-identityˡ {toCtx 𝕊 ⟨ ρ ⟩}))
                            ++ᶜ-identityˡ)
                (eq-ren-≐ʳ _ refl))))
          V')

    cell : ∀ {𝕊'} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
         → VRed A 𝕊' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V₀)
    cell q = VRed-≡ᵛ A (sym (cancel q)) (pV (γ ⟨ q ⟩ᵉ) pγ)

-- Performing: already a weak head normal form, so this is `cred-op` at the empty
-- run. Its resumption premise is the induction hypothesis at the environment a
-- `resume` amounts to (the lock the operation is performed under, matched by
-- the resumption's own reach, and the arity value on top), where the action is
-- the resumption, both of `env-Cˢ`'s casts being `refl` at the empty suffix.

fund-perform : ∀ {𝕊 Γ A ε} {op : Op} → (γ : Env 𝕊 Γ) → Rel-Env γ
             → (V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
             → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                      ⊢ᶜ⦂ A ! ε)
             → VRed ⌜ param op ⌝ᵍ 𝕊 (env-V γ V)
             → (∀ {𝕊'} → (γ' : Env 𝕊' (Γ ⟨ ∣ op-grade op ∣ᵉ ⟩
                                         ∷ ⌜ arity op ⌝ᵍ))
                  → Rel-Env γ' → CRed' A ε 𝕊' (env-C γ' M))
             --------------------------------------------------------------
             → CRed' A (op-grade op ·ₑ ε) 𝕊 (env-C γ (perform op V M))

fund-perform {𝕊 = 𝕊} {Γ = Γ} {op = op} γ pγ V M pV pM =
  subst (CRed' _ _ _) (sym (env-Cˢ-perform γ [] V M))
    (cred-op refl done (VRed→VRedᵍ (param op) (env-V γ V) pV)
      (λ q W' pW' →
         subst (CRed' _ _ _) (resumeq q W')
           (pM ((γ ⟨ q ⟩ᵉ) ∷ᵉ W') (pγ , VRedᵍ→VRed (arity op) W' pW'))))
  where
    ρ  = ∣ op-grade op ∣ᵉ
    Ar = ⌜ arity op ⌝ᵍ
    M₀ = env-Cˢ γ ([] ⟨ ρ ⟩ ∷ Ar) M

    -- the action at the resumption's environment is the resumption, once the
    -- two `++ᶜ`-associativity casts are seen to be the identity
    resumeq : ∀ {𝕊₂ : State []} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊₂)
            → (W' : toCtx 𝕊₂ ⊢ᵛ⦂ Ar)
            → env-C ((γ ⟨ q ⟩ᵉ) ∷ᵉ W') M ≡ resume q M₀ W'
    resumeq q W' =
      cong (λ z → (C-rename (cong-∷-ren (unbox-ren q)) z) [ split-[] ↦ W' ]c)
        (trans (castᶜ-irr (sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ρ ⟩) ([] ∷ Ar)))
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
  -- gains the argument (`reachᵉ`, `_∷ᵉ_`). The action is a `fun`, so `APP`
  -- reduces the clause's application to that body.

  fund-v : ∀ {𝕊 Γ A} → (γ : Env 𝕊 Γ) → Rel-Env γ
         → (V : Γ ⊢ᵛ⦂ A)
         -------------------------------
         → VRed A 𝕊 (env-V γ V)

  fund-v γ pγ (var f x)   = env-var γ pγ x f
  fund-v γ pγ (const B c) = tt
  fund-v γ pγ ⋆           = tt
  fund-v γ pγ true        = tt
  fund-v γ pγ false       = tt
  fund-v γ pγ zero        = tt
  fund-v γ pγ (succ V)    = tt

  fund-v {A = A |×| B} γ pγ ⦉ V , W ⦊ =
      VRed-≡ᵛ A (sym (cong fstᵛ (env-Vˢ-pair γ [] V W))) (fund-v γ pγ V)
    , VRed-≡ᵛ B (sym (cong sndᵛ (env-Vˢ-pair γ [] V W))) (fund-v γ pγ W)

  fund-v {A = A |+| B} γ pγ (inl V) =
    subst (VRed (A |+| B) _) (sym (env-Vˢ-inl γ [] V)) (red-inl (fund-v γ pγ V))

  fund-v {A = A |+| B} γ pγ (inr V) =
    subst (VRed (A |+| B) _) (sym (env-Vˢ-inr γ [] V)) (red-inr (fund-v γ pγ V))

  fund-v {A = list A} γ pγ nil =
    subst (VRed (list A) _) (sym (env-Vˢ-nil γ [])) red-nil

  fund-v {A = list A} γ pγ (cons V W) =
    subst (VRed (list A) _) (sym (env-Vˢ-cons γ [] V W))
      (red-cons (fund-v γ pγ V) (fund-v γ pγ W))

  fund-v {A = A ⇒ (B ! ε)} γ pγ (fun M) q W pW =
    subst (λ z → CRed' B ε _ (reach-val q z · W)) (sym (env-Vˢ-fun γ [] M))
      (CRed-expand APP (fund-c (reachᵉ γ q ∷ᵉ W) (pγ , pW) M))

  -- At a handler the environment moves to the state the Kripke clause offers,
  -- and `fund-handler` handles at the use.

  fund-v {A = (A ! ε) ⇛ (B ! ε')} γ pγ (handler N H) q u M pM =
    CRedˢ'-≡ˢ
      (fund-handler (reachᵉ γ q) pγ N H
        (λ γ' pγ' → fund-c γ' pγ' (H _ _)) (λ γ' pγ' → fund-c γ' pγ' N) u pM)

  fund-v {A = A} γ pγ (subV V p) =
    VRed-≡ᵛ A (sym (env-Vˢ-sub γ [] V)) (VRed-sub p (env-V γ V) (fund-v γ pγ V))

  -- The computation half. `return` is a weak head normal form; subsumption,
  -- application and `delay` are head expansion off their own rule; `absurd` is
  -- vacuous, since no value of the empty type lives over a state context.
  --
  -- Application instantiates the function's Kripke clause at the state it
  -- already stands in, and `delay` at the reach the lock it passes gives. In
  -- both, the renaming the clause inserts is identity-like, so the reduct is
  -- the action itself up to `_≡_`.

  fund-c : ∀ {𝕊 Γ A ε} → (γ : Env 𝕊 Γ) → Rel-Env γ
         → (M : Γ ⊢ᶜ⦂ A ! ε)
         -------------------------------
         → CRed' A ε 𝕊 (env-C γ M)

  fund-c γ pγ (return V) =
    subst (CRed' _ _ _) (sym (env-Cˢ-ret γ [] V)) (cred-ret refl done (fund-v γ pγ V))

  fund-c γ pγ (subC M (p !ₛ q)) =
    subst (CRed' _ _ _) (sym (env-Cˢ-sub γ [] M))
      (CRed'-sub p q (fund-c γ pγ M))

  fund-c γ pγ (absurd V) = ⊥-elim (empty-not-value (env-V γ V))

  -- `cmp` is head expansion off `CMP`, whose reduct returns a boolean.

  fund-c γ pγ (cmp ⋈ V W et) =
    subst (CRed' _ _ _) (sym (env-Cˢ-cmp γ [] ⋈ V W et))
      (CRed-expand {e₀ = refl} CMP (cred-ret refl done tt))

  -- `if` is head expansion along whichever run the scrutinee licenses: over a
  -- state context a boolean reaches one of the two branches
  -- (`bool-canonical`).

  fund-c γ pγ (if V `then M `else N) with bool-canonical (env-V γ V)
  ... | inj₁ rs =
    subst (CRed' _ _ _) (sym (env-Cˢ-if γ [] V M N))
      (CRed-expand* rs (fund-c γ pγ M))
  ... | inj₂ rs =
    subst (CRed' _ _ _) (sym (env-Cˢ-if γ [] V M N))
      (CRed-expand* rs (fund-c γ pγ N))

  -- `matchℕ` likewise (`nat-canonical`); the successor branch receives the
  -- predecessor, reducible as every natural number is.

  fund-c γ pγ (matchℕ V `zero M `succ N) with nat-canonical (env-V γ V)
  ... | inj₁ rs =
    subst (CRed' _ _ _) (sym (env-Cˢ-matchℕ γ [] V M N))
      (CRed-expand* rs (fund-c γ pγ M))
  ... | inj₂ (W , rs) =
    subst (CRed' _ _ _) (sym (env-Cˢ-matchℕ γ [] V M N))
      (CRed-expand* rs (fund-c (γ ∷ᵉ W) (pγ , tt) N))

  fund-c γ pγ (V · W) =
    subst (CRed' _ _ _) (sym (env-Cˢ-app γ [] V W))
      (subst (λ z → CRed' _ _ _ (z · env-V γ W))
             (V-rename-id-≡ reach-renᵘ-id-≐ʳ (env-V γ V))
             (fund-v γ pγ V reach-id (env-V γ W) (fund-v γ pγ W)))

  fund-c {𝕊 = 𝕊} γ pγ (delay τ M) =
    subst (CRed' _ _ _) (sym (env-Cˢ-delay γ [] M))
      (CRed-expand DELAY
        (CRed-≡ᶜ
          (C-rename-id-≡ unbox-ren-delay-≐ʳ (env-Cˢ γ ([] ⟨ ιᵣ τ ⟩) M))
          (subst (CRed' _ _ _) eqδ (fund-c (γ ⟨ delay-reach ⟩ᵉ) pγ M))))
    where
      eqδ = cong (C-rename (unbox-ren (delay-reach {ιᵣ τ} {𝕊})))
              (trans
                (castᶜ-irr (sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ιᵣ τ ⟩) []))
                           refl _)
                (cong (env-Cˢ γ ([] ⟨ ιᵣ τ ⟩))
                      (castᶜ-irr (++ᶜ-assoc _ ([] ⟨ ιᵣ τ ⟩) []) refl M)))

  -- Sequencing: `env-Cˢ-seq` splits the action, `seq-CRed` runs the scrutinee and
  -- then the sequel. The environment the sequel needs is `(γ ⟨ q ⟩ᵉ) ∷ᵉ V`, and
  -- `env-Cˢ (γ ⟨ q ⟩ᵉ) ([] ∷ A)` is `C-rename (cong-∷-ren (unbox-ren q))` of the
  -- action at suffix `[] ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A`, definitionally (both of `env-Cˢ`'s
  -- casts are `refl` at the empty suffix), so only `env-Cˢ-head` is needed.

  fund-c {𝕊 = 𝕊} {ε = ε} γ pγ (_⨟_ {A = A} {ε = ε₁} M N) =
    subst (CRed' _ _ 𝕊) (sym (env-Cˢ-seq γ [] M N))
      (seq-CRed (env-Cˢ γ ([] ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A) N) (fund-c γ pγ M)
        (λ q V pV →
           subst (CRed' _ _ _) (sym (env-Cˢ-head (γ ⟨ q ⟩ᵉ) N V))
                 (fund-c ((γ ⟨ q ⟩ᵉ) ∷ᵉ V) (pγ , pV) N)))

  -- Handling: the handler's Kripke clause at the state it already stands in,
  -- used as itself.

  fund-c γ pγ (handle M `with V) =
    subst (CRed' _ _ _) (sym (env-Cˢ-handle γ [] M V))
      (CRedˢ'-≡ˢ
        (fund-v γ pγ V reach-id
          (subst (λ z → Use z (env-V γ V))
                 (sym (V-rename-id-≡ reach-renᵘ-id-≐ʳ (env-V γ V))) use-id)
          (env-C γ M) (CRedˢ'-≡ˢ (fund-c γ pγ M))))

  fund-c γ pγ (recℕ V M N p) =
    fund-recℕ γ pγ V M N p (fund-c γ pγ M) (λ γ' pγ' → fund-c γ' pγ' N)

  fund-c γ pγ (matchL V `nil M `cons N) =
    fund-matchL γ pγ V M N (fund-v γ pγ V) (fund-c γ pγ M) (λ γ' pγ' → fund-c γ' pγ' N)

  fund-c γ pγ (recL V M N p) =
    fund-recL γ pγ V M N p (fund-v γ pγ V) (fund-c γ pγ M) (λ γ' pγ' → fund-c γ' pγ' N)

  fund-c γ pγ (match V `with M) =
    fund-match γ pγ V M (fund-v γ pγ V) (λ γ' pγ' → fund-c γ' pγ' M)

  fund-c γ pγ (match+ V `inl M `inr N) =
    fund-match+ γ pγ V M N (fund-v γ pγ V)
      (λ γ' pγ' → fund-c γ' pγ' M) (λ γ' pγ' → fund-c γ' pγ' N)

  fund-c γ pγ (perform op V M) =
    fund-perform γ pγ V M (fund-v γ pγ V) (λ γ' pγ' → fund-c γ' pγ' M)

  fund-c γ pγ (box _ V M) =
    fund-box γ pγ V M (λ γ' pγ' → fund-v γ' pγ' V) (λ γ' pγ' → fund-c γ' pγ' M)

  fund-c γ pγ (unbox x rel p M) =
    fund-unbox γ pγ x rel p M (λ γ' pγ' → fund-c γ' pγ' M)

-- A reducible computation halts: its run is the evaluation, and which of the
-- two shapes it halts in is which `CRed` constructor it is. Only normalization
-- is read off; the reducibility of the components plays no part.

CRed-halts : ∀ {s} {P : VPred s} {A ε} {e : shapeᵛ A ≡ s} {𝕊 : State []}
           → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
           → CRed s P e ε 𝕊 M
           --------------------
           → Halts (⟨ 𝕊 ∣ M ⟩)

CRed-halts (cred-ret _ rs _)  = halts-ret (ret-whnf _ _ _ rs)
CRed-halts (cred-op _ rs _ _) = halts-op (op-whnf _ _ _ _ _ _ rs)

-- A closed program is reducible at the empty state: `Γ = []`, `𝕊 = ∅`, and
-- `toCtx ∅` has no variables to make reducible (`SRed-∅`).

normalize : ∀ {A ε} → (M : Closed A ε) → CRed' A ε ∅ M
normalize M = subst (CRed' _ _ ∅) (env-C-id M) (fund-c ⌊ ∅ ⌋ SRed-∅ M)

-- Hence every closed program reaches a weak head normal form: it returns a
-- value, or it gets stuck on an unhandled operation.

halts : ∀ {A ε} → (M : Closed A ε) → Halts (⟨ ∅ ∣ M ⟩)
halts M = CRed-halts (normalize M)
