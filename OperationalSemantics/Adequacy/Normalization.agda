------------------------------------------------------------------------
-- Weak-head normalization: the fundamental lemma.                    --
--                                                                    --
-- The language has no recursion, so termination is syntactic.        --
-- Reducibility is still needed, since substitution can grow a term.  --
--                                                                    --
-- The `handle` case is an induction on the scrutinee's `Comp`        --
-- derivation: each `HANDLE-OP` consumes one resumption premise.      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
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

open import OperationalSemantics.Adequacy.Environment    Spec
open import OperationalSemantics.Adequacy.Evaluation     Spec
open import OperationalSemantics.Adequacy.Reducibility   Spec
open import OperationalSemantics.Adequacy.RenEquivalence Spec
open import OperationalSemantics.Adequacy.Slice          Spec
open import OperationalSemantics.Adequacy.SubEquivalence Spec

------------------------------------------------------------------------
-- THE FUNDAMENTAL LEMMA
--
-- Induction on the typing derivation, mutually for values and computations.
-- Six computation cases are still open; each is stated as its own lemma taking
-- the induction hypotheses it needs — for a binding subterm, at *every*
-- environment, since the state the subterm is reached at is not the one the
-- case starts from.
------------------------------------------------------------------------

postulate

  -- Handling: as sequencing (`handle-steps`), with `HANDLE-OP` firing a clause.
  -- This is the case that inducts on the scrutinee's `Comp` derivation.

  FL-handle : ∀ {St Γ A B ε₁ ε₂} → (γ : Env St Γ) → Rel-Env γ
            → (M : Γ ⊢C⦂ A ‼ ε₁)
            → (H : (op : Op) → (ε₃ : E) → (Γ' : Ctx) → Cl B op ε₃ Γ' (Γ ᴱ))
            → (N : Γ ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
            → Comp' A ε₁ St (env-C γ M)
            → (∀ {St'} {op : Op} {ε₃ : E} {Γ' : Ctx}
                 → (γ' : Env St' (Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                    ∷ [ mapᵉ (op-grade op) ]
                                        (type-of-gtype (arity op) ⇒ B ‼ ε₃)))
                 → Rel-Env γ'
                 → Comp' B (op-grade op ·ₑ ε₃) St' (env-C γ' (H op ε₃ Γ')))
            → (∀ {St'} → (γ' : Env St' (Γ ⟨ mapᵉ ε₁ ⟩ ∷ A)) → Rel-Env γ'
                 → Comp' B ε₂ St' (env-C γ' N))
            --------------------------------------------------------------
            → Comp' B (ε₁ ·ₑ ε₂) St (env-C γ (handle M `with H `in N))

  -- Matching: the scrutinee is a pair, and the reduct substitutes its two
  -- components. Needs the two nested substitutions to be seen in the order the
  -- environment applies them.

  FL-match : ∀ {St Γ A B D ε} → (γ : Env St Γ) → Rel-Env γ
           → (V : Γ ⊢V⦂ A |×| B) → (M : Γ ∷ A ∷ B ⊢C⦂ D ‼ ε)
           → Val (A |×| B) St (env-V γ V)
           → (∀ {St'} → (γ' : Env St' (Γ ∷ A ∷ B)) → Rel-Env γ'
                → Comp' D ε St' (env-C γ' M))
           --------------------------------------------------------------
           → Comp' D ε St (env-C γ (match V `in M))

  -- Boxing: allocate, which is where the store grows (`store-fresh`). The
  -- boxed value is asked for at every state its lock permits, which is why the
  -- hypothesis quantifies over the environment.

  FL-box : ∀ {St Γ A D ρ ε} → (γ : Env St Γ) → Rel-Env γ
         → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A) → (M : Γ ∷ [ ρ ] A ⊢C⦂ D ‼ ε)
         → (∀ {St'} → (γ' : Env St' (Γ ⟨ ρ ⟩)) → Rel-Env γ'
              → Val A St' (env-V γ' V))
         → (∀ {St'} → (γ' : Env St' (Γ ∷ [ ρ ] A)) → Rel-Env γ'
              → Comp' D ε St' (env-C γ' M))
         --------------------------------------------------------------
         → Comp' D ε St (env-C γ (box V M))

  -- Unboxing: read the store. The value read is reducible because the cell the
  -- action's `unbox` names is the one the environment sends the boxed
  -- variable to.

  FL-unbox : ∀ {St Γ Δ₀ A D ρ ε} → (γ : Env St Γ) → Rel-Env γ
           → (w : Ren (Δ₀ ⟨ ρ ⟩) Γ) → (V : Δ₀ ⊢V⦂ [ ρ ] A)
           → (M : Γ ∷ A ⊢C⦂ D ‼ ε)
           → (∀ {St'} → (γ' : Env St' (Γ ∷ A)) → Rel-Env γ'
                → Comp' D ε St' (env-C γ' M))
           --------------------------------------------------------------
           → Comp' D ε St (env-C γ (unbox w V M))

-- Performing: already a weak head normal form, so this is `comp-op` at the empty
-- run. Its resumption premise is the induction hypothesis at the environment a
-- `resume` amounts to: the lock the operation is performed under, matched by the
-- resumption's own slice extended by the lock it lands beneath
-- (`unbox-ren-resume-≐`), and the arity value on top.

FL-perform : ∀ {St Γ A ε} {op : Op} → (γ : Env St Γ) → Rel-Env γ
           → (V : Γ ⊢V⦂ type-of-gtype (param op))
           → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                    ⊢C⦂ A ‼ ε)
           → Val (type-of-gtype (param op)) St (env-V γ V)
           → (∀ {St'} → (γ' : Env St' (Γ ⟨ mapᵉ (op-grade op) ⟩
                                         ∷ type-of-gtype (arity op)))
                → Rel-Env γ' → Comp' A ε St' (env-C γ' M))
           --------------------------------------------------------------
           → Comp' A (op-grade op ·ₑ ε) St (env-C γ (perform op V M))

FL-perform {St = St} {Γ = Γ} {op = op} γ pγ V M pV pM =
  subst (Comp' _ _ _) (sym (env-Cˢ-perform γ [] V M))
    (comp-op ε* (Val→Valᵍ (param op) (env-V γ V) pV)
      (λ q W' pW' →
         Comp-≐ᶜ (resumeq q W')
           (pM ((γ ⟨ slice-∘ delay-slice q ⟩ᵉ) ∷ᵉ W')
               (pγ , Valᵍ→Val (arity op) W' pW'))))
  where
    ρ  = mapᵉ (op-grade op)
    Ar = type-of-gtype (arity op)
    M₀ = env-Cˢ γ ([] ⟨ ρ ⟩ ∷ Ar) M

    -- the action at the resumption's environment *is* the resumption, once the
    -- two `++ᶜ`-associativity casts are seen to be the identity and the two
    -- renamings to act alike
    resumeq : ∀ {St₂ : 𝕊 []} → (q : Slice St ρ St₂ ρ)
            → (W' : toCtx (St₂ ⟨ ρ ⟩ₛ) ⊢V⦂ Ar)
            → env-C ((γ ⟨ slice-∘ delay-slice q ⟩ᵉ) ∷ᵉ W') M
            ≐ᶜ resume q M₀ W'
    resumeq q W' =
      subst (λ z → (z [ Hd ↦ W' ]c) ≐ᶜ resume q M₀ W')
        (sym (cong (C-rename (cong-∷-ren (unbox-ren (slice-∘ delay-slice q))))
               (trans (castᶜ-irr (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩)
                                                 ([] ∷ Ar))) refl _)
                      (cong (env-Cˢ γ ([] ⟨ ρ ⟩ ∷ Ar))
                            (castᶜ-irr (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) ([] ∷ Ar))
                                       refl M)))))
        (sub-≐ᶜ Hd (≐ᵛ-refl W')
          (C-rename-≐ (cong-∷-ren-≐ (unbox-ren-resume-≐ q)) M₀))

mutual

  -- The value half. Nothing is asked at a base, unit or empty type; a pair is
  -- the pair of the actions; a variable is `env-var`.
  --
  -- At a lambda the environment moves to the state the Kripke clause offers and
  -- gains the argument (`sliceᵉ`, `_∷ᵉ_`) — and that is the whole reason the
  -- slice is *recorded* in the environment: the clause supplies no store for
  -- the later state, and a recorded slice needs none. The reduct the clause asks
  -- for is the action's body up to `_≐ᶜ_`, whence `Comp-≐ᶜ`.

  FL-V : ∀ {St Γ A} → (γ : Env St Γ) → Rel-Env γ
       → (V : Γ ⊢V⦂ A)
       -------------------------------
       → Val A St (env-V γ V)

  FL-V γ pγ (var f x)  = env-var γ pγ x f
  FL-V γ pγ (const c)  = tt
  FL-V γ pγ ⋆          = tt
  FL-V γ pγ ⦉ V , W ⦊   =
    _ , _ , env-Vˢ-pair γ [] V W , FL-V γ pγ V , FL-V γ pγ W

  FL-V {A = A ⇒ (B ‼ ε)} γ pγ (lam M) =
      _ , env-Vˢ-lam γ [] M
    , λ q M₂ eM₂ W pW →
        Comp-≐ᶜ (sub-≐ᶜ Hd (≐ᵛ-refl W) (≐ᶜ-sym eM₂))
                (FL-C (sliceᵉ γ q ∷ᵉ W) (pγ , pW) M)

  -- The computation half. `return` is a weak head normal form; `coerce`,
  -- application and `delay` are head expansion off their own rule; `absurd` is
  -- vacuous, since no value of the empty type lives over a state context.
  --
  -- Application instantiates the function's Kripke clause at the state it
  -- already stands in, and `delay` at the slice the lock it passes gives. In
  -- both, the renaming the clause inserts is identity-like, so the reduct is
  -- the action itself up to `_≐ᶜ_`.

  FL-C : ∀ {St Γ A ε} → (γ : Env St Γ) → Rel-Env γ
       → (M : Γ ⊢C⦂ A ‼ ε)
       -------------------------------
       → Comp' A ε St (env-C γ M)

  FL-C γ pγ (return V) =
    subst (Comp' _ _ _) (sym (env-Cˢ-ret γ [] V)) (comp-ret ε* (FL-V γ pγ V))

  FL-C γ pγ (coerce p M) =
    subst (Comp' _ _ _) (sym (env-Cˢ-coerce γ [] M))
      (Comp-expand COERCE (FL-C γ pγ M))

  FL-C γ pγ (absurd V) = ⊥-elim (empty-canonical (env-V γ V))

  FL-C γ pγ (V · W) with FL-V γ pγ V
  ... | M₀ , eq , f =
    subst (Comp' _ _ _) (sym (env-Cˢ-app γ [] V W))
      (subst (λ z → Comp' _ _ _ (z · env-V γ W)) (sym eq)
        (Comp-expand APP
          (Comp-≐ᶜ
            (sub-≐ᶜ Hd (≐ᵛ-refl (env-V γ W))
              (C-rename-id-≐ (cong-∷-ren-id-≐ slice-renᵘ-id-≐) M₀))
            (f slice-id (slice-under slice-id M₀) (≐ᶜ-refl _)
               (env-V γ W) (FL-V γ pγ W)))))

  FL-C {St = St} γ pγ (delay τ M) =
    subst (Comp' _ _ _) (sym (env-Cˢ-delay γ [] M))
      (Comp-expand DELAY
        (Comp-≐ᶜ
          (C-rename-id-≐ unbox-ren-delay-≐ (env-Cˢ γ ([] ⟨ of-natʳ τ ⟩) M))
          (subst (Comp' _ _ _) eqδ (FL-C (γ ⟨ delay-slice ⟩ᵉ) pγ M))))
    where
      eqδ = cong (C-rename (unbox-ren (delay-slice {of-natʳ τ} {St})))
              (trans
                (castᶜ-irr (sym (++ᶜ-assoc (toCtx St) ([] ⟨ of-natʳ τ ⟩) []))
                           refl _)
                (cong (env-Cˢ γ ([] ⟨ of-natʳ τ ⟩))
                      (castᶜ-irr (++ᶜ-assoc _ ([] ⟨ of-natʳ τ ⟩) []) refl M)))

  -- Sequencing: `env-Cˢ-seq` splits the action, `seq-Comp` runs the scrutinee and
  -- then the sequel. The environment the sequel needs is `(γ ⟨ q ⟩ᵉ) ∷ᵉ V` — and
  -- `env-Cˢ (γ ⟨ q ⟩ᵉ) ([] ∷ A)` *is* `C-rename (cong-∷-ren (unbox-ren q))` of the
  -- action at suffix `[] ⟨ mapᵉ ε₁ ⟩ ∷ A`, definitionally (both of `env-Cˢ`'s
  -- casts are `refl` at the empty suffix), so only `env-Cˢ-head` is needed.

  FL-C {St = St} {ε = ε} γ pγ (_⨟_ {A = A} {ε = ε₁} M N) =
    subst (Comp' _ _ St) (sym (env-Cˢ-seq γ [] M N))
      (seq-Comp (env-Cˢ γ ([] ⟨ mapᵉ ε₁ ⟩ ∷ A) N) (FL-C γ pγ M)
        (λ q V pV →
           subst (Comp' _ _ _) (sym (env-Cˢ-head (γ ⟨ q ⟩ᵉ) N V))
                 (FL-C ((γ ⟨ q ⟩ᵉ) ∷ᵉ V) (pγ , pV) N)))

  FL-C γ pγ (handle M `with H `in N) =
    FL-handle γ pγ M H N (FL-C γ pγ M)
      (λ γ' pγ' → FL-C γ' pγ' (H _ _ _)) (λ γ' pγ' → FL-C γ' pγ' N)

  FL-C γ pγ (match V `in M) =
    FL-match γ pγ V M (FL-V γ pγ V) (λ γ' pγ' → FL-C γ' pγ' M)

  FL-C γ pγ (perform op V M) =
    FL-perform γ pγ V M (FL-V γ pγ V) (λ γ' pγ' → FL-C γ' pγ' M)

  FL-C γ pγ (box V M) =
    FL-box γ pγ V M (λ γ' pγ' → FL-V γ' pγ' V) (λ γ' pγ' → FL-C γ' pγ' M)

  FL-C γ pγ (unbox w V M) =
    FL-unbox γ pγ w V M (λ γ' pγ' → FL-C γ' pγ' M)

------------------------------------------------------------------------
-- COROLLARIES
------------------------------------------------------------------------

-- A reducible computation halts: its run *is* the evaluation, and which of the
-- two shapes it halts in is which `Comp` constructor it is. The reducibility
-- of the components plays no part — normalization is all that is read off.

Comp-halts : ∀ {A P ε} {St : 𝕊 []} → {M : toCtx St ⊢C⦂ A ‼ ε}
           → Comp A P ε St M
           -------------------
           → Halts (⟨ St , M ⟩)

Comp-halts (comp-ret rs _)  = halts-ret (ret-whnf _ _ rs)
Comp-halts (comp-op rs _ _) = halts-op (op-whnf _ _ _ _ _ rs)

-- A closed program is reducible at the empty state: `Γ = []`, `St = ∅`, and
-- `toCtx ∅` has no variables to make reducible (`store-∅`).

normalize : ∀ {A ε} → (M : Prog A ε) → Comp' A ε ∅ M
normalize M = subst (Comp' _ _ ∅) (env-C-id M) (FL-C ⌊ ∅ ⌋ store-∅ M)

-- Hence every closed program reaches a weak head normal form: it returns a
-- value, or it gets stuck on an unhandled operation.

halts : ∀ {A ε} → (M : Prog A ε) → Halts (⟨ ∅ , M ⟩)
halts M = Comp-halts (normalize M)
