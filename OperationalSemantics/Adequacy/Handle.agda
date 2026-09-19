------------------------------------------------------------------------
-- Handling preserves reducibility.                                   --
--                                                                    --
-- As `Bind`, plus a clause premise, and above `Environment` for the   --
-- same reason (`sub-wk-C`).                                           --
--                                                                    --
-- Both premises are stated at exactly the reduct the machine          --
-- produces. `HANDLE-OP` boxes the resumption at the operation's own   --
-- grade and `BOX` then allocates it, so the clause fires at           --
-- `St₁ ∷ₛ V₀` with its continuation binder *being* the fresh cell.    --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (yes; no; ¬_; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Handle (Spec : LanguageSpec) where

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

------------------------------------------------------------------------
-- THE TWO PREMISES
--
-- The clause premise: at the state the operation is handled at, with the
-- resumption already boxed and allocated. `V₀` is the boxed resumption in the
-- shape `_∷ₛ_` stores it, and the hypothesis about it is exactly
-- `SRed-fresh`'s — reducible at every state the lock permits.
------------------------------------------------------------------------

Boxed : (B : VType) → (op : Op) → (ε₃ : E) → 𝕊 [] → Set
Boxed B op ε₃ St₁ =
  ([] ++ᶜ toCtx St₁ ⟨ mapᵉ (op-grade op) ⟩)
  ⊢V⦂ (type-of-gtype (arity op) ⇒ B ‼ ε₃)

Boxed-VRed : (B : VType) → (op : Op) → (ε₃ : E)
           → (St₁ : 𝕊 []) → Boxed B op ε₃ St₁ → Set
Boxed-VRed B op ε₃ St₁ V₀ =
  ∀ {St'} → (q : St₁ ⊑ₛ[ mapᵉ (op-grade op) ] St')
    → VRed (type-of-gtype (arity op) ⇒ B ‼ ε₃) St'
           (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V₀)

-- The clause, crossed into the context it fires at and given the operation's
-- parameter. Its continuation binder is the cell `BOX` just allocated, so this
-- lives over `toCtx (St₁ ∷ₛ V₀)` and nothing further is substituted. Crossing
-- the barrier is `unbox-ren` at the `⊤ᵣ`-reach the run to `St₁` licenses.

Fired : ∀ {B} → (St : 𝕊 []) → (op : Op) → (ε₃ : E) → Fam B (toCtx St ⟨ ⊤ᵣ ⟩)
      → {St₁ : 𝕊 []} → (q : St ⊑ₛ[ ⊤ᵣ ] St₁) → (V₀ : Boxed B op ε₃ St₁)
      → toCtx St₁ ⊢V⦂ type-of-gtype (param op)
      → toCtx (St₁ ∷ₛ V₀) ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)
Fired St op ε₃ H q V₀ W =
  (C-rename (cong-∷-ren (cong-∷-ren (unbox-ren q))) (H op ε₃))
    [ split-∷ split-[] ↦ W ]c

Clause-Prem : (B : VType) → (St : 𝕊 []) → Fam B (toCtx St ⟨ ⊤ᵣ ⟩) → Set
Clause-Prem B St H =
  ∀ {St₁ : 𝕊 []} {op : Op} {ε₃ : E}
    → (q : St ⊑ₛ[ ⊤ᵣ ] St₁)
    → (V₀ : Boxed B op ε₃ St₁) → Boxed-VRed B op ε₃ St₁ V₀
    → (W : toCtx St₁ ⊢V⦂ type-of-gtype (param op))
    → VRed (type-of-gtype (param op)) St₁ W
    → CRed' B (op-grade op ·ₑ ε₃) (St₁ ∷ₛ V₀) (Fired St op ε₃ H q V₀ W)

-- Two clause binders' worth of congruence, composed.

cong-cl-ren-∘-≐ʳ : ∀ {Γ₁ Γ₂ Γ₃ A A₀}
                 → (r : Ren [] Γ₂ Γ₁) → (r' : Ren [] Γ₃ Γ₂)
                 → (cong-∷-ren {A = A₀} (cong-∷-ren {A = A} r)
                      ∘ʳ cong-∷-ren (cong-∷-ren r'))
                 ≐ʳ cong-∷-ren (cong-∷-ren (r ∘ʳ r'))
cong-cl-ren-∘-≐ʳ r r' =
  ≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ʳ (cong-∷-ren r) (cong-∷-ren r')))
           (cong-∷-ren-≐ʳ (≐ʳ-sym (cong-∷-ren-∘-≐ʳ r r')))

-- The sequel premise, as in `Bind`.

Seq-Prem : ∀ {A B ε₁ ε₂} {St : 𝕊 []}
         → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂) → Set
Seq-Prem {A} {B} {ε₁} {ε₂} {St} N =
  ∀ {St₁ : 𝕊 []} → (q : St ⊑ₛ[ mapᵉ ε₁ ] St₁)
    → (V : toCtx St₁ ⊢V⦂ A) → VRed A St₁ V
    → CRed' B ε₂ St₁ ((C-rename (cong-∷-ren (unbox-ren q)) N) [ split-[] ↦ V ]c)

------------------------------------------------------------------------
-- HANDLING
--
-- Induction on the scrutinee's `CRed` derivation. `cred-ret` fires `HANDLE-RET`
-- and is `Bind`'s `cred-ret` verbatim — the sequel premise consumes the value
-- and the run's `mapᵉ uₑ` is reconciled with the reach's `uᵣ` by
-- `suc-comp-ren-grade`.
------------------------------------------------------------------------

handle-CRed : ∀ {A B ε₁ ε₂} {St : 𝕊 []}
            → {M : toCtx St ⊢C⦂ A ‼ ε₁}
            → (H : Fam B (toCtx St ⟨ ⊤ᵣ ⟩))
            → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
            → CRed' A ε₁ St M
            → Clause-Prem B St H
            → Seq-Prem N
            ------------------------------------------------------------
            → CRed' B (ε₁ ·ₑ ε₂) St (handle M `with H `in N)

-- The scrutinee returns: `HANDLE-RET`, and the clauses are discarded.

handle-CRed {A} {B} {ε₁} {ε₂} {St} H N
            (cred-ret {St₁ = St₁} {V = V} rs pV) hH hN
  with handle-steps rs H N

... | H₁ , N₁ , rs' , eH₁ , eN₁ =
  CRed-expand* rs'
    (CRed-expand HANDLE-RET
      (CRed-≡ᶜ (sub-≡ᶜ split-[] (refl) shift) (hN q V pV)))
  where
    E₀  = steps-extends-state rs
    srs = suc-comp-ren E₀ (steps-grade-≾ rs)

    b : ≤ₛ-grade E₀ ≾ᵣ mapᵉ ε₁
    b = ≾ᵣ-trans
          (≾ᵣ-reflexive
            (trans (sym (·ᵣ-identityʳ (≤ₛ-grade E₀)))
                   (cong (≤ₛ-grade E₀ ·ᵣ_) (sym map-uᵉ))))
          (steps-grade-≾ rs)

    q = reach E₀ b

    R₁ : Ren [] (toCtx St₁) (toCtx St₁ ⟨ mapᵉ uₑ ⟩)
    R₁ = eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren

    eqr : (srs ∘ʳ R₁) ≐ʳ unbox-ren q
    eqr = ≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ʳ srs (eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ))
                                       ⟨⟩-η-ren))
                   (∘ʳ-≐ʳ (suc-comp-ren-grade E₀ map-uᵉ (steps-grade-≾ rs)
                                             (reach-bound q))
                         ≐ʳ-refl)

    shift : C-rename (cong-∷-ren (unbox-ren q)) N
          ≡ C-rename (cong-∷-ren R₁) N₁
    shift =
      sym
        (trans (C-rename-cong (cong-∷-ren R₁) eN₁)
          (trans (sym (C-rename-∘ (cong-∷-ren srs) (cong-∷-ren R₁) N))
            (C-rename-≡ (≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ʳ srs R₁))
                                  (cong-∷-ren-≐ʳ eqr)) N)))


-- The scrutinee gets stuck on an operation. The reduct chain is
--
--   handle-steps rs H N   -- run to the `perform`
--   HANDLE-OP             -- box the resumption
--   BOX                   -- allocate it
--
-- landing at `⟨ St₁ ∷ₛ V₀ , Fired … ⟩`. `Fired` is `HANDLE-OP`'s clause instance
-- once `handle-steps`'s renaming of the clauses is composed with the barrier
-- crossing (`barrier-unbox-≐ʳ`), and the effects need no `ε-subst`: `_↝_`
-- relates configurations at different effects, and `box`'s body carries
-- `op-grade op ·ₑ (ε₃ ·ₑ ε₂)` where the redex carries `(op-grade op ·ₑ ε₃) ·ₑ ε₂`.

handle-CRed {A} {B} {ε₁} {ε₂} {St} H N
            (cred-op {ε₁ = ε₃} {St₁ = St₁} {op = op} {W = W} {M' = M'} rs pW pk)
            hH hN
  with handle-steps rs H N

... | H₁ , N₁ , rs' , eH₁ , eN₁ =
  CRed-expand* rs'
    (CRed-expand HANDLE-OP
      (CRed-expand BOX
        (subst (CRed' B _ (St₁ ∷ₛ V₀)) fired
          (hH q₀ V₀ bv W (VRedᵍ→VRed (param op) W pW)))))
  where
    ρₒ  = mapᵉ (op-grade op)
    Ar  = type-of-gtype (arity op)
    E₀  = steps-extends-state rs

    b₀  = steps-grade-≾ rs
    srs = suc-comp-ren E₀ b₀

    -- the barrier reach the run licenses: `⊤ᵣ` is greatest, so no bound is
    -- accumulated along the way
    q₀ : St ⊑ₛ[ ⊤ᵣ ] St₁
    q₀ = reach E₀ (≾-⊤ᵣ _)

    emap : toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩
         ≡ toCtx St₁ ⟨ ρₒ ·ᵣ mapᵉ ε₃ ⟩
    emap = cong (toCtx St₁ ⟨_⟩) map-·ᵉ

    κ : Ren [] ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ⟨ mapᵉ ε₃ ⟩)
              (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
    κ = (eq-ren emap ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    -- the clauses and sequel `HANDLE-OP` puts under the boxed resumption
    H₁' : Fam B ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ⟨ ⊤ᵣ ⟩)
    H₁' op' ε' =
      C-rename (cong-∷-ren (cong-∷-ren (barrier-wk-ren ρₒ Ar))) (H₁ op' ε')

    N₁' = C-rename (cong-∷-ren κ) N₁

    Body = handle M' `with H₁' `in N₁'

    V₀ : Boxed B op (ε₃ ·ₑ ε₂) St₁
    V₀ = V-rename (eq-ren (sym ++ᶜ-identityˡ)) (lam Body)

    fired : Fired St op (ε₃ ·ₑ ε₂) H q₀ V₀ W
          ≡ (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
               (H₁ op (ε₃ ·ₑ ε₂))) [ split-∷ split-[] ↦ W ]c
    fired = sub-≡ᶜ (split-∷ split-[]) (refl) (sym cross)
      where
        cross : C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                  (H₁ op (ε₃ ·ₑ ε₂))
              ≡ C-rename (cong-∷-ren (cong-∷-ren (unbox-ren q₀)))
                  (H op (ε₃ ·ₑ ε₂))
        cross =
          trans
            (C-rename-cong (cong-∷-ren (cong-∷-ren barrier-ren))
                           (eH₁ op (ε₃ ·ₑ ε₂)))
            (trans
              (sym (C-rename-∘
                      (cong-∷-ren (cong-∷-ren (steps-barrier-ren rs)))
                      (cong-∷-ren (cong-∷-ren barrier-ren))
                      (H op (ε₃ ·ₑ ε₂))))
              (C-rename-≡
                (≐ʳ-trans
                  (≐ʳ-sym (cong-∷-ren-∘-≐ʳ
                             (cong-∷-ren (steps-barrier-ren rs))
                             (cong-∷-ren barrier-ren)))
                  (cong-∷-ren-≐ʳ
                    (≐ʳ-trans
                      (≐ʳ-sym (cong-∷-ren-∘-≐ʳ (steps-barrier-ren rs)
                                              barrier-ren))
                      (cong-∷-ren-≐ʳ (barrier-unbox-≐ʳ q₀ (≾-⊤ᵣ _))))))
                (H op (ε₃ ·ₑ ε₂))))

    -- The boxed resumption *is* a lambda, so `VRed`'s arrow clause is met by its
    -- own body; the two `eq-ren`s cancel and `reach-unbox-ren-≐ʳ` composes the
    -- unboxing with the clause's own reach.

    bv : Boxed-VRed B op (ε₃ ·ₑ ε₂) St₁ V₀
    bv {St'} q = _ , refl , resump
      where
        Mq = C-rename (cong-∷-ren (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q))
               (C-rename (cong-∷-ren (eq-ren (sym (++ᶜ-identityˡ
                                                    {toCtx St₁ ⟨ ρₒ ⟩})))) Body)

        resump : ∀ {St'' : 𝕊 []} → (q' : St' ⊑ₛ[ uᵣ ] St'')
               → (M₂ : toCtx St'' ∷ Ar ⊢C⦂ B ‼ (ε₃ ·ₑ ε₂))
               → M₂ ≡ reach-under q' Mq
               → (W' : toCtx St'' ⊢V⦂ Ar) → VRed Ar St'' W'
               → CRed' B (ε₃ ·ₑ ε₂) St'' (M₂ [ split-[] ↦ W' ]c)

        resump {St''} q' M₂ eM₂ W' pW' =
          CRed-≡ᶜ (sym (sub-≡ᶜ split-[] (refl) collapse)) inner
          where
            q₂ = reach-∘ q' q

            R₂ = eq-ren (sym (++ᶜ-identityˡ {toCtx St₁ ⟨ ρₒ ⟩}))
                   ∘ʳ (eq-ren (++ᶜ-identityˡ {toCtx St₁ ⟨ ρₒ ⟩}) ∘ʳ unbox-ren q)

            -- the three renamings the clause stacks up compose to `unbox-ren q₂`
            ren-eq : (R₂ ∘ʳ reach-renᵘ q') ≐ʳ unbox-ren q₂
            ren-eq =
              ≐ʳ-trans
                (∘ʳ-≐ʳ
                  (≐ʳ-trans
                    (≐ʳ-sym (∘ʳ-assoc-≐ʳ (eq-ren (sym ++ᶜ-identityˡ))
                                        (eq-ren ++ᶜ-identityˡ) (unbox-ren q)))
                    (∘ʳ-idˡ-≐ʳ (unbox-ren q)
                      (≐ʳ-trans
                        (eq-ren-∘-≐ʳ (sym (++ᶜ-identityˡ {toCtx St₁ ⟨ ρₒ ⟩}))
                                    ++ᶜ-identityˡ)
                        (eq-ren-≐ʳ _ refl))))
                  ≐ʳ-refl)
                (reach-unbox-ren-≐ʳ q' q)

            collapse : M₂ ≡ C-rename (cong-∷-ren (unbox-ren q₂)) Body
            collapse =
              trans eM₂
                (trans
                  (C-rename-cong (cong-∷-ren (reach-renᵘ q'))
                    (trans
                      (sym (C-rename-∘
                                 (cong-∷-ren (eq-ren (sym ++ᶜ-identityˡ)))
                                 (cong-∷-ren (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q))
                                 Body))
                      (C-rename-≡
                        (≐ʳ-sym (cong-∷-ren-∘-≐ʳ
                                   (eq-ren (sym ++ᶜ-identityˡ))
                                   (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q)))
                        Body)))
                  (trans
                    (sym
                      (C-rename-∘ (cong-∷-ren R₂)
                                  (cong-∷-ren (reach-renᵘ q')) Body))
                    (C-rename-≡
                      (≐ʳ-trans
                        (≐ʳ-sym (cong-∷-ren-∘-≐ʳ R₂ (reach-renᵘ q')))
                        (cong-∷-ren-≐ʳ ren-eq))
                      Body)))

            -- The reduct *is* the recursive call: renaming and `_[_↦_]c` both
            -- distribute over `handle` definitionally, and the scrutinee reached
            -- is `resume q₂ M' W'`.
            inner : CRed' B (ε₃ ·ₑ ε₂) St''
                      ((C-rename (cong-∷-ren (unbox-ren q₂)) Body)
                         [ split-[] ↦ W' ]c)
            inner =
              handle-CRed _ _ (pk q₂ W' (VRed→VRedᵍ (arity op) W' pW')) hH₂ hN₂
              where
                sq = unbox-ren q₂

                B₁' : ≤ₛ-grade (ext q₂) ·ᵣ mapᵉ ε₃ ≾ᵣ ρₒ ·ᵣ mapᵉ ε₃
                B₁' = ·ᵣ-monoˡ-≾ᵣ (bound q₂)

                B₁ : ≤ₛ-grade (ext q₂) ·ᵣ mapᵉ ε₃
                   ≾ᵣ mapᵉ (op-grade op ·ₑ ε₃)
                B₁ = ≾ᵣ-trans B₁' (≾ᵣ-reflexive (sym map-·ᵉ))

                -- what is left of the sequel's renaming once the arity variable
                -- is gone
                W₁ : Ren [] (toCtx St'' ⟨ mapᵉ ε₃ ⟩)
                          (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
                W₁ = (eq-ren emap ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren sq

                eW₁ : W₁ ≐ʳ suc-comp-ren (ext q₂) B₁
                eW₁ =
                  ≐ʳ-trans
                    (∘ʳ-assoc-≐ʳ (eq-ren emap) ⟨⟩-μ-ren (cong-⟨⟩-ren sq))
                    (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (unbox-ren-μ-≐ʳ q₂ B₁'))
                              (suc-comp-ren-grade-src (ext q₂) map-·ᵉ B₁' B₁))

                -- the sequel the recursion needs is the original one, renamed:
                -- `HANDLE-OP` weakens it past the arity variable and `resume`
                -- substitutes for exactly that variable, so the two cancel
                eN₂ : (C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₁')
                        [ split-∷ (split-⟨⟩ split-[]) ↦ W' ]c
                    ≡ C-rename (cong-∷-ren (srs ∘ʳ W₁)) N
                eN₂ =
                  trans (sub-≡ᶜ (split-∷ (split-⟨⟩ split-[])) (refl) split-off)
                    (trans (sub-wk-C ([] ⟨ mapᵉ ε₃ ⟩ ∷ A)
                                        (C-rename (cong-∷-ren W₁) N₁) W')
                      (trans (C-rename-cong (cong-∷-ren W₁) eN₁)
                        (trans
                          (sym (C-rename-∘ (cong-∷-ren srs)
                                              (cong-∷-ren W₁) N))
                          (C-rename-≡ (≐ʳ-sym (cong-∷-ren-∘-≐ʳ srs W₁)) N))))
                  where
                    innerᵣ : (κ ∘ʳ cong-⟨⟩-ren (cong-∷-ren sq))
                           ≐ʳ (W₁ ∘ʳ cong-⟨⟩-ren wk-ren)
                    innerᵣ =
                      ≐ʳ-trans
                        (∘ʳ-assoc-≐ʳ (eq-ren emap ∘ʳ ⟨⟩-μ-ren)
                                    (cong-⟨⟩-ren wk-ren)
                                    (cong-⟨⟩-ren (cong-∷-ren sq)))
                        (≐ʳ-trans
                          (∘ʳ-≐ʳ ≐ʳ-refl
                            (≐ʳ-trans
                              (≐ʳ-sym (cong-⟨⟩-ren-∘-≐ʳ wk-ren (cong-∷-ren sq)))
                              (≐ʳ-trans (cong-⟨⟩-ren-≐ʳ (wk-ren-nat-≐ʳ sq))
                                        (cong-⟨⟩-ren-∘-≐ʳ sq wk-ren))))
                          (≐ʳ-sym (∘ʳ-assoc-≐ʳ (eq-ren emap ∘ʳ ⟨⟩-μ-ren)
                                              (cong-⟨⟩-ren sq)
                                              (cong-⟨⟩-ren wk-ren))))

                    split-off : C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq)))
                                         N₁'
                              ≡ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren))
                                   (C-rename (cong-∷-ren W₁) N₁)
                    split-off =
                      trans
                        (sym (C-rename-∘
                                   (cong-∷-ren κ)
                                   (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq)))
                                   N₁))
                        (trans
                          (C-rename-≡
                            (≐ʳ-trans
                              (≐ʳ-sym (cong-∷-ren-∘-≐ʳ
                                         κ (cong-⟨⟩-ren (cong-∷-ren sq))))
                              (≐ʳ-trans (cong-∷-ren-≐ʳ innerᵣ)
                                        (cong-∷-ren-∘-≐ʳ W₁ (cong-⟨⟩-ren wk-ren))))
                            N₁)
                          (C-rename-∘ (cong-∷-ren W₁)
                                      (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N₁))

                hN₂ : Seq-Prem ((C-rename
                                   (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₁')
                                  [ split-∷ (split-⟨⟩ split-[]) ↦ W' ]c)
                hN₂ {St₃} q₃ V pV =
                  CRed-≡ᶜ (sub-≡ᶜ split-[] (refl) shift) (hN q₄ V pV)
                  where
                    -- the run and the clause's own reach accumulate: the grades
                    -- multiply and each is bounded, so the composite stays
                    -- under `ε₁`
                    B₂ : ≤ₛ-grade (≤ₛ-trans E₀ (ext q₂)) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁
                    B₂ =
                      ≾ᵣ-trans
                        (≾ᵣ-reflexive
                          (trans (cong (_·ᵣ mapᵉ ε₃)
                                       (≤ₛ-grade-trans E₀ (ext q₂)))
                                 (·ᵣ-assoc (≤ₛ-grade E₀) (≤ₛ-grade (ext q₂))
                                           (mapᵉ ε₃))))
                        (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ B₁) b₀)

                    q₄ : St ⊑ₛ[ mapᵉ ε₁ ] St₃
                    q₄ = reach (≤ₛ-trans (≤ₛ-trans E₀ (ext q₂)) (ext q₃))
                           (≾ᵣ-trans
                             (≾ᵣ-reflexive
                               (≤ₛ-grade-trans (≤ₛ-trans E₀ (ext q₂)) (ext q₃)))
                             (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (bound q₃)) B₂))

                    composite : suc-comp-ren (ext q₄) (reach-bound q₄)
                              ≐ʳ ((srs ∘ʳ W₁)
                                    ∘ʳ suc-comp-ren (ext q₃) (reach-bound q₃))
                    composite =
                      ≐ʳ-trans
                        (suc-comp-ren-∘-≐ʳ (≤ₛ-trans E₀ (ext q₂)) (ext q₃)
                                          (reach-bound q₄) B₂ (reach-bound q₃))
                        (∘ʳ-≐ʳ
                          (≐ʳ-trans
                            (suc-comp-ren-∘-≐ʳ E₀ (ext q₂) B₂ b₀ B₁)
                            (∘ʳ-≐ʳ ≐ʳ-refl (≐ʳ-sym eW₁)))
                          ≐ʳ-refl)

                    finalEq : unbox-ren q₄ ≐ʳ ((srs ∘ʳ W₁) ∘ʳ unbox-ren q₃)
                    finalEq =
                      ≐ʳ-trans (∘ʳ-≐ʳ composite (≐ʳ-refl {r = ⟨⟩-η-ren}))
                        (∘ʳ-assoc-≐ʳ (srs ∘ʳ W₁)
                                    (suc-comp-ren (ext q₃) (reach-bound q₃))
                                    ⟨⟩-η-ren)

                    shift : C-rename (cong-∷-ren (unbox-ren q₄)) N
                          ≡ C-rename (cong-∷-ren (unbox-ren q₃))
                               ((C-rename
                                   (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₁')
                                  [ split-∷ (split-⟨⟩ split-[]) ↦ W' ]c)
                    shift =
                      trans
                        (C-rename-≡
                          (≐ʳ-trans (cong-∷-ren-≐ʳ finalEq)
                                    (cong-∷-ren-∘-≐ʳ (srs ∘ʳ W₁)
                                                    (unbox-ren q₃))) N)
                        (trans
                          (C-rename-∘ (cong-∷-ren (srs ∘ʳ W₁))
                                      (cong-∷-ren (unbox-ren q₃)) N)
                          (C-rename-cong (cong-∷-ren (unbox-ren q₃))
                                         (sym eN₂)))

                -- The clause premise, rebuilt from `hH`. The clauses the
                -- recursion sees are `H` renamed by the run, weakened past the
                -- arity variable, crossed into `St''` and then substituted at
                -- that same variable — so the weakening and the substitution
                -- cancel (`sub-wk-C`) and what is left is one `suc-comp-ren`.
                hH₂ : Clause-Prem B St''
                        (((λ op' ε' →
                              C-rename (cong-∷-ren (cong-∷-ren
                                          (cong-⟨⟩-ren (cong-∷-ren sq))))
                                (H₁' op' ε'))
                          [ split-[] {toCtx St'' ∷ _} ↦ W' ]cl))
                hH₂ {St₃} {op₃} {ε₄} q₃ V₀' bv' W₃ pW₃ =
                  CRed-≡ᶜ (sub-≡ᶜ (split-∷ split-[]) (refl) step)
                          (hH q₄ V₀' bv' W₃ pW₃)
                  where
                    Eᶜ = ≤ₛ-trans E₀ (ext q₂)

                    q₄ : St ⊑ₛ[ ⊤ᵣ ] St₃
                    q₄ = reach (≤ₛ-trans Eᶜ (ext q₃)) (≾-⊤ᵣ _)

                    -- the barrier renaming the three stacked ones amount to
                    R₀ : Ren [] (toCtx St'' ⟨ ⊤ᵣ ⟩) (toCtx St ⟨ ⊤ᵣ ⟩)
                    R₀ = suc-comp-ren Eᶜ (≾-⊤ᵣ _)

                    Bᶜ : ≤ₛ-grade (ext q₂) ·ᵣ ⊤ᵣ ≾ᵣ ρₒ ·ᵣ ⊤ᵣ
                    Bᶜ = ·ᵣ-monoˡ-≾ᵣ (bound q₂)

                    stack : (steps-barrier-ren rs
                              ∘ʳ barrier-wk-ren ρₒ Ar
                              ∘ʳ cong-⟨⟩-ren (cong-∷-ren sq))
                          ≐ʳ (R₀ ∘ʳ cong-⟨⟩-ren (wk-ren {A = Ar}))
                    stack =
                      ≐ʳ-trans
                        (∘ʳ-≐ʳ ≐ʳ-refl
                          (≐ʳ-trans
                            (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren (≾-⊤ᵣ (ρₒ ·ᵣ ⊤ᵣ)))
                                        (⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren wk-ren)
                                        (cong-⟨⟩-ren (cong-∷-ren sq)))
                            (∘ʳ-≐ʳ ≐ʳ-refl
                              (≐ʳ-trans
                                (∘ʳ-assoc-≐ʳ ⟨⟩-μ-ren (cong-⟨⟩-ren wk-ren)
                                            (cong-⟨⟩-ren (cong-∷-ren sq)))
                                (≐ʳ-trans
                                  (∘ʳ-≐ʳ ≐ʳ-refl
                                    (≐ʳ-trans
                                      (≐ʳ-sym (cong-⟨⟩-ren-∘-≐ʳ
                                                 wk-ren (cong-∷-ren sq)))
                                      (≐ʳ-trans
                                        (cong-⟨⟩-ren-≐ʳ (wk-ren-nat-≐ʳ sq))
                                        (cong-⟨⟩-ren-∘-≐ʳ sq wk-ren))))
                                  (≐ʳ-sym (∘ʳ-assoc-≐ʳ ⟨⟩-μ-ren (cong-⟨⟩-ren sq)
                                                      (cong-⟨⟩-ren wk-ren))))))))
                        (≐ʳ-trans
                          (∘ʳ-≐ʳ ≐ʳ-refl
                            (≐ʳ-sym (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren (≾-⊤ᵣ (ρₒ ·ᵣ ⊤ᵣ)))
                                                (⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren sq)
                                                (cong-⟨⟩-ren wk-ren))))
                          (≐ʳ-trans
                            (≐ʳ-sym (∘ʳ-assoc-≐ʳ (steps-barrier-ren rs)
                                                (⟨⟩-≤-ren (≾-⊤ᵣ (ρₒ ·ᵣ ⊤ᵣ))
                                                  ∘ʳ (⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren sq))
                                                (cong-⟨⟩-ren wk-ren)))
                            (∘ʳ-≐ʳ
                              (≐ʳ-trans
                                (∘ʳ-≐ʳ ≐ʳ-refl
                                  (≐ʳ-trans
                                    (∘ʳ-≐ʳ ≐ʳ-refl (unbox-ren-μ-≐ʳ q₂ Bᶜ))
                                    (≐ʳ-sym (suc-comp-ren-≤ˡ (ext q₂)
                                              (≾-⊤ᵣ _) Bᶜ (≾-⊤ᵣ (ρₒ ·ᵣ ⊤ᵣ))))))
                                (≐ʳ-sym (suc-comp-ren-∘-≐ʳ E₀ (ext q₂)
                                          (≾-⊤ᵣ _) (≾-⊤ᵣ _) (≾-⊤ᵣ _))))
                              ≐ʳ-refl)))

                    -- the stacked renamings, before the arity variable is
                    -- substituted away
                    stacked : ∀ op' ε'
                            → C-rename (cong-∷-ren (cong-∷-ren
                                          (cong-⟨⟩-ren (cong-∷-ren sq))))
                                (H₁' op' ε')
                            ≡ C-rename (cong-ren {Γ'' = Dcl B op' ε'}
                                          (wk-ren {A = Ar}))
                                (C-rename (cong-∷-ren (cong-∷-ren R₀))
                                          (H op' ε'))
                    stacked op' ε' =
                      trans
                        (C-rename-cong R₃
                          (trans (C-rename-cong R₂' (eH₁ op' ε'))
                                 (sym (C-rename-∘ R₁' R₂' (H op' ε')))))
                        (trans
                          (sym (C-rename-∘ (R₁' ∘ʳ R₂') R₃ (H op' ε')))
                          (trans
                            (C-rename-≡ fused (H op' ε'))
                            (C-rename-∘ (cong-∷-ren (cong-∷-ren R₀))
                                        (cong-∷-ren (cong-∷-ren
                                          (cong-⟨⟩-ren (wk-ren {A = Ar}))))
                                        (H op' ε'))))
                      where
                        R₁' = cong-∷-ren (cong-∷-ren (steps-barrier-ren rs))
                        R₂' = cong-∷-ren (cong-∷-ren (barrier-wk-ren ρₒ Ar))
                        R₃  = cong-∷-ren (cong-∷-ren
                                (cong-⟨⟩-ren (cong-∷-ren sq)))

                        stack' : ((steps-barrier-ren rs ∘ʳ barrier-wk-ren ρₒ Ar)
                                   ∘ʳ cong-⟨⟩-ren (cong-∷-ren sq))
                               ≐ʳ (R₀ ∘ʳ cong-⟨⟩-ren (wk-ren {A = Ar}))
                        stack' =
                          ≐ʳ-trans
                            (∘ʳ-assoc-≐ʳ (steps-barrier-ren rs)
                                        (barrier-wk-ren ρₒ Ar)
                                        (cong-⟨⟩-ren (cong-∷-ren sq)))
                            stack

                        fused : ((R₁' ∘ʳ R₂') ∘ʳ R₃)
                              ≐ʳ (cong-∷-ren (cong-∷-ren R₀)
                                    ∘ʳ cong-∷-ren (cong-∷-ren
                                         (cong-⟨⟩-ren (wk-ren {A = Ar}))))
                        fused =
                          ≐ʳ-trans
                            (∘ʳ-≐ʳ (cong-cl-ren-∘-≐ʳ (steps-barrier-ren rs)
                                                    (barrier-wk-ren ρₒ Ar))
                                  ≐ʳ-refl)
                            (≐ʳ-trans
                              (cong-cl-ren-∘-≐ʳ
                                (steps-barrier-ren rs ∘ʳ barrier-wk-ren ρₒ Ar)
                                (cong-⟨⟩-ren (cong-∷-ren sq)))
                              (≐ʳ-trans
                                (cong-∷-ren-≐ʳ (cong-∷-ren-≐ʳ stack'))
                                (≐ʳ-sym (cong-cl-ren-∘-≐ʳ R₀
                                          (cong-⟨⟩-ren (wk-ren {A = Ar}))))))

                    -- and the substitution cancels the weakening
                    cancelled : ∀ op' ε'
                              → (((λ op'' ε'' →
                                      C-rename (cong-∷-ren (cong-∷-ren
                                                  (cong-⟨⟩-ren (cong-∷-ren sq))))
                                        (H₁' op'' ε''))
                                  [ split-[] {toCtx St'' ∷ Ar} ↦ W' ]cl) op' ε')
                              ≡ C-rename (cong-∷-ren (cong-∷-ren R₀)) (H op' ε')
                    cancelled op' ε' =
                      trans (sub-≡ᶜ (split-∷ (split-∷ (split-⟨⟩ split-[]))) (refl)
                                    (stacked op' ε'))
                            (sub-wk-C (Dcl B op' ε')
                              (C-rename (cong-∷-ren (cong-∷-ren R₀)) (H op' ε'))
                              W')

                    barrierEq : (R₀ ∘ʳ unbox-ren q₃) ≐ʳ unbox-ren q₄
                    barrierEq =
                      ≐ʳ-trans
                        (≐ʳ-sym (∘ʳ-assoc-≐ʳ R₀
                                   (suc-comp-ren (ext q₃) (reach-bound q₃))
                                   ⟨⟩-η-ren))
                        (∘ʳ-≐ʳ
                          (≐ʳ-sym (suc-comp-ren-∘-≐ʳ Eᶜ (ext q₃)
                                     (reach-bound q₄) (≾-⊤ᵣ _) (reach-bound q₃)))
                          ≐ʳ-refl)

                    step : C-rename (cong-∷-ren (cong-∷-ren (unbox-ren q₄)))
                             (H op₃ ε₄)
                         ≡ C-rename (cong-∷-ren (cong-∷-ren (unbox-ren q₃)))
                             (((λ op' ε' →
                                   C-rename (cong-∷-ren (cong-∷-ren
                                               (cong-⟨⟩-ren (cong-∷-ren sq))))
                                     (H₁' op' ε'))
                               [ split-[] {toCtx St'' ∷ Ar} ↦ W' ]cl) op₃ ε₄)
                    step =
                      trans
                        (C-rename-≡
                          (≐ʳ-trans
                            (cong-∷-ren-≐ʳ (cong-∷-ren-≐ʳ (≐ʳ-sym barrierEq)))
                            (≐ʳ-trans
                              (cong-∷-ren-≐ʳ
                                (cong-∷-ren-∘-≐ʳ R₀ (unbox-ren q₃)))
                              (cong-∷-ren-∘-≐ʳ (cong-∷-ren R₀)
                                              (cong-∷-ren (unbox-ren q₃)))))
                          (H op₃ ε₄))
                        (trans
                          (C-rename-∘ (cong-∷-ren (cong-∷-ren R₀))
                                      (cong-∷-ren (cong-∷-ren (unbox-ren q₃)))
                                      (H op₃ ε₄))
                          (C-rename-cong
                            (cong-∷-ren (cong-∷-ren (unbox-ren q₃)))
                            (sym (cancelled op₃ ε₄))))

------------------------------------------------------------------------
-- THE FIRED CLAUSE IS THE CLAUSE ENVIRONMENT'S ACTION
--
-- `env-Hˢ` at the empty suffix is the action at the clause suffix, and the
-- barrier crossing is the lock zone `_⟨_⟩ᵉ` at the same reach — so the two
-- sides are the same term.
------------------------------------------------------------------------

env-Hˢ-fired : ∀ {St Γ B} → (γ : Env St Γ) → {St₁ : 𝕊 []}
             → (q : St ⊑ₛ[ ⊤ᵣ ] St₁)
             → (H : Fam B (Γ ⟨ ⊤ᵣ ⟩)) → {op : Op} → {ε : E}
             → (V₀ : Boxed B op ε St₁)
             → (W : toCtx St₁ ⊢V⦂ type-of-gtype (param op))
             → Fired St op ε (env-Hˢ γ [] H) q V₀ W
             ≡ env-C (liftᵉ V₀ ((γ ⟨ q ⟩ᵉ) ∷ᵉ W)) (H op ε)

env-Hˢ-fired γ q H V₀ W = refl
