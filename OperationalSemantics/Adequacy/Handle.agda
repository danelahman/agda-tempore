------------------------------------------------------------------------
-- Handling preserves reducibility.                                   --
--                                                                    --
-- As `Bind`, plus a clause premise, and above `Environment` for the   --
-- same reason (`sub-wk-C`).                                           --
--                                                                    --
-- Both premises are stated at exactly the reduct the machine          --
-- produces. `HANDLE-OP` boxes the resumption at the operation's own   --
-- grade and `BOX` then allocates it, so the clause fires at           --
-- `St₁ ∷ₛ V₀` with its continuation binder *being* the fresh cell —   --
-- no store to propagate (`∅ᵉ`) and nothing to contract (`liftᵉ`).     --
------------------------------------------------------------------------

open import Data.Product

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
open import OperationalSemantics.Adequacy.RenEquivalence Spec
open import OperationalSemantics.Adequacy.Slice          Spec
open import OperationalSemantics.Adequacy.SubEquivalence Spec

------------------------------------------------------------------------
-- THE TWO PREMISES
--
-- The clause premise: at the state the operation is handled at, with the
-- resumption already boxed and allocated. `V₀` is the boxed resumption in the
-- shape `_∷ₛ_` stores it, and the hypothesis about it is exactly
-- `store-fresh`'s — reducible at every state the lock permits.
------------------------------------------------------------------------

Boxed : (B : VType) → (op : Op) → (ε₃ : E) → 𝕊 [] → Set
Boxed B op ε₃ St₁ =
  ([] ++ᶜ toCtx St₁ ⟨ mapᵉ (op-grade op) ⟩)
  ⊢V⦂ (type-of-gtype (arity op) ⇒ B ‼ ε₃)

Boxed-Val : (B : VType) → (op : Op) → (ε₃ : E)
          → (St₁ : 𝕊 []) → Boxed B op ε₃ St₁ → Set
Boxed-Val B op ε₃ St₁ V₀ =
  ∀ {St'} → (q : Slice St₁ (mapᵉ (op-grade op)) St' uᵣ)
    → Val (type-of-gtype (arity op) ⇒ B ‼ ε₃) St'
          (V-rename (unbox-ren q ∘ʳ eq-ren ++ᶜ-identityˡ) V₀)

-- The clause, included into the context it fires at and given the operation's
-- parameter. Its continuation binder is the cell `BOX` just allocated, so this
-- lives over `toCtx (St₁ ∷ₛ V₀)` and nothing further is substituted.

Fired : ∀ {B} → (St : 𝕊 []) → (op : Op) → (ε₃ : E)
      → ((op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St ᴱ))
      → (St₁ : 𝕊 []) → (V₀ : Boxed B op ε₃ St₁)
      → toCtx St₁ ⊢V⦂ type-of-gtype (param op)
      → toCtx (St₁ ∷ₛ V₀) ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)
Fired {B} St op ε₃ H St₁ V₀ W =
  (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren (toCtx St₁))))
     (subst (Cl B op ε₃) (toCtxᴱ-≡ St St₁) (H op ε₃)))
    [ Tl-∷ Hd ↦ W ]c

Clause-Prem : (B : VType) → (St : 𝕊 [])
            → ((op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St ᴱ)) → Set
Clause-Prem B St H =
  ∀ {St₁ : 𝕊 []} {op : Op} {ε₃ : E}
    → (V₀ : Boxed B op ε₃ St₁) → Boxed-Val B op ε₃ St₁ V₀
    → (W : toCtx St₁ ⊢V⦂ type-of-gtype (param op))
    → Val (type-of-gtype (param op)) St₁ W
    → Comp' B (op-grade op ·ₑ ε₃) (St₁ ∷ₛ V₀) (Fired St op ε₃ H St₁ V₀ W)

-- The sequel premise, as in `Bind`.

Seq-Prem : ∀ {A B ε₁ ε₂} {St : 𝕊 []}
         → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂) → Set
Seq-Prem {A} {B} {ε₁} {ε₂} {St} N =
  ∀ {St₁ : 𝕊 []} → (q : Slice St (mapᵉ ε₁) St₁ uᵣ)
    → (V : toCtx St₁ ⊢V⦂ A) → Val A St₁ V
    → Comp' B ε₂ St₁ ((C-rename (cong-∷-ren (unbox-ren q)) N) [ Hd ↦ V ]c)

------------------------------------------------------------------------
-- WHAT SUBSTITUTION LEAVES OF THE CLAUSES
--
-- `_[_↦_]c`'s `handle` clause is a `with` on `eternal? A`, so it does not reduce
-- at an abstract type. This mirrors its two branches at the *head* variable —
-- the one `Val`'s arrow clause substitutes — so that a `rewrite` on the `Dec`
-- makes the definition and the mirror agree definitionally. Taking the `Dec` as
-- a parameter rather than a `with` is what lets that `rewrite` fire at all.
------------------------------------------------------------------------

sub-clauses : ∀ {B A'} {St'' : 𝕊 []} → Dec (Eternal A')
            → ((op' : Op) → (ε' : E) → Cl B op' ε' ((toCtx St'' ∷ A') ᴱ))
            → toCtx St'' ⊢V⦂ A'
            → (op' : Op) → (ε' : E) → Cl B op' ε' (toCtx St'' ᴱ)

sub-clauses {B} {A'} {St''} (no ¬et) Hᵣ W' op' ε' =
  subst (λ Γ₀ → Cl B op' ε' Γ₀) (ᴱ-drop-split ¬et (Hd {Γ = toCtx St''}))
        (Hᵣ op' ε')

sub-clauses {B} {A'} {St''} (yes et) Hᵣ W' op' ε' =
  subst (_⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
    (trans (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
      (trans (sym (++ᶜ-assoc ((toCtx St'') ᴱ) (([] {- split-r Hd -}) ᴱ) D))
             (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (toCtx St'') [])))))
    ((Hᵣ op' ε') [ split→∈ s
                    ↦ subst (_⊢V⦂ A') (sym (split→∈-split-l s))
                         (eternal-val-restrict et W') ]c)
  where
    D = [] ∷ type-of-gtype (param op')
           ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
    s = split-++ʳ (∈-ᴱ-split et (Hd {Γ = toCtx St''})) D

------------------------------------------------------------------------
-- HANDLING
--
-- Induction on the scrutinee's `Comp` derivation. `comp-ret` fires `HANDLE-RET`
-- and is `Bind`'s `comp-ret` verbatim — the sequel premise consumes the value
-- and the run's `mapᵉ uₑ` is reconciled with the slice's `uᵣ` by
-- `suc-comp-ren-grade`.
------------------------------------------------------------------------

handle-Comp : ∀ {A B ε₁ ε₂} {St : 𝕊 []}
            → {M : toCtx St ⊢C⦂ A ‼ ε₁}
            → (H : (op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St ᴱ))
            → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
            → Comp' A ε₁ St M
            → Clause-Prem B St H
            → Seq-Prem N
            ------------------------------------------------------------
            → Comp' B (ε₁ ·ₑ ε₂) St (handle M `with H `in N)

-- The scrutinee returns: `HANDLE-RET`, and the clauses are discarded.

handle-Comp {A} {B} {ε₁} {ε₂} {St} H N
            (comp-ret {St₁ = St₁} {V = V} rs pV) hH hN
  with handle-steps rs H N

... | H₁ , N₁ , rs' , eH₁ , eN₁ =
  Comp-expand* rs'
    (Comp-expand HANDLE-RET
      (Comp-≐ᶜ (sub-≐ᶜ Hd (≐ᵛ-refl V) shift) (hN q V pV)))
  where
    E₀  = steps-extends-state rs
    srs = suc-comp-ren E₀ (steps-grade-≾ rs)

    b : ≤ₛ-grade E₀ ·ᵣ uᵣ ≾ᵣ mapᵉ ε₁
    b = ≾ᵣ-trans (≾ᵣ-reflexive (cong (≤ₛ-grade E₀ ·ᵣ_) (sym map-uᵉ)))
                 (steps-grade-≾ rs)

    q = slice E₀ b

    R₁ : Ren [] (toCtx St₁ ⟨ mapᵉ uₑ ⟩) (toCtx St₁)
    R₁ = ⟨⟩-η-ren ∘ʳ eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ)

    eqr : (R₁ ∘ʳ srs) ≐ʳ unbox-ren q
    eqr = ≐ʳ-trans (∘ʳ-assoc-≐ ⟨⟩-η-ren (eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ)) srs)
                   (∘ʳ-≐ ≐ʳ-refl
                     (suc-comp-ren-grade E₀ map-uᵉ (steps-grade-≾ rs) b))

    shift : C-rename (cong-∷-ren (unbox-ren q)) N
          ≐ᶜ C-rename (cong-∷-ren R₁) N₁
    shift =
      ≐ᶜ-sym
        (≐ᶜ-trans (C-rename-cong (cong-∷-ren R₁) eN₁)
          (≐ᶜ-trans (≐ᶜ-sym (C-rename-∘ (cong-∷-ren R₁) (cong-∷-ren srs) N))
            (C-rename-≐ (≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ R₁ srs))
                                  (cong-∷-ren-≐ eqr)) N)))

-- The scrutinee gets stuck on an operation. The reduct chain is
--
--   handle-steps rs H N   -- run to the `perform`
--   HANDLE-OP             -- box the resumption
--   BOX                   -- allocate it
--
-- landing at `⟨ St₁ ∷ₛ V₀ , Fired … ⟩`. `Fired` is `HANDLE-OP`'s clause instance
-- once `handle-steps`'s `H₁ op ε ≡ subst (Cl …) (toCtxᴱ-≡ St St₁) (H op ε)` is
-- read backwards, and the effects need no `ε-subst`: `_↝_` relates
-- configurations at different effects, and `box`'s body carries
-- `op-grade op ·ₑ (ε₃ ·ₑ ε₂)` where the redex carries `(op-grade op ·ₑ ε₃) ·ₑ ε₂`.

handle-Comp {A} {B} {ε₁} {ε₂} {St} H N
            (comp-op {ε₁ = ε₃} {St₁ = St₁} {op = op} {W = W} {M' = M'} rs pW pk)
            hH hN
  with handle-steps rs H N

... | H₁ , N₁ , rs' , eH₁ , eN₁ =
  Comp-expand* rs'
    (Comp-expand HANDLE-OP
      (Comp-expand BOX
        (subst (Comp' B _ (St₁ ∷ₛ V₀)) fired
          (hH V₀ bval W (Valᵍ→Val (param op) W pW)))))
  where
    ρₒ = mapᵉ (op-grade op)
    Ar = type-of-gtype (arity op)

    -- the clauses and sequel `HANDLE-OP` puts under the boxed resumption
    H₁' : (op' : Op) → (ε' : E) → Cl B op' ε' ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ᴱ)
    H₁' op' ε' =
      C-rename (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {toCtx St₁ ⟨ ρₒ ⟩} Ar))) (H₁ op' ε')

    N₁' = C-rename
            (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren
                           ∘ʳ eq-ren (cong (toCtx St₁ ⟨_⟩) map-·ᵉ)))
            N₁

    Body = handle M' `with H₁' `in N₁'

    V₀ : Boxed B op (ε₃ ·ₑ ε₂) St₁
    V₀ = V-rename (eq-ren (sym ++ᶜ-identityˡ)) (lam Body)

    fired : Fired St op (ε₃ ·ₑ ε₂) H St₁ V₀ W
          ≡ (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren (toCtx St₁))))
               (H₁ op (ε₃ ·ₑ ε₂))) [ Tl-∷ Hd ↦ W ]c
    fired =
      cong (λ z → (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren (toCtx St₁)))) z)
                    [ Tl-∷ Hd ↦ W ]c)
           (sym (eH₁ op (ε₃ ·ₑ ε₂)))

    -- The boxed resumption *is* a lambda, so `Val`'s arrow clause is met by its
    -- own body; the two `eq-ren`s cancel and `slice-unbox-ren-≐` composes the
    -- unboxing with the clause's own slice.

    bval : Boxed-Val B op (ε₃ ·ₑ ε₂) St₁ V₀
    bval {St'} q = _ , refl , resump
      where
        Mq = C-rename (cong-∷-ren (unbox-ren q ∘ʳ eq-ren ++ᶜ-identityˡ))
               (C-rename (cong-∷-ren (eq-ren (sym (++ᶜ-identityˡ
                                                    {toCtx St₁ ⟨ ρₒ ⟩})))) Body)

        resump : ∀ {St'' : 𝕊 []} → (q' : Slice St' uᵣ St'' uᵣ)
               → (M₂ : toCtx St'' ∷ Ar ⊢C⦂ B ‼ (ε₃ ·ₑ ε₂))
               → M₂ ≐ᶜ slice-under q' Mq
               → (W' : toCtx St'' ⊢V⦂ Ar) → Val Ar St'' W'
               → Comp' B (ε₃ ·ₑ ε₂) St'' (M₂ [ Hd ↦ W' ]c)

        resump {St''} q' M₂ eM₂ W' pW' =
          Comp-≐ᶜ (≐ᶜ-sym (sub-≐ᶜ Hd (≐ᵛ-refl W') collapse)) inner
          where
            q₂ = slice-∘ q' q

            R₂ = (unbox-ren q ∘ʳ eq-ren (++ᶜ-identityˡ {toCtx St₁ ⟨ ρₒ ⟩}))
                   ∘ʳ eq-ren (sym (++ᶜ-identityˡ {toCtx St₁ ⟨ ρₒ ⟩}))

            -- the three renamings the clause stacks up compose to `unbox-ren q₂`
            ren-eq : (slice-renᵘ q' ∘ʳ R₂) ≐ʳ unbox-ren q₂
            ren-eq =
              ≐ʳ-trans
                (∘ʳ-≐ ≐ʳ-refl
                  (≐ʳ-trans
                    (∘ʳ-assoc-≐ (unbox-ren q) (eq-ren ++ᶜ-identityˡ)
                                (eq-ren (sym ++ᶜ-identityˡ)))
                    (∘ʳ-id-≐ʳ (unbox-ren q)
                      (≐ʳ-trans
                        (eq-ren-∘-≐ (sym (++ᶜ-identityˡ {toCtx St₁ ⟨ ρₒ ⟩}))
                                    ++ᶜ-identityˡ)
                        (eq-ren-≐ _ refl)))))
                (slice-unbox-ren-≐ q' q)

            collapse : M₂ ≐ᶜ C-rename (cong-∷-ren (unbox-ren q₂)) Body
            collapse =
              ≐ᶜ-trans eM₂
                (≐ᶜ-trans
                  (C-rename-cong (cong-∷-ren (slice-renᵘ q'))
                    (≐ᶜ-trans
                      (≐ᶜ-sym (C-rename-∘
                                 (cong-∷-ren (unbox-ren q ∘ʳ eq-ren ++ᶜ-identityˡ))
                                 (cong-∷-ren (eq-ren (sym ++ᶜ-identityˡ)))
                                 Body))
                      (C-rename-≐
                        (≐ʳ-sym (cong-∷-ren-∘-≐
                                   (unbox-ren q ∘ʳ eq-ren ++ᶜ-identityˡ)
                                   (eq-ren (sym ++ᶜ-identityˡ))))
                        Body)))
                  (≐ᶜ-trans
                    (≐ᶜ-sym
                      (C-rename-∘ (cong-∷-ren (slice-renᵘ q'))
                                  (cong-∷-ren R₂) Body))
                    (C-rename-≐
                      (≐ʳ-trans
                        (≐ʳ-sym (cong-∷-ren-∘-≐ (slice-renᵘ q') R₂))
                        (cong-∷-ren-≐ ren-eq))
                      Body)))

            -- WHAT IS LEFT, and why it is not just plumbing.
            --
            -- Both branches of the reduction are the same recursive call
            --
            --   handle-Comp _ _ (pk q₂ W' (Val→Valᵍ (arity op) W' pW')) hH₂ hN₂
            --
            -- — the scrutinee reached *is* `resume q₂ M' W'` definitionally,
            -- renaming and substitution both distributing over `handle`, and
            -- `sub-clauses` above already names the clauses each branch leaves.
            -- What blocks it is that the reduction cannot be taken here at all:
            --
            --   * `_[_↦_]c`'s `handle` clause is a `with` on `eternal? Ar`, so
            --     the substitution is stuck;
            --   * `with eternal? Ar` does not unstick it, because `_ᴱ` is *also*
            --     a `with` on `eternal? Ar` (`Contexts.agda`), so the clause
            --     family's own context `(toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ᴱ` is stuck too
            --     and the abstraction misses that occurrence — it sits under an
            --     unreduced `_ᴱ` rather than syntactically in the goal;
            --   * `rewrite` fails for the same reason, at every nesting depth,
            --     including in a top-level lemma taking the `Dec` as a parameter.
            --
            -- Nor is either branch vacuous: `arity op` is a `GType`, and
            -- `[ ρ ]ᵍ G` maps to a box type, which is never eternal.
            --
            -- Unsticking it needs `_ᴱ`'s `∷` clause restated through a helper
            -- taking the `Dec`, so that `_ᴱ` stops being a `with`-function —
            -- a change in `Syntax/Contexts.agda` that touches the development.
            --
            -- The two premises then remain: `hN₂` from `hN` by `sub-wk-C`
            -- (`resume`'s substitution cancels `N₁'`'s arity weakening, as in
            -- `Bind`'s `comp-op`), and `hH₂` from `hH` by clause bookkeeping —
            -- where the angle is that every renaming involved has source
            -- `toCtx St₁ ᴱ ≡ []`, so `∅-ren-≐` should identify them.
            postulate
              inner : Comp' B (ε₃ ·ₑ ε₂) St''
                        ((C-rename (cong-∷-ren (unbox-ren q₂)) Body)
                           [ Hd ↦ W' ]c)
