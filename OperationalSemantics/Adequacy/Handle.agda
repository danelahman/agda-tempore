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
    ρₒ  = mapᵉ (op-grade op)
    Ar  = type-of-gtype (arity op)
    E₀  = steps-extends-state rs
    b₀  = steps-grade-≾ rs
    srs = suc-comp-ren E₀ b₀

    emap : toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩
         ≡ toCtx St₁ ⟨ ρₒ ·ᵣ mapᵉ ε₃ ⟩
    emap = cong (toCtx St₁ ⟨_⟩) map-·ᵉ

    κ : Ren [] (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
              ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ⟨ mapᵉ ε₃ ⟩)
    κ = cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren emap

    -- the clauses and sequel `HANDLE-OP` puts under the boxed resumption
    H₁' : (op' : Op) → (ε' : E) → Cl B op' ε' ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ᴱ)
    H₁' op' ε' =
      C-rename (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {toCtx St₁ ⟨ ρₒ ⟩} Ar))) (H₁ op' ε')

    N₁' = C-rename (cong-∷-ren κ) N₁

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

            -- The reduct *is* the recursive call: renaming distributes over
            -- `handle` definitionally, `_[_↦_]c` now does too (its eternality
            -- split having moved into `⟨_⟩[_↦_]cl`), and the scrutinee reached
            -- is `resume q₂ M' W'`.
            inner : Comp' B (ε₃ ·ₑ ε₂) St''
                      ((C-rename (cong-∷-ren (unbox-ren q₂)) Body)
                         [ Hd ↦ W' ]c)
            inner =
              handle-Comp _ _ (pk q₂ W' (Val→Valᵍ (arity op) W' pW')) hH₂ hN₂
              where
                sq = unbox-ren q₂

                bq : ≤ₛ-grade (ext q₂) ≾ᵣ ρₒ
                bq = ≾ᵣ-trans
                       (≾ᵣ-reflexive (sym (·ᵣ-identityʳ (≤ₛ-grade (ext q₂)))))
                       (bound q₂)

                B₁' : ≤ₛ-grade (ext q₂) ·ᵣ mapᵉ ε₃ ≾ᵣ ρₒ ·ᵣ mapᵉ ε₃
                B₁' = ·ᵣ-monoˡ-≾ᵣ bq

                B₁ : ≤ₛ-grade (ext q₂) ·ᵣ mapᵉ ε₃
                   ≾ᵣ mapᵉ (op-grade op ·ₑ ε₃)
                B₁ = ≾ᵣ-trans B₁' (≾ᵣ-reflexive (sym map-·ᵉ))

                sB : Slice St₁ (mapᵉ (op-grade op ·ₑ ε₃)) St'' (mapᵉ ε₃)
                sB = slice (ext q₂) B₁

                -- what is left of the sequel's renaming once the arity variable
                -- is gone
                W₁ : Ren [] (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
                          (toCtx St'' ⟨ mapᵉ ε₃ ⟩)
                W₁ = cong-⟨⟩-ren sq ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren emap

                eW₁ : W₁ ≐ʳ suc-comp-ren (ext q₂) B₁
                eW₁ =
                  ≐ʳ-trans
                    (≐ʳ-sym (∘ʳ-assoc-≐ (cong-⟨⟩-ren sq) ⟨⟩-μ-ren (eq-ren emap)))
                    (≐ʳ-trans (∘ʳ-≐ (unbox-ren-μ-≐ q₂ B₁') ≐ʳ-refl)
                              (suc-comp-ren-grade-src (ext q₂) map-·ᵉ B₁' B₁))

                -- the sequel the recursion needs is the original one, renamed:
                -- `HANDLE-OP` weakens it past the arity variable and `resume`
                -- substitutes for exactly that variable, so the two cancel
                eN₂ : (C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₁')
                        [ Tl-∷ (Tl-⟨⟩ Hd) ↦ W' ]c
                    ≐ᶜ C-rename (cong-∷-ren (W₁ ∘ʳ srs)) N
                eN₂ =
                  ≐ᶜ-trans (sub-≐ᶜ (Tl-∷ (Tl-⟨⟩ Hd)) (≐ᵛ-refl W') split-off)
                    (≐ᶜ-trans (sub-wk-C ([] ⟨ mapᵉ ε₃ ⟩ ∷ A)
                                        (C-rename (cong-∷-ren W₁) N₁) W')
                      (≐ᶜ-trans (C-rename-cong (cong-∷-ren W₁) eN₁)
                        (≐ᶜ-trans
                          (≐ᶜ-sym (C-rename-∘ (cong-∷-ren W₁)
                                              (cong-∷-ren srs) N))
                          (C-rename-≐ (≐ʳ-sym (cong-∷-ren-∘-≐ W₁ srs)) N))))
                  where
                    innerᵣ : (cong-⟨⟩-ren (cong-∷-ren sq) ∘ʳ κ)
                           ≐ʳ (cong-⟨⟩-ren wk-ren ∘ʳ W₁)
                    innerᵣ =
                      ≐ʳ-trans
                        (≐ʳ-sym (∘ʳ-assoc-≐ (cong-⟨⟩-ren (cong-∷-ren sq))
                                            (cong-⟨⟩-ren wk-ren)
                                            (⟨⟩-μ-ren ∘ʳ eq-ren emap)))
                        (≐ʳ-trans
                          (∘ʳ-≐ (≐ʳ-trans
                                  (≐ʳ-sym (cong-⟨⟩-ren-∘-≐ (cong-∷-ren sq) wk-ren))
                                  (≐ʳ-trans (cong-⟨⟩-ren-≐ (wk-ren-nat-≐ sq))
                                            (cong-⟨⟩-ren-∘-≐ wk-ren sq)))
                                ≐ʳ-refl)
                          (∘ʳ-assoc-≐ (cong-⟨⟩-ren wk-ren) (cong-⟨⟩-ren sq)
                                      (⟨⟩-μ-ren ∘ʳ eq-ren emap)))

                    split-off : C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq)))
                                         N₁'
                              ≐ᶜ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren))
                                   (C-rename (cong-∷-ren W₁) N₁)
                    split-off =
                      ≐ᶜ-trans
                        (≐ᶜ-sym (C-rename-∘
                                   (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq)))
                                   (cong-∷-ren κ) N₁))
                        (≐ᶜ-trans
                          (C-rename-≐
                            (≐ʳ-trans
                              (≐ʳ-sym (cong-∷-ren-∘-≐
                                         (cong-⟨⟩-ren (cong-∷-ren sq)) κ))
                              (≐ʳ-trans (cong-∷-ren-≐ innerᵣ)
                                        (cong-∷-ren-∘-≐ (cong-⟨⟩-ren wk-ren) W₁)))
                            N₁)
                          (C-rename-∘ (cong-∷-ren (cong-⟨⟩-ren wk-ren))
                                      (cong-∷-ren W₁) N₁))

                hN₂ : Seq-Prem ((C-rename
                                   (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₁')
                                  [ Tl-∷ (Tl-⟨⟩ Hd) ↦ W' ]c)
                hN₂ {St₃} q₃ V pV =
                  Comp-≐ᶜ (sub-≐ᶜ Hd (≐ᵛ-refl V) shift) (hN q₄ V pV)
                  where
                    s₁₂ = slice-∘ sB (steps-slice rs)
                    q₄  = slice-∘ q₃ s₁₂

                    composite : suc-comp-ren (ext q₄) (bound q₄)
                              ≐ʳ (suc-comp-ren (ext q₃) (bound q₃)
                                    ∘ʳ (W₁ ∘ʳ srs))
                    composite =
                      ≐ʳ-trans
                        (suc-comp-ren-∘-≐ (≤ₛ-trans E₀ (ext q₂)) (ext q₃)
                                          (bound q₄) (bound s₁₂) (bound q₃))
                        (∘ʳ-≐ ≐ʳ-refl
                          (≐ʳ-trans
                            (suc-comp-ren-∘-≐ E₀ (ext q₂) (bound s₁₂) b₀ B₁)
                            (∘ʳ-≐ (≐ʳ-sym eW₁) ≐ʳ-refl)))

                    finalEq : unbox-ren q₄ ≐ʳ (unbox-ren q₃ ∘ʳ (W₁ ∘ʳ srs))
                    finalEq =
                      ≐ʳ-trans (∘ʳ-≐ (≐ʳ-refl {r = ⟨⟩-η-ren}) composite)
                        (≐ʳ-sym (∘ʳ-assoc-≐ ⟨⟩-η-ren
                                   (suc-comp-ren (ext q₃) (bound q₃))
                                   (W₁ ∘ʳ srs)))

                    shift : C-rename (cong-∷-ren (unbox-ren q₄)) N
                          ≐ᶜ C-rename (cong-∷-ren (unbox-ren q₃))
                               ((C-rename
                                   (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₁')
                                  [ Tl-∷ (Tl-⟨⟩ Hd) ↦ W' ]c)
                    shift =
                      ≐ᶜ-trans
                        (C-rename-≐
                          (≐ʳ-trans (cong-∷-ren-≐ finalEq)
                                    (cong-∷-ren-∘-≐ (unbox-ren q₃)
                                                    (W₁ ∘ʳ srs))) N)
                        (≐ᶜ-trans
                          (C-rename-∘ (cong-∷-ren (unbox-ren q₃))
                                      (cong-∷-ren (W₁ ∘ʳ srs)) N)
                          (C-rename-cong (cong-∷-ren (unbox-ren q₃))
                                         (≐ᶜ-sym eN₂)))

                -- WHAT IS LEFT: the clause premise, rebuilt from `hH`.
                --
                -- It suffices that `Fired`'s two clause instances agree, since
                -- `Fired` is a renaming and a substitution of them, both
                -- congruences; then `hH₂ = Comp-≐ᶜ … (hH …)`. So the goal is
                --
                --   subst (Cl B op₃ ε₄) (toCtxᴱ-≡ St'' St₃) (H₂ op₃ ε₄)
                --   ≐ᶜ subst (Cl B op₃ ε₄) (toCtxᴱ-≡ St   St₃) (H  op₃ ε₄)
                --
                -- where `H₂` is `H` pushed along: `eH₁`'s transport, the
                -- `ren-ᴱ-∷ Ar` inclusion, `restrict-ren (cong-∷-ren sq)`, and
                -- `⟨ eternal? Ar ⟩[ Hd ↦ W' ]cl`.
                --
                -- Two lemmas close it, and both are within reach now that `_ᴱ`
                -- and `_[_↦_]c` expose the decision:
                --
                --   * *the inclusion cancels the substitution*: at an eternal
                --     `Ar`, `ren-ᴱ-∷′ Ar (yes et)` is `wk-ren` and
                --     `⟨ yes et ⟩[ Hd ↦ W' ]cl` substitutes for exactly that
                --     binder, so `sub-wk-C` cancels them (its splitting
                --     `split-++ʳ (∈-ᴱ-split et Hd) D` *is* `split-≡-++ᶜ`
                --     definitionally, `D` being built from `[]`); at a
                --     non-eternal one the inclusion is `id-ren` and the
                --     substitution only retypes, so `uip` finishes.
                --   * *renamings out of a clause context over a state agree when
                --     they agree on the clause's own two variables*: the eternal
                --     part is `[]` (`toCtxᴱ-[]`), so `∈-++ᶜ-split` sends every
                --     variable to `D` and the rest is `∈-++ᶜ-split-inj₂`. This
                --     is what makes `restrict-ren (cong-∷-ren sq)` and the two
                --     `toCtxᴱ-≡` transports interchangeable.
                --
                -- The `Dec`-parameter rollout is complete — `_ᴱ`, `_[_↦_]c`'s
                -- `handle` clause, `ren-ᴱ-∷`, `restrict-ren`'s three clauses and
                -- `ᴱ-ren`'s `∷` clause all take the decision now.
                --
                -- What still blocks the first lemma is `⟨_⟩[_↦_]cl`'s *signature*:
                -- its family argument sits at `Γ ᴱ` for `Γ` the substituted
                -- variable's own context, so at `Γ := Γ₀ ∷ A` and `x := Hd` the
                -- family's type recomputes `eternal? A` independently of the
                -- `dec` argument. A `with`/`rewrite` at a use site abstracts one
                -- and not the other, and the application stops typechecking —
                -- in either direction. Tying the two together (an `ᴱ-∷`-shaped
                -- family argument for the head case, or an abstract context plus
                -- an equation) is the design decision to take next.
                postulate
                  hH₂ : Clause-Prem B St'' _
