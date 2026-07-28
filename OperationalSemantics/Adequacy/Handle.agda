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

-- The scrutinee gets stuck on an operation. The reduct chain is settled:
--
--   handle-steps rs H N                        -- run to the `perform`
--   HANDLE-OP                                  -- box the resumption
--   BOX                                        -- allocate it
--
-- landing at `⟨ St₁ ∷ₛ V₀ , Fired … ⟩` with
-- `V₀ = V-rename (eq-ren (sym ++ᶜ-identityˡ)) (lam (handle M' `with H₁' `in N₁'))`,
-- and `Fired` *is* `HANDLE-OP`'s clause instance once `handle-steps`'s
-- `H₁ op ε ≡ subst (Cl …) (toCtxᴱ-≡ St St₁) (H op ε)` is read backwards. The
-- effects need no `ε-subst`: `_↝_` relates configurations at different effects,
-- and `box`'s body carries `op-grade op ·ₑ (ε₃ ·ₑ ε₂)` where the redex carries
-- `(op-grade op ·ₑ ε₃) ·ₑ ε₂`.
--
-- What is left is the clause premise's `Boxed-Val` argument: the boxed
-- resumption reducible at every state its lock permits. Unfolding `Val`'s arrow
-- clause there gives a `handle` at that state, so it is the recursive call on
-- `pk` — and the recursion needs its own two premises rebuilt from these:
--
--   * `Seq-Prem` for `N₁'`, which is `N₁` weakened past the operation's arity
--     variable by `cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong … map-·ᵉ)`.
--     That weakening is undone by `sub-wk-C` exactly as in `Bind`'s `comp-op`
--     case, with `unbox-ren-μ-≐` recognising the composite;
--   * `Clause-Prem` for `H₁'`, which is `H₁` included by
--     `ren-ᴱ-∷ (type-of-gtype (arity op))`. Reconciling that inclusion with the
--     `ᴱ-ren` of `Fired` at the *new* state is the clause bookkeeping — the same
--     kind that `sub-wk-handle` needed.

handle-Comp {A} {B} {ε₁} {ε₂} {St} H N
            (comp-op {ε₁ = ε₃} {St₁ = St₁} {op = op} {W = W} {M' = M'} rs pW pk)
            hH hN = handle-Comp-op H N rs pW pk hH hN

  where
    postulate
      handle-Comp-op : ∀ {A B ε₁ ε₂ ε₃} {St St₁ : 𝕊 []} {op : Op}
                     → {M : toCtx St ⊢C⦂ A ‼ ε₁}
                     → {W : toCtx St₁ ⊢V⦂ type-of-gtype (param op)}
                     → {M' : toCtx St₁ ⟨ mapᵉ (op-grade op) ⟩
                               ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε₃}
                     → (H : (op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St ᴱ))
                     → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
                     → ⟨ St , M ⟩ ↝* ⟨ St₁ , perform op W M' ⟩
                     → Valᵍ (param op) St₁ W
                     → (∀ {St₂ : 𝕊 []}
                        → (q : Slice St₁ (mapᵉ (op-grade op)) St₂ uᵣ)
                        → (W' : toCtx St₂ ⊢V⦂ type-of-gtype (arity op))
                        → Valᵍ (arity op) St₂ W'
                        → Comp' A ε₃ St₂ (resume q M' W'))
                     → Clause-Prem B St H
                     → Seq-Prem N
                     → Comp' B (ε₁ ·ₑ ε₂) St (handle M `with H `in N)
