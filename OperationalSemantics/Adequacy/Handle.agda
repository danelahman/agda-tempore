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
-- RENAMINGS BETWEEN CLAUSE CONTEXTS OVER A STATE
--
-- A clause over a state's eternal context lives at `toCtx St ᴱ ++ᶜ D` with
-- `D = [] ∷ param ∷ cont`, and `toCtx St ᴱ` is `[]` (`toCtxᴱ-[]`). So a renaming
-- out of it is pinned by what it does to `D`'s two variables alone — which is
-- what lets the chain `ren-ᴱ-∷`/`restrict-ren`/transports be collapsed without
-- ever reducing any of them.
------------------------------------------------------------------------

cl-ren-≐ : ∀ {Γ'} → (St : 𝕊 []) → (D : Ctx)
         → {r r' : Ren [] (toCtx St ᴱ ++ᶜ D) Γ'}
         → (∀ {A ρ} → (y : A ∈[ ρ ] D)
              → var-tgt r  (∈-++ᶜʳ {Γ = toCtx St ᴱ} y)
              ≡ var-tgt r' (∈-++ᶜʳ {Γ = toCtx St ᴱ} y))
         → r ≐ʳ r'

cl-ren-≐ St D {r} {r'} h = mk≐ʳ go
  where
    go : ∀ {A ρ} → (x : A ∈[ ρ ] (toCtx St ᴱ ++ᶜ D))
       → var-tgt r x ≡ var-tgt r' x
    go x with ∈-++ᶜ-split (toCtx St ᴱ) D x in eq
    ... | inj₁ (ρ' , z) =
      ⊥-elim (not-in-empty-ctx
               (subst (λ Γ₀ → _ ∈[ ρ' ] Γ₀) (toCtxᴱ-[] St) z))
    ... | inj₂ y rewrite ∈-++ᶜ-split-inj₂ (toCtx St ᴱ) D x y eq = h y

-- Relocating a pushed suffix variable along an equality of the prefix.

∈-++ᶜʳ-cast : ∀ {Γ Γ' A ρ} → (D : Ctx) → (e₀ : Γ ≡ Γ') → (y : A ∈[ ρ ] D)
            → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (cong (_++ᶜ D) e₀) (∈-++ᶜʳ {Γ = Γ} y)
            ≡ ∈-++ᶜʳ {Γ = Γ'} y
∈-++ᶜʳ-cast D refl y = refl

-- Hence: a congruence renaming out of such a context is the transport, whatever
-- it is built from — the two agree on `D` by `cong-ren-tgt-r` and `eq-ren-tgt`.

cl-ren-eq-≐ : ∀ {Γ₁} → (St : 𝕊 []) → (D : Ctx)
            → (r₀ : Ren [] (toCtx St ᴱ) Γ₁) → (e₀ : toCtx St ᴱ ≡ Γ₁)
            → cong-ren {Γ'' = D} r₀ ≐ʳ eq-ren (cong (_++ᶜ D) e₀)

cl-ren-eq-≐ St D r₀ e₀ =
  cl-ren-≐ St D
    (λ y → trans (cong-ren-tgt-r r₀ y)
             (sym (trans (eq-ren-tgt (cong (_++ᶜ D) e₀) (∈-++ᶜʳ y))
                         (cong (λ z → _ , z) (∈-++ᶜʳ-cast D e₀ y)))))

-- Transports of a clause along its eternal context compose. (`subst-fuseᶜ` is
-- at the motive `_⊢C⦂ C`; a clause is transported at `Cl B op ε`, which moves
-- the context *under* two binders.)

subst-fuse-cl : ∀ {B op ε} {Γ₁ Γ₂ Γ₃ : Ctx}
              → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (X : Cl B op ε Γ₁)
              → subst (Cl B op ε) e' (subst (Cl B op ε) e X)
              ≡ subst (Cl B op ε) (trans e e') X
subst-fuse-cl refl refl X = refl

-- Three such transports whose composite has the same endpoints as a fourth.

subst-collapse-cl : ∀ {B op ε} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
                  → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃) → (e₃ : Γ₃ ≡ Γ₄)
                  → (e₄ : Γ₁ ≡ Γ₄) → (X : Cl B op ε Γ₁)
                  → subst (Cl B op ε) e₃
                      (subst (Cl B op ε) e₂ (subst (Cl B op ε) e₁ X))
                  ≡ subst (Cl B op ε) e₄ X
subst-collapse-cl refl refl refl e₄ X =
  cong (λ z → subst (Cl _ _ _) z X) (uip {p = refl} {q = e₄})

------------------------------------------------------------------------
-- TAKING THE ETERNALITY SPLIT WHERE THE CONTEXT IS STILL ABSTRACT
--
-- `⟨_⟩[_↦_]cl`'s clause family sits at `Γ ᴱ` for `Γ` the substituted variable's
-- own context. At a *concrete* `Γ := Γ₀ ∷ A` that reduces and recomputes
-- `eternal? A` independently of the `dec` argument, so a `with` there abstracts
-- one occurrence and not the other and the application stops typechecking.
--
-- Here `Γ` and `x` are parameters, so `Γ ᴱ` does not reduce and the only
-- occurrence is the decision itself. Each branch then has a *literal* `Dec`, so
-- `⟨_⟩[_↦_]cl` computes without any further dispatch at the use site.
------------------------------------------------------------------------

cl-cancel : ∀ {Γ A B ρ} → (dec : Dec (Eternal A))
          → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
          → (H : (op : Op) → (ε : E) → Cl B op ε (Γ ᴱ))
          → (K : (op : Op) → (ε : E)
                   → Cl B op ε ((split-l x ++ᶜ split-r x) ᴱ))
          → ((¬et : ¬ Eternal A) → (op : Op) → (ε : E)
               → ⟨ no ¬et ⟩[ x ↦ W ]cl H op ε ≐ᶜ K op ε)
          → ((et : Eternal A) → (op : Op) → (ε : E)
               → ⟨ yes et ⟩[ x ↦ W ]cl H op ε ≐ᶜ K op ε)
          → (op : Op) → (ε : E)
          → ⟨ dec ⟩[ x ↦ W ]cl H op ε ≐ᶜ K op ε

cl-cancel (no ¬et) x W H K hne het op ε = hne ¬et op ε
cl-cancel (yes et) x W H K hne het op ε = het et op ε

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

    -- the two variables a clause of `op'` at `ε'` adds
    Dof : (op' : Op) → (ε' : E) → Ctx
    Dof op' ε' = [] ∷ type-of-gtype (param op')
                    ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')

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
                -- The clause premise, rebuilt from `hH`. `cl-cancel` supplies
                -- the dispatch, at `K` := `H` transported to this state; the
                -- outer step is then a `subst` fusion reconciled by `uip`.
                K : (op' : Op) → (ε' : E) → Cl B op' ε' (toCtx St'' ᴱ)
                K op' ε' = subst (Cl B op' ε') (toCtxᴱ-≡ St St'') (H op' ε')

                hH₂ : Clause-Prem B St''
                        (⟨ eternal? Ar ⟩[ Hd {Γ = toCtx St''} ↦ W' ]cl
                           (λ op' ε' →
                              C-rename (cong-∷-ren (cong-∷-ren
                                          (restrict-ren
                                            (cong-∷-ren (unbox-ren q₂)))))
                                (H₁' op' ε')))
                hH₂ {St₃} {op₃} {ε₄} V₀' bv W₃ pW₃ =
                  Comp-≐ᶜ
                    (sub-≐ᶜ (Tl-∷ Hd) (≐ᵛ-refl W₃)
                      (C-rename-cong
                        (cong-∷-ren (cong-∷-ren (ᴱ-ren (toCtx St₃)))) step))
                    (hH V₀' bv W₃ pW₃)
                  where
                    -- WHAT IS LEFT: the two branch facts.
                    --
                    -- In both, the clause reached is `H₁ op ε` renamed by
                    -- `cong-ren {D} (restrict-ren (cong-∷-ren sq) ∘ʳ ren-ᴱ-∷ Ar)`,
                    -- and `eH₁` links `H₁` back to `H`. Neither branch needs to
                    -- know what that renaming *is*: `cl-ren-≐` pins it by what it
                    -- does to the clause's own two variables, which is nothing.
                    --
                    --   * `hne`: source and target eternal parts are both `[]`,
                    --     so `cl-ren-eq-≐` makes the renaming a transport and the
                    --     transports fuse by `uip`;
                    --   * `het`: the target is `[] ∷ Ar`, so the renaming is
                    --     `≐ʳ cong-ren {D} (wk-ren ∘ʳ eq-ren _)` — again by
                    --     `cl-ren-≐`, both sides fixing `D` — and `sub-wk-C`
                    --     cancels the `wk-ren` against the substitution.
                    -- the composite the two renamings amount to, and the
                    -- transport it is: source and target eternal parts are both
                    -- `[]`, and `cl-ren-≐` pins it by `D`'s variables alone
                    Rᶜ : (op' : Op) → (ε' : E)
                       → Ren [] (toCtx St₁ ᴱ ++ᶜ Dof op' ε')
                              ((toCtx St'' ∷ Ar) ᴱ ++ᶜ Dof op' ε')
                    Rᶜ op' ε' =
                      cong-ren {Γ'' = Dof op' ε'}
                        (restrict-ren (cong-∷-ren (unbox-ren q₂)))
                      ∘ʳ cong-ren {Γ'' = Dof op' ε'}
                           (ren-ᴱ-∷′ {toCtx St₁ ⟨ ρₒ ⟩} {[]} Ar (eternal? Ar))

                    -- `Hᵣ` is the clause renamed by that composite
                    Hᵣ-≐ : (op' : Op) → (ε' : E)
                         → C-rename (cong-∷-ren (cong-∷-ren
                                       (restrict-ren (cong-∷-ren (unbox-ren q₂)))))
                             (H₁' op' ε')
                         ≐ᶜ C-rename (Rᶜ op' ε') (H₁ op' ε')
                    Hᵣ-≐ op' ε' =
                      ≐ᶜ-sym (C-rename-∘ _ _ (H₁ op' ε'))

                    -- and `H₁` is `H` transported (`eH₁`)
                    H₁-≐ : (op' : Op) → (ε' : E)
                         → H₁ op' ε'
                         ≡ subst (Cl B op' ε') (toCtxᴱ-≡ St St₁) (H op' ε')
                    H₁-≐ = eH₁

                    hne : (¬et : ¬ Eternal Ar) → (op' : Op) → (ε' : E)
                        → ⟨ no ¬et ⟩[ Hd {Γ = toCtx St''} ↦ W' ]cl
                            (λ op'' ε'' →
                               C-rename (cong-∷-ren (cong-∷-ren
                                           (restrict-ren
                                             (cong-∷-ren (unbox-ren q₂)))))
                                 (H₁' op'' ε''))
                            op' ε'
                        ≐ᶜ K op' ε'
                    hne ¬et op' ε' =
                      ≐ᶜ-trans
                        (substᶜ-≐′ (λ Γ₀ → Γ₀ ++ᶜ D)
                          eD
                          (≐ᶜ-trans (Hᵣ-≐ op' ε')
                            (≐ᶜ-trans
                              (C-rename-eq-≐ (cong (_++ᶜ D) e₀)
                                (cl-ren-≐ St₁ D
                                  (λ y →
                                     trans
                                       (trans
                                         (cong (var-tgt′
                                                 (cong-ren {Γ'' = D}
                                                   (restrict-ren
                                                     (cong-∷-ren (unbox-ren q₂)))))
                                               (cong-ren-tgt-r _ y))
                                         (cong-ren-tgt-r _ y))
                                       (sym (trans
                                         (eq-ren-tgt (cong (_++ᶜ D) e₀)
                                                     (∈-++ᶜʳ y))
                                         (cong (λ z → _ , z)
                                           (∈-++ᶜʳ-cast D e₀ y))))))
                                (H₁ op' ε'))
                              (≡→≐ᶜ (cong (subst (_⊢C⦂ CT) (cong (_++ᶜ D) e₀))
                                          (H₁-≐ op' ε'))))))
                        (≡→≐ᶜ collapse-ne)
                      where
                        D  = Dof op' ε'
                        CT = B ‼ (op-grade op' ·ₑ ε')

                        e₀ : toCtx St₁ ᴱ ≡ (toCtx St'' ∷ Ar) ᴱ
                        e₀ = trans (toCtxᴱ-[] St₁)
                               (sym (trans (ᴱ-∷-drop {toCtx St''} {Ar} ¬et)
                                           (toCtxᴱ-[] St'')))

                        eD : (toCtx St'' ∷ Ar) ᴱ ≡ toCtx St'' ᴱ
                        eD = ᴱ-drop-split {A = Ar} ¬et (Hd {Γ = toCtx St''})

                        collapse-ne :
                            subst (Cl B op' ε') eD
                              (subst (_⊢C⦂ CT) (cong (_++ᶜ D) e₀)
                                (subst (Cl B op' ε') (toCtxᴱ-≡ St St₁)
                                  (H op' ε')))
                          ≡ K op' ε'
                        collapse-ne =
                          trans
                            (cong (subst (Cl B op' ε') eD)
                              (sym (subst-++ᶜʳ D e₀
                                     (subst (Cl B op' ε') (toCtxᴱ-≡ St St₁)
                                       (H op' ε')))))
                            (subst-collapse-cl (toCtxᴱ-≡ St St₁) e₀ eD
                                               (toCtxᴱ-≡ St St'') (H op' ε'))

                    -- THE ETERNAL BRANCH, and what it needs.
                    --
                    -- Here `⟨ yes et ⟩[ Hd ↦ W' ]cl` substitutes
                    -- `eternal-val-restrict et W'` for the `Ar` variable of the
                    -- renamed clause, at the splitting
                    -- `sp = split-++ʳ (∈-ᴱ-split et Hd) D`.
                    --
                    -- The clause does not contain that variable: its own context
                    -- is `toCtx St₁ ᴱ`, i.e. `[]`, so every variable it has comes
                    -- from `D`. So the substitution is the identity, and
                    -- `sub-wk-C` is the tool — which means presenting the renamed
                    -- clause as `C-rename (cong-ren {D} (wk-ren {A = Ar})) M₀`
                    -- with `M₀` the transport of `H₁ op' ε'` to
                    -- `toCtx St'' ᴱ ++ᶜ D`. `cl-ren-≐` supplies that (both sides
                    -- fix `D`, and `ᴱ-∷-keep et` identifies the target
                    -- `(toCtx St'' ∷ Ar) ᴱ` with `toCtx St'' ᴱ ∷ Ar`).
                    --
                    -- Three further steps, all present but none short:
                    --
                    --   * push the substitution across that identification
                    --     (`sub-cast-C`);
                    --   * identify its variable with
                    --     `split→∈ (split-≡-++ᶜ {toCtx St'' ᴱ ∷ Ar} {D})`, which
                    --     `sub-wk-C` wants — `split-unique`/`split→∈-unique`,
                    --     since two splittings of the same context agree;
                    --   * fuse the leftover transports (`eOut`, `ᴱ-∷-keep et`,
                    --     `castOf`, `toCtxᴱ-≡`) by `uip`.
                    --
                    -- This is the shape of `sub-wk-handle-et` in `Environment`,
                    -- the longest single proof in the development.
                    het : (et : Eternal Ar) → (op' : Op) → (ε' : E)
                        → ⟨ yes et ⟩[ Hd {Γ = toCtx St''} ↦ W' ]cl
                            (λ op'' ε'' →
                               C-rename (cong-∷-ren (cong-∷-ren
                                           (restrict-ren
                                             (cong-∷-ren (unbox-ren q₂)))))
                                 (H₁' op'' ε''))
                            op' ε'
                        ≐ᶜ K op' ε'
                    het et op' ε' =
                      ≐ᶜ-trans
                        (substᶜ-≐ eOut
                          (sub-≐ᶜ (split→∈ sp) (≐ᵛ-refl Ws) factor))
                        (≐ᶜ-trans
                          (≡→≐ᶜ (cong (subst (_⊢C⦂ CT) eOut)
                                   (sub-cast-C′ eKD Mwk (split→∈ tp) (split→∈ sp)
                                                ey Wt Ws eW)))
                          (≐ᶜ-trans
                            (≡→≐ᶜ (subst-fuseᶜ eSub eOut
                                     (Mwk [ split→∈ tp ↦ Wt ]c)))
                            (≐ᶜ-trans
                              (≡→≐ᶜ (trans
                                (cong (λ z → subst (_⊢C⦂ CT) z
                                               (Mwk [ split→∈ tp ↦ Wt ]c)) uip)
                                (sym (castᶜ≡subst
                                       (castOf {toCtx St'' ᴱ} {Ar} D) _))))
                              (≐ᶜ-trans (sub-wk-C-cast D eG (H₁ op' ε') Wt)
                                        (≡→≐ᶜ collapse-et)))))
                      where
                        D  = Dof op' ε'
                        CT = B ‼ (op-grade op' ·ₑ ε')

                        -- the two splittings of the clause's context: the one
                        -- `⟨ yes et ⟩[_↦_]cl` uses, and the one `sub-wk-C` wants
                        sp = split-++ʳ (∈-ᴱ-split et (Hd {Γ = toCtx St''})) D
                        tp = split-≡-++ᶜ {toCtx St'' ᴱ ∷ Ar} {D}

                        -- `∈-ᴱ-split`'s own type identifies the two contexts —
                        -- no `eternal?` reduction needed
                        eKD = cong (_++ᶜ D)
                                (split-≡ (∈-ᴱ-split et (Hd {Γ = toCtx St''})))
                        eG  = cong (_++ᶜ D) (toCtxᴱ-≡ St₁ St'')

                        Mwk = C-rename (cong-ren {Γ'' = D} (wk-ren {A = Ar}))
                                (subst (_⊢C⦂ CT) eG (H₁ op' ε'))

                        ey = split→∈-unique eKD tp sp
                        eL = trans (split-l-cast eKD (split→∈ tp)) (cong split-l ey)

                        eSub = cong₂ _++ᶜ_ eL
                                 (trans (split-r-cast eKD (split→∈ tp))
                                        (cong split-r ey))

                        Ws = subst (_⊢V⦂ Ar) (sym (split→∈-split-l sp))
                               (eternal-val-restrict et W')
                        Wt = subst (_⊢V⦂ Ar) (sym eL) Ws
                        eW = subst-subst-sym′ eL Ws

                        eOut =
                          trans (cong₂ _++ᶜ_ (split→∈-split-l sp)
                                             (split→∈-split-r sp))
                            (trans (sym (++ᶜ-assoc ((toCtx St'') ᴱ) ([] ᴱ) D))
                                   (cong (_++ᶜ D)
                                     (sym (ᴱ-++ᶜ (toCtx St'') []))))

                        -- the renaming factors through `wk-ren`: `cl-ren-≐`
                        -- again, both sides fixing `D`'s two variables
                        factor : C-rename (cong-∷-ren (cong-∷-ren
                                             (restrict-ren
                                               (cong-∷-ren (unbox-ren q₂)))))
                                   (H₁' op' ε')
                               ≐ᶜ subst (_⊢C⦂ CT) eKD Mwk
                        factor =
                          ≐ᶜ-trans (Hᵣ-≐ op' ε')
                            (≐ᶜ-trans
                              (C-rename-≐ (cl-ren-≐ St₁ D pointwise) (H₁ op' ε'))
                              (≐ᶜ-trans
                                (C-rename-∘ (eq-ren eKD)
                                  (cong-ren {Γ'' = D} (wk-ren {A = Ar})
                                     ∘ʳ eq-ren eG)
                                  (H₁ op' ε'))
                                (≐ᶜ-trans
                                  (C-rename-cong (eq-ren eKD)
                                    (≐ᶜ-trans
                                      (C-rename-∘
                                        (cong-ren {Γ'' = D} (wk-ren {A = Ar}))
                                        (eq-ren eG) (H₁ op' ε'))
                                      (C-rename-cong
                                        (cong-ren {Γ'' = D} (wk-ren {A = Ar}))
                                        (C-rename-eq-≐ eG ≐ʳ-refl (H₁ op' ε')))))
                                  (C-rename-eq-≐ eKD ≐ʳ-refl Mwk))))
                          where
                            pointwise : ∀ {A₀ ρ₀} → (y : A₀ ∈[ ρ₀ ] D) → _
                            pointwise y =
                              trans
                                (trans
                                  (cong (var-tgt′
                                          (cong-ren {Γ'' = D}
                                            (restrict-ren
                                              (cong-∷-ren (unbox-ren q₂)))))
                                        (cong-ren-tgt-r _ y))
                                  (cong-ren-tgt-r _ y))
                                (sym (trans
                                  (cong (λ z → var-tgt′ (eq-ren eKD)
                                                 (var-tgt′ (cong-ren {Γ'' = D}
                                                   (wk-ren {A = Ar})) z))
                                        (trans (eq-ren-tgt eG (∈-++ᶜʳ y))
                                          (cong (λ z → _ , z)
                                            (∈-++ᶜʳ-cast D (toCtxᴱ-≡ St₁ St'') y))))
                                  (trans (cong (var-tgt′ (eq-ren eKD))
                                           (cong-ren-tgt-r _ y))
                                    (trans (eq-ren-tgt eKD (∈-++ᶜʳ y))
                                      (cong (λ z → _ , z)
                                        (∈-++ᶜʳ-cast D _ y))))))

                        collapse-et :
                            subst (_⊢C⦂ CT) eG (H₁ op' ε') ≡ K op' ε'
                        collapse-et =
                          trans
                            (cong (λ z → subst (_⊢C⦂ CT) eG z) (eH₁ op' ε'))
                            (trans
                              (sym (subst-++ᶜʳ D (toCtxᴱ-≡ St₁ St'')
                                     (subst (Cl B op' ε') (toCtxᴱ-≡ St St₁)
                                       (H op' ε'))))
                              (trans
                                (subst-fuse-cl (toCtxᴱ-≡ St St₁)
                                               (toCtxᴱ-≡ St₁ St'') (H op' ε'))
                                (cong (λ z → subst (Cl B op' ε') z (H op' ε'))
                                      uip)))

                    -- the two transports compose to the one `hH` supplies
                    fuse : subst (Cl B op₃ ε₄) (toCtxᴱ-≡ St'' St₃) (K op₃ ε₄)
                         ≡ subst (Cl B op₃ ε₄) (toCtxᴱ-≡ St St₃) (H op₃ ε₄)
                    fuse =
                      trans (subst-fuse-cl (toCtxᴱ-≡ St St'') (toCtxᴱ-≡ St'' St₃)
                                           (H op₃ ε₄))
                            (cong (λ z → subst (Cl B op₃ ε₄) z (H op₃ ε₄)) uip)

                    step : subst (Cl B op₃ ε₄) (toCtxᴱ-≡ St St₃) (H op₃ ε₄)
                         ≐ᶜ subst (Cl B op₃ ε₄) (toCtxᴱ-≡ St'' St₃)
                              (⟨ eternal? Ar ⟩[ Hd {Γ = toCtx St''} ↦ W' ]cl
                                 (λ op' ε' →
                                    C-rename (cong-∷-ren (cong-∷-ren
                                                (restrict-ren
                                                  (cong-∷-ren (unbox-ren q₂)))))
                                      (H₁' op' ε'))
                                 op₃ ε₄)
                    step =
                      ≐ᶜ-trans (≡→≐ᶜ (sym fuse))
                        (substᶜ-≐′
                          (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op₃)
                                     ∷ [ mapᵉ (op-grade op₃) ]
                                         (type-of-gtype (arity op₃) ⇒ B ‼ ε₄))
                          (toCtxᴱ-≡ St'' St₃)
                          (≐ᶜ-sym
                            (cl-cancel (eternal? Ar) (Hd {Γ = toCtx St''}) W' _ K
                                       hne het op₃ ε₄)))


------------------------------------------------------------------------
-- THE FIRED CLAUSE IS THE CLAUSE ENVIRONMENT'S ACTION
--
-- `env-Hˢ-clause` at the empty suffix. What is left to reconcile is where each
-- side puts the two extra binders: `Fired` renames the clause into `toCtx St₁`
-- and then substitutes the parameter at `Tl-∷ Hd`, while `liftᵉ` (at the empty
-- suffix, two `refl` casts) and `_∷ᵉ_` (whose splitting's variable *is*
-- `Tl-∷ Hd`) produce exactly that. The two weakenings differ — `ᴱ-ren
-- (toCtx St₁)` against `clause-ren St₁ []` — but both leave `toCtx St ᴱ`, a
-- context with no variables, so `≐ʳ` identifies them.
------------------------------------------------------------------------

-- A state's eternal part has no variables, so any two renamings out of it act
-- alike — `∅-ren-≐` one `toCtxᴱ-[]` away.

toCtxᴱ-ren-≐ : ∀ {Γ'} → (St : 𝕊 []) → (r r' : Ren [] (toCtx St ᴱ) Γ')
             → r ≐ʳ r'
toCtxᴱ-ren-≐ St r r' =
  mk≐ʳ (λ x → ⊥-elim (not-in-empty-ctx
                        (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (toCtxᴱ-[] St) x)))

-- A clause's transport is absorbed into the renaming that follows it.

subst-Cl-ren : ∀ {Γ₀ Γ₀' Γ₁ B} {op : Op} {ε : E} → (e : Γ₀ ≡ Γ₀')
             → (r : Ren [] Γ₀' Γ₁) → (r' : Ren [] Γ₀ Γ₁)
             → (r ∘ʳ eq-ren e) ≐ʳ r' → (Y : Cl B op ε Γ₀)
             → C-rename (cong-∷-ren (cong-∷-ren r)) (subst (Cl B op ε) e Y)
             ≐ᶜ C-rename (cong-∷-ren (cong-∷-ren r')) Y
subst-Cl-ren refl r r' h Y =
  C-rename-≐
    (cong-∷-ren-≐ (cong-∷-ren-≐ (≐ʳ-trans (≐ʳ-sym (∘ʳ-identityʳ-≐ r)) h))) Y

env-Hˢ-fired : ∀ {St Γ B} → (γ : Env St Γ) → (St₁ : 𝕊 [])
             → (H : Fam B (Γ ᴱ)) → {op : Op} → {ε : E}
             → (V₀ : Boxed B op ε St₁)
             → (W : toCtx St₁ ⊢V⦂ type-of-gtype (param op))
             → Fired St op ε (env-Hˢ γ [] H) St₁ V₀ W
             ≐ᶜ env-C (liftᵉ V₀ (env-clause γ St₁ ∷ᵉ W)) (H op ε)

env-Hˢ-fired {St} {Γ} {B} γ St₁ H {op} {ε} V₀ W =
  sub-≐ᶜ (Tl-∷ Hd) (≐ᵛ-refl W)
    (≐ᶜ-trans
      (subst-Cl-ren (toCtxᴱ-≡ St St₁) (ᴱ-ren (toCtx St₁))
                    (clause-ren St₁ [] ∘ʳ eq-ren (toCtxᴱ-++ᶜ St []))
                    (toCtxᴱ-ren-≐ St _ _)
                    (env-Hˢ γ [] H op ε))
      (env-Hˢ-clause γ St₁ [] H op ε))
