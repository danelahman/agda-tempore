------------------------------------------------------------------------
-- The clause action against the clause environment.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (yes; no; ¬_; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Environment.Clauses (Spec : LanguageSpec) where

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

open import OperationalSemantics.Adequacy.Reducibility   Spec
open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import Syntax.Substitutions.Restrict  Spec
open import Syntax.Substitutions.At        Spec
open import Syntax.Substitutions.Clauses   Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec
open import OperationalSemantics.Adequacy.Environment.Core Spec
open import OperationalSemantics.Adequacy.Environment.Action Spec
open import OperationalSemantics.Adequacy.Environment.Variables Spec

------------------------------------------------------------------------
-- THE CLAUSE ACTION AGAINST THE CLAUSE ENVIRONMENT, PROVED
--
-- The factorisation: `env-Hˢ-ᴱ` is the state-free core — the clause
-- action *is* the eternal-restriction action `env-eternal-C ∘ env-ᴱ`, up
-- to transport (the state contributes nothing to a restricted context) —
-- and the `St₁`-weakening is one generic conjugation step on top.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- UTILITIES
------------------------------------------------------------------------

-- A lock-freeness witness is unique.

Lock-free-irr : ∀ {Δ} → (p q : Lock-free Δ) → p ≡ q
Lock-free-irr lf-[]     lf-[]      = refl
Lock-free-irr (lf-∷ p)  (lf-∷ q)   = cong lf-∷ (Lock-free-irr p q)

-- A renaming out of a provably empty context acts like any transport.

empty-src-≐ʳ : ∀ {Γ₀ Γ₁} → (e₀ : Γ₀ ≡ []) → (r : Ren [] Γ₁ Γ₀)
            → (e : Γ₀ ≡ Γ₁) → r ≐ʳ eq-ren e
empty-src-≐ʳ e₀ r e =
  mk≐ʳ (λ x → ⊥-elim (not-in-empty-ctx
                       (subst (λ Γ₂ → _ ∈[ _ ] Γ₂) e₀ x)))

-- The eternal-values action at a provably empty prefix is a transport.

env-eternal-C-empty : ∀ {Δ₀ Γc C} → (e : Δ₀ ≡ [])
                    → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                    → (M : (Δ₀ ++ᶜ Γc) ⊢C⦂ C)
                    → env-eternal-C lf η M
                    ≡ castᶜ (trans (cong (_++ᶜ Γc) e) (++ᶜ-identityˡ {Γc})) M
env-eternal-C-empty {Γc = Γc} e lf-[] η M =
  castᶜ-irr (++ᶜ-identityˡ {Γc}) (trans (cong (_++ᶜ Γc) e) (++ᶜ-identityˡ {Γc})) M
env-eternal-C-empty e (lf-∷ lf) η M with e
... | ()

-- The eternal-values action respects a transport of its suffix.

env-eternal-C-suffix : ∀ {Δ₀ Γc Γc' C} → (e : Γc ≡ Γc')
                     → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                     → (M : (Δ₀ ++ᶜ Γc) ⊢C⦂ C)
                     → castᶜ e (env-eternal-C lf η M)
                     ≡ env-eternal-C lf η (castᶜ (cong (Δ₀ ++ᶜ_) e) M)
env-eternal-C-suffix refl lf η M = refl

-- Fusing a conjugation whose core is itself an `eq-ren`.

conj-eq-≐ʳ : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'}
          → {R : Ren [] Γ₂' Γ₁} → (e : Γ₁ ≡ Γ₁') → (e₀ : Γ₁' ≡ Γ₂)
          → (e' : Γ₂ ≡ Γ₂')
          → R ≐ʳconj⟨ e , eq-ren e₀ , e' ⟩
          → R ≐ʳ eq-ren (trans e (trans e₀ e'))
conj-eq-≐ʳ e e₀ e' h =
  ≐ʳ-trans h
    (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-∘-≐ʳ e₀ e'))
              (≐ʳ-trans (eq-ren-∘-≐ʳ e (trans e₀ e'))
                        (eq-ren-≐ʳ _ _)))

-- A loop of four casts is the identity.

cast-loop₄ : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃)
           → (e₃ : Γ₃ ≡ Γ₄) → (e₄ : Γ₄ ≡ Γ₁) → (M : Γ₁ ⊢C⦂ C)
           → castᶜ e₄ (castᶜ e₃ (castᶜ e₂ (castᶜ e₁ M))) ≡ M
cast-loop₄ refl refl refl e₄ M = castᶜ-irr e₄ refl M

-- A loop of two casts is the identity.

cast-loop₂ : ∀ {Γ₁ Γ₂ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₁) → (M : Γ₁ ⊢C⦂ C)
           → castᶜ e₂ (castᶜ e₁ M) ≡ M
cast-loop₂ refl e₂ M = castᶜ-irr e₂ refl M

-- A chain of two casts is one transport.

cast-chain₂ : ∀ {Γ₁ Γ₂ Γ₃ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃)
            → (M : Γ₁ ⊢C⦂ C)
            → castᶜ e₂ (castᶜ e₁ M) ≡ subst (_⊢C⦂ C) (trans e₁ e₂) M
cast-chain₂ refl refl M = refl

-- A chain of four casts is one transport.

cast-chain₄ : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃)
            → (e₃ : Γ₃ ≡ Γ₄) → (e₄ : Γ₄ ≡ Γ₅) → (M : Γ₁ ⊢C⦂ C)
            → castᶜ e₄ (castᶜ e₃ (castᶜ e₂ (castᶜ e₁ M)))
            ≡ subst (_⊢C⦂ C) (trans e₁ (trans e₂ (trans e₃ e₄))) M
cast-chain₄ refl refl refl refl M = refl

------------------------------------------------------------------------
-- THE STATE-FREE CORE
--
-- `env-Hˢ γ Δ K` is `env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)` of the
-- clause, up to transport: the state's part of the restricted context is
-- empty, so every state-indexed zone of `env-Hˢ` contributes only a
-- transport, and the value-substituting zones match `env-eternal-C`'s
-- own steps.
------------------------------------------------------------------------

-- The recursion's suffix context.

D~ : Ctx → VType → Op → E → Ctx
D~ Δ B op ε =
  Δ ᴱ ∷ type-of-gtype (param op)
      ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε)

eStar : ∀ {B} → (St : 𝕊 []) → (Δ : Ctx) → (op : Op) → (ε : E)
      → ([] ++ᶜ D~ Δ B op ε)
      ≡ ((toCtx St ++ᶜ Δ) ᴱ ∷ type-of-gtype (param op)
           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε))
eStar {B} St Δ op ε =
  trans (++ᶜ-identityˡ {D~ Δ B op ε})
        (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (toCtxᴱ-++ᶜ St Δ)))

-- The eternal-values action respects equality (the computation counterpart of
-- `env-eternal-V-≡`).

env-eternal-C-≡ : ∀ {Δ Γ C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → {M M' : (Δ ++ᶜ Γ) ⊢C⦂ C} → M ≡ M'
                → env-eternal-C lf η M ≡ env-eternal-C lf η M'
env-eternal-C-≡ lf η = cong (env-eternal-C lf η)

------------------------------------------------------------------------
-- ONE SUBSTITUTION PAST THE ETERNAL CHAIN
--
-- `env-eternal-C` peels its prefix from the *right*, while `env-Hˢ`
-- reaches a zone's substitution only after the zones to its left have
-- run. So the two open cases both need to move one substitution past the
-- whole chain. Each step of the chain substitutes the entry immediately
-- to the left of the one being moved — `Δ ∷ B` against `([] ∷ A) ++ᶜ Θ'`
-- *is* `(Δ ∷ B ∷ A) ++ᶜ Θ'` — so each step is exactly one `sub-swap-C`.
--
-- Note `env-eternal-C (lf-∷ lf) η` *is* `env-eternal-C lf η' ∘ sub-atᶜ`,
-- definitionally: the two agree on the nose, which is what makes the
-- induction below readable.
------------------------------------------------------------------------

env-eternal-C-swap : ∀ {Δ₀ A C} → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                   → (Θ' : Ctx) → (V : [] ⊢V⦂ A)
                   → (M : ((Δ₀ ∷ A) ++ᶜ Θ') ⊢C⦂ C)
                   → castᶜ (++ᶜ-identityˡ {Θ'})
                       (sub-atᶜ {[]} {A} Θ'
                         (env-eternal-C lf η
                           (castᶜ (++ᶜ-assoc Δ₀ ([] ∷ A) Θ') M)) V)
                   ≡ env-eternal-C lf η
                        (sub-atᶜ {Δ₀} {A} Θ' M (V-rename (empty-ren lf) V))

env-eternal-C-swap {Δ₀} {A} {C} lf-[] η Θ' V M =
  trans
    (castᶜ-≡ (++ᶜ-identityˡ {Θ'})
      (sub-atᶜ-≡ {[]} {A} Θ' V
        ((cast-loop₂ (++ᶜ-assoc [] ([] ∷ A) Θ') (++ᶜ-identityˡ) M))))
    (castᶜ-≡ (++ᶜ-identityˡ {Θ'})
      (sub-atᶜ-≡ᵥ {[]} {A} Θ' M (sym (V-rename-id-≡ ≐ʳ-refl V))))

env-eternal-C-swap {Δ ∷ B} {A} {C} (lf-∷ lf) η Θ' V M =
  trans
    ((cong (λ z → castᶜ (++ᶜ-identityˡ {Θ'})
                         (sub-atᶜ {[]} {A} Θ' (env-eternal-C lf η' z) V))
                (sym (cast-loop₂ (sym (++ᶜ-assoc Δ ([] ∷ A) Θ'))
                                 (++ᶜ-assoc Δ ([] ∷ A) Θ')
                                 (sub-atᶜ {Δ} {B} (([] ∷ A) ++ᶜ Θ')
                                    (castᶜ (++ᶜ-assoc (Δ ∷ B) ([] ∷ A) Θ') M)
                                    W₁)))))
    (trans (env-eternal-C-swap lf η' Θ' V (inner₀ᶜ Θ' M W₁))
      (env-eternal-C-≡ lf η'
        (trans (sym (sub-swap-C Θ' M W₂ W₁))
                  (sub-atᶜ-≡ {Δ} {B} Θ' W₁
                    (sub-atᶜ-≡ᵥ {Δ ∷ B} {A} Θ' M
                      (sym (V-rename-∘ (empty-ren lf)
                                          (wk-ren {A = B}) V)))))))
  where
    η' : ClosedVals Δ
    η' x = η (Tl-∷ x)

    W₁ = V-rename (empty-ren lf) (η Hd)
    W₂ = V-rename (empty-ren lf) V

------------------------------------------------------------------------
-- THE CHAIN AT A CONCATENATED PREFIX
--
-- At `eternalˡ` the mismatch is block for block: `env-Hˢ` runs the
-- eternal zone's substitutions before the zones to its left, while
-- `env-eternal-C` at `Δ₁ ++ᶜ Δ₂` peels `Δ₂` first. Splitting the
-- concatenated chain one entry at a time reduces that to
-- `env-eternal-C-swap`: each entry of `Δ₂` moves past the whole of `Δ₁`,
-- and the entry left over is adjacent to the chain it crosses.
------------------------------------------------------------------------

-- The values of a concatenated prefix. By recursion on `Δ₂`'s
-- lock-freeness, so that peeling an entry is definitional.

++ᶜᵛ : ∀ {Δ₁ Δ₂} → Lock-free Δ₂ → ClosedVals Δ₁ → ClosedVals Δ₂
     → ClosedVals (Δ₁ ++ᶜ Δ₂)
++ᶜᵛ lf-[]      η₁ η₂ x        = η₁ x
++ᶜᵛ (lf-∷ lf₂) η₁ η₂ Hd       = η₂ Hd
++ᶜᵛ (lf-∷ lf₂) η₁ η₂ (Tl-∷ x) = ++ᶜᵛ lf₂ η₁ (λ y → η₂ (Tl-∷ y)) x

-- and the same values, presented against the splitting `env-ᴱ` dispatches
-- on rather than by recursion

splitVal : ∀ {Δ₁ Δ₂ A ρ} → ClosedVals Δ₁ → ClosedVals Δ₂
         → (Σ[ ρ' ∈ R ] A ∈[ ρ' ] Δ₁) ⊎ (A ∈[ ρ ] Δ₂) → [] ⊢V⦂ A
splitVal η₁ η₂ (inj₁ (_ , y)) = η₁ y
splitVal η₁ η₂ (inj₂ y)       = η₂ y

++ᶜᵛ-split : ∀ {Δ₁ Δ₂ A ρ} → (lf₂ : Lock-free Δ₂)
           → (η₁ : ClosedVals Δ₁) → (η₂ : ClosedVals Δ₂)
           → (y : A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂))
           → ++ᶜᵛ lf₂ η₁ η₂ y ≡ splitVal η₁ η₂ (∈-++ᶜ-split Δ₁ Δ₂ y)
++ᶜᵛ-split lf-[]      η₁ η₂ y  = refl
++ᶜᵛ-split (lf-∷ lf₂) η₁ η₂ Hd = refl
++ᶜᵛ-split {Δ₁} {Δ₂ ∷ B} (lf-∷ lf₂) η₁ η₂ (Tl-∷ y)
  with ∈-++ᶜ-split Δ₁ Δ₂ y | ++ᶜᵛ-split lf₂ η₁ (λ z → η₂ (Tl-∷ z)) y
... | inj₁ p | q = q
... | inj₂ z | q = q

-- The chain uses its values only pointwise.

env-eternal-C-η : ∀ {Δ Θ C} → (lf : Lock-free Δ) → {η η' : ClosedVals Δ}
                → (∀ {A ρ} → (x : A ∈[ ρ ] Δ) → η x ≡ η' x)
                → (M : (Δ ++ᶜ Θ) ⊢C⦂ C)
                → env-eternal-C lf η M ≡ env-eternal-C lf η' M
env-eternal-C-η lf-[] h M = refl
env-eternal-C-η {Δ ∷ B} {Θ} (lf-∷ lf) {η} {η'} h M =
  trans (cong (λ z → env-eternal-C lf (λ x → η (Tl-∷ x))
                       (sub-atᶜ {Δ} {B} Θ M (V-rename (empty-ren lf) z)))
              (h Hd))
        (env-eternal-C-η lf (λ x → h (Tl-∷ x))
          (sub-atᶜ {Δ} {B} Θ M (V-rename (empty-ren lf) (η' Hd))))

-- and it respects a transport of its prefix.

env-eternal-C-pre : ∀ {Δ Δ' Θ C} → (e : Δ ≡ Δ')
                  → (lf : Lock-free Δ) → (lf' : Lock-free Δ')
                  → (η : ClosedVals Δ) → (η' : ClosedVals Δ')
                  → (∀ {A ρ} → (x : A ∈[ ρ ] Δ)
                       → η x ≡ η' (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x))
                  → (M : (Δ ++ᶜ Θ) ⊢C⦂ C)
                  → env-eternal-C lf η M
                  ≡ env-eternal-C lf' η' (castᶜ (cong (_++ᶜ Θ) e) M)
env-eternal-C-pre refl lf lf' η η' h M
  rewrite Lock-free-irr lf lf' = env-eternal-C-η lf' h M

-- The decomposition itself.

env-eternal-C-++ : ∀ {Δ₁ Δ₂ Θ C} → (lf₁ : Lock-free Δ₁) → (lf₂ : Lock-free Δ₂)
                 → (lf₁₂ : Lock-free (Δ₁ ++ᶜ Δ₂))
                 → (η₁ : ClosedVals Δ₁) → (η₂ : ClosedVals Δ₂)
                 → (M : ((Δ₁ ++ᶜ Δ₂) ++ᶜ Θ) ⊢C⦂ C)
                 → env-eternal-C lf₁₂ (++ᶜᵛ lf₂ η₁ η₂) M
                 ≡ env-eternal-C lf₂ η₂
                      (env-eternal-C lf₁ η₁ (castᶜ (++ᶜ-assoc Δ₁ Δ₂ Θ) M))

env-eternal-C-++ {Δ₁} {[]} {Θ} lf₁ lf-[] lf₁₂ η₁ η₂ M =
  trans ((env-eternal-C-pre refl lf₁₂ lf₁ _ η₁ (λ x → refl) M))
    ((sym
      (trans (env-eternal-C-suffix (++ᶜ-identityˡ {Θ}) lf₁ η₁ _)
             (cong (env-eternal-C lf₁ η₁)
                   (cast-loop₂ (++ᶜ-assoc Δ₁ [] Θ)
                               (cong (Δ₁ ++ᶜ_) (++ᶜ-identityˡ {Θ})) M)))))

env-eternal-C-++ {Δ₁} {Δ₂ ∷ B} {Θ} {C} lf₁ (lf-∷ lf₂) (lf-∷ lf₁₂) η₁ η₂ M =
  trans (sym (env-eternal-C-swap lf₁₂ (++ᶜᵛ lf₂ η₁ η₂') Θ (η₂ Hd) M))
    (trans
      (castᶜ-≡ (++ᶜ-identityˡ {Θ})
        (sub-atᶜ-≡ {[]} {B} Θ (η₂ Hd)
          (trans (env-eternal-C-++ lf₁ lf₂ lf₁₂ η₁ η₂' (castᶜ c₂ M))
                    (env-eternal-C-≡ lf₂ η₂' (qeq)))))
      (env-eternal-C-swap lf₂ η₂' Θ (η₂ Hd) M̃))
  where
    η₂' : ClosedVals Δ₂
    η₂' x = η₂ (Tl-∷ x)

    c₂ = ++ᶜ-assoc (Δ₁ ++ᶜ Δ₂) ([] ∷ B) Θ
    c₁ = ++ᶜ-assoc Δ₁ Δ₂ (([] ∷ B) ++ᶜ Θ)
    c₃ = ++ᶜ-assoc Δ₁ (Δ₂ ∷ B) Θ

    M̃ = env-eternal-C lf₁ η₁ (castᶜ c₃ M)

    qeq : env-eternal-C lf₁ η₁ (castᶜ c₁ (castᶜ c₂ M))
        ≡ castᶜ (++ᶜ-assoc Δ₂ ([] ∷ B) Θ) M̃
    qeq =
      trans
        (cong (env-eternal-C lf₁ η₁)
          (trans (cast-chain₂ c₂ c₁ M)
            (trans (cong (λ p → subst (_⊢C⦂ C) p M) uip)
                   (sym (cast-chain₂ c₃
                          (cong (Δ₁ ++ᶜ_) (++ᶜ-assoc Δ₂ ([] ∷ B) Θ)) M)))))
        (sym (env-eternal-C-suffix (++ᶜ-assoc Δ₂ ([] ∷ B) Θ) lf₁ η₁
                                   (castᶜ c₃ M)))

------------------------------------------------------------------------
-- THE ETERNAL ZONE'S CLAUSE ACTION IS A CHAIN
--
-- `env-eternal-H` peels `Δ₀` itself; `env-eternal-C` peels the *restricted*
-- `Δ₀ ᴱ`. At a non-eternal entry the first is a transport and the second
-- has nothing to peel; at an eternal one both substitute the restricted
-- value, and in the same order — so, unlike `eternalˡ` as a whole, this
-- needs no swap, only the per-entry dispatch.
------------------------------------------------------------------------

-- Restricting a closed value is the identity: it has no variables to move.

restrict-closed : ∀ {A} → (et : Eternal A) → (V : [] ⊢V⦂ A)
                → eternal-val-restrict et V ≡ V
restrict-closed (Baseₑ b p)    (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed (Baseₑ b p)    (const c)   = refl
restrict-closed Unitₑ          (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed Unitₑ          ⋆           = refl
restrict-closed Emptyₑ         (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed (et₁ |×|ₑ et₂) (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  cong₂ (λ U₁ U₂ → ⦉ U₁ , U₂ ⦊)
        (restrict-closed et₁ V₁) (restrict-closed et₂ V₂)

-- An eternal zone's values, on the context the chain peels.

ηᴱ : ∀ {Δ₀} → ClosedVals Δ₀ → ClosedVals (Δ₀ ᴱ)
ηᴱ {Δ₀} η y = η (proj₂ (∈-ᴱ⁻ Δ₀ y))

-- The clause context, split at the zone's own boundary.

eH : (Δ₀ Γc : Ctx) → (B : VType) → (op : Op) → (ε : E)
   → ((Δ₀ ++ᶜ Γc) ᴱ ++ᶜ Dcl B op ε)
   ≡ (Δ₀ ᴱ ++ᶜ (Γc ᴱ ++ᶜ Dcl B op ε))
eH Δ₀ Γc B op ε =
  trans (cong (_++ᶜ Dcl B op ε) (ᴱ-++ᶜ Δ₀ Γc))
        (++ᶜ-assoc (Δ₀ ᴱ) (Γc ᴱ) (Dcl B op ε))

-- As `env-Hˢ-ᴱ-∷`, except that here the decision can be taken *before*
-- the statement is made: every occurrence of `eternal? B₀` sits under one
-- of the rollout's `Dec`-taking forms, so the entry is stated at `d` and
-- matched directly — no `rewrite`, hence no with-abstraction to reorder.

env-eternal-H-C-∷ : ∀ {B₀ Δ Γc B} → (lf : Lock-free Δ)
                  → (η : ClosedVals (Δ ∷ B₀))
                  → (K : Fam B (((Δ ∷ B₀) ++ᶜ Γc) ᴱ)) → (op : Op) → (ε : E)
                  → (d : Dec (Eternal B₀))
                  → (e₁ : (((Δ ∷ B₀) ++ᶜ Γc) ᴱ ++ᶜ Dcl B op ε)
                        ≡ (ᴱ-∷ (Δ ᴱ) B₀ d ++ᶜ (Γc ᴱ ++ᶜ Dcl B op ε)))
                  → (ih : (K₀ : Fam B ((Δ ++ᶜ Γc) ᴱ))
                        → env-eternal-H {_} {Γc} lf (λ x → η (Tl-∷ x)) K₀ op ε
                        ≡ env-eternal-C {_} {Γc ᴱ ++ᶜ Dcl B op ε}
                             (ᴱ-lock-free Δ) (ηᴱ (λ x → η (Tl-∷ x)))
                             (castᶜ (eH Δ Γc B op ε) (K₀ op ε)))
                  → env-eternal-H {_} {Γc} lf (λ x → η (Tl-∷ x))
                       (sub-atᴴ Γc K (V-rename (empty-ren lf) (η Hd))) op ε
                  ≡ env-eternal-C {_} {Γc ᴱ ++ᶜ Dcl B op ε}
                       (ᴱ-lock-free-∷ Δ B₀ d)
                       (λ y → η (proj₂ (∈-ᴱ⁻-∷ Δ B₀ d y)))
                       (castᶜ e₁ (K op ε))

env-eternal-H-C : ∀ {Δ₀ Γc B} → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                → (K : Fam B ((Δ₀ ++ᶜ Γc) ᴱ)) → (op : Op) → (ε : E)
                → env-eternal-H {_} {Γc} lf η K op ε
                ≡ env-eternal-C {_} {Γc ᴱ ++ᶜ Dcl B op ε}
                     (ᴱ-lock-free Δ₀) (ηᴱ η)
                     (castᶜ (eH Δ₀ Γc B op ε) (K op ε))

env-eternal-H-C {[]} {Γc} {B} lf-[] η K op ε =
  sym (    (trans (cast-chain₂ (eH [] Γc B op ε)
                        (++ᶜ-identityˡ {Γc ᴱ ++ᶜ Dcl B op ε}) (K op ε))
      (trans (cong (λ p → subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) p (K op ε)) uip)
             (sym (castᶜ≡subst
                     (cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                                     ∷ [ mapᵉ (op-grade op) ]
                                         (type-of-gtype (arity op) ⇒ B ‼ ε))
                           (++ᶜ-identityˡ {Γc}))
                     (K op ε))))))

env-eternal-H-C {Δ ∷ B₀} {Γc} {B} (lf-∷ lf) η K op ε =
  env-eternal-H-C-∷ lf η K op ε (eternal? B₀) (eH (Δ ∷ B₀) Γc B op ε)
    (λ K₀ → env-eternal-H-C lf (λ x → η (Tl-∷ x)) K₀ op ε)

-- at a non-eternal entry neither side peels: the clause substitution is a
-- transport and the entry is absent from the restricted prefix

env-eternal-H-C-∷ {B₀} {Δ} {Γc} {B} lf η K op ε (no ¬et) e₁ ih =
  trans (ih K₄) ((cong (env-eternal-C (ᴱ-lock-free Δ) (ηᴱ η')) inner))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε

    η' : ClosedVals Δ
    η' x = η (Tl-∷ x)

    W₀ = V-rename (empty-ren lf) (η Hd)

    K₄ : Fam B ((Δ ++ᶜ Γc) ᴱ)
    K₄ = sub-atᴴ Γc K W₀

    dropM = ᴱ-drop-split ¬et (split-≡-++ᶜ {Δ ∷ B₀} {Γc})

    inner : castᶜ (eH Δ Γc B op ε) (K₄ op ε) ≡ castᶜ e₁ (K op ε)
    inner =
      trans (cong (castᶜ (eH Δ Γc B op ε))
               (trans (cl-ne-≡ ¬et (split-≡-++ᶜ {Δ ∷ B₀} {Γc}) W₀ K op ε)
                      (subst-++ᶜʳ Dc dropM (K op ε))))
        (trans (castᶜ≡subst (eH Δ Γc B op ε) _)
          (trans (subst-fuseᶜ (cong (_++ᶜ Dc) dropM)
                              (eH Δ Γc B op ε) (K op ε))
            (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
                   (sym (castᶜ≡subst e₁ (K op ε))))))

-- at an eternal one both sides substitute the restricted value, and both
-- do it first, so `cl-yes` and `sub-at-≡` align them where they stand

env-eternal-H-C-∷ {B₀} {Δ} {Γc} {B} lf η K op ε (yes et) e₁ ih =
  trans (ih K₄)
    (env-eternal-C-≡ (ᴱ-lock-free Δ) (ηᴱ η')
      (isSub-≡ isL (isSub-refl S₂) (sym swapStep)))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε
    Θᴱ = Γc ᴱ ++ᶜ Dc

    η' : ClosedVals Δ
    η' x = η (Tl-∷ x)

    W₀ = V-rename (empty-ren lf) (η Hd)
    s  = split-≡-++ᶜ {Δ ∷ B₀} {Γc}

    K₄ : Fam B ((Δ ++ᶜ Γc) ᴱ)
    K₄ = sub-atᴴ Γc K W₀

    V₂ = V-rename (empty-ren (ᴱ-lock-free Δ)) (η Hd)

    eclx = eCl et s B op ε

    X₁ = subst (_⊢C⦂ CT) eclx (K op ε)
    X₂ = castᶜ e₁ (K op ε)

    -- both are transports of the same clause; the splitting's halves are `Δ`
    -- and `Γc` as given, so the two sit at the same context
    mid : X₂ ≡ X₁
    mid =
      trans (castᶜ≡subst e₁ (K op ε))
            (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)

    eVal : eternal-val-restrict et W₀ ≡ V₂
    eVal =
      trans (eternal-val-restrict-ren et (empty-ren lf) (η Hd))
        (trans
          ((cong (V-rename (restrict-ren (empty-ren lf)))
                      (restrict-closed et (η Hd))))
          (V-rename-≡ (∅-ren-≐ʳ (restrict-ren (empty-ren lf))
                                   (empty-ren (ᴱ-lock-free Δ)))
                      (η Hd)))

    S₁ = sub-atᶜ {Δ ᴱ} {B₀} Θᴱ X₁ (eternal-val-restrict et W₀)
    S₂ = sub-atᶜ {Δ ᴱ} {B₀} Θᴱ X₂ V₂

    swapStep : S₂ ≡ S₁
    swapStep = sub-≡ᶜ split-≡-++ᶜ (sym eVal) mid

    isL = isSub-cast _ (eH Δ Γc B op ε) (cl-yes et s W₀ K op ε eclx)

-- THE TELESCOPE ENTRY
--
-- The clause is split off, taking the eternality decision *and* the
-- equation naming it, plus its own induction hypothesis (as
-- `ren-sub-unbox` does). That is the only way in: a bare `with eternal? A`
-- on the `_∷ᵉ_` clause hoists the decision ahead of `St`, `Γ`, `γ`, `W`,
-- `Δ`, `K` and leaves an occurrence un-abstracted, because the statement
-- mentions fixed proof terms whose types mention `(Γ ∷ A) ᴱ`. Here every
-- variable is already fixed, so `rewrite` touches the goal alone.

env-Hˢ-ᴱ-∷ : ∀ {St Γ A B} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A)
           → (Δ : Ctx) → (K : Fam B (((Γ ∷ A) ++ᶜ Δ) ᴱ))
           → (op : Op) → (ε : E)
           → (e₁ : (((Γ ∷ A) ++ᶜ Δ) ᴱ ++ᶜ Dcl B op ε)
                 ≡ ((Γ ∷ A) ᴱ ++ᶜ ([] ++ᶜ D~ Δ B op ε)))
           → (d : Dec (Eternal A)) → eternal? A ≡ d
           → (ih : (Δ₀ : Ctx) → (K₀ : Fam B ((Γ ++ᶜ Δ₀) ᴱ))
                 → env-Hˢ γ Δ₀ K₀ op ε
                 ≡ castᶜ (eStar St Δ₀ op ε)
                      (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
                        (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ₀ B op ε))
                          (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ₀) (K₀ op ε)))))
           → env-Hˢ (γ ∷ᵉ W) Δ K op ε
           ≡ castᶜ (eStar St Δ op ε)
                (env-eternal-C (ᴱ-lock-free (Γ ∷ A)) (env-ᴱ (γ ∷ᵉ W))
                  (castᶜ e₁ (K op ε)))

env-Hˢ-ᴱ : ∀ {St Γ B} → (γ : Env St Γ) → (Δ : Ctx)
         → (K : Fam B ((Γ ++ᶜ Δ) ᴱ)) → (op : Op) → (ε : E)
         → env-Hˢ γ Δ K op ε
         ≡ castᶜ (eStar St Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
               (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ) (K op ε))))

-- the state contributes nothing: the prefix is provably empty and every
-- transport loops back to the clause itself

env-Hˢ-ᴱ {B = B} ⌊ St ⌋ Δ K op ε =
  sym (    (trans (cong (castᶜ (eStar St Δ op ε))
                 (env-eternal-C-empty (toCtxᴱ-[] St)
                                      (ᴱ-lock-free (toCtx St)) _ _))
           (cast-loop₄
              (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε))
                    (ᴱ-++ᶜ (toCtx St) Δ))
              (++ᶜ-assoc (toCtx St ᴱ) [] (D~ Δ B op ε))
              (trans (cong (_++ᶜ ([] ++ᶜ D~ Δ B op ε)) (toCtxᴱ-[] St))
                     (++ᶜ-identityˡ {[] ++ᶜ D~ Δ B op ε}))
              (eStar St Δ op ε) (K op ε))))
-- the base weakening restricts to a transport ([] has no variables)

env-Hˢ-ᴱ {B = B} (∅ᵉ St) Δ K op ε =
  trans
    (C-rename-eq-≡ (cong (_++ᶜ Dcl B op ε) Efull) hren (K op ε))
    ((sym rhs-eq))
  where
    Efull = trans (ᴱ-++ᶜ [] Δ)
                  (trans (cong (_++ᶜ Δ ᴱ) (sym (toCtxᴱ-[] St)))
                         (sym (ᴱ-++ᶜ (toCtx St) Δ)))

    hren : cong-∷-ren (cong-∷-ren
             (restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (∅-ren St))))
         ≐ʳ eq-ren (cong (_++ᶜ Dcl B op ε) Efull)
    hren =
      ≐ʳ-trans (cong-ren-≐ʳ (Dcl B op ε) inner)
               (cong-ren-eq-ren-≐ʳ (Dcl B op ε) Efull)
      where
        inner : restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (∅-ren St))
              ≐ʳ eq-ren Efull
        inner =
          conj-eq-≐ʳ (ᴱ-++ᶜ [] Δ)
                    (cong (_++ᶜ Δ ᴱ) (sym (toCtxᴱ-[] St)))
                    (sym (ᴱ-++ᶜ (toCtx St) Δ))
            (≐ʳ-trans
              (restrict-cong-≐ʳ (∅-ren St) Δ (ᴱ-++ᶜ [] Δ)
                                            (ᴱ-++ᶜ (toCtx St) Δ))
              (∘ʳ-≐ʳ ≐ʳ-refl
                (∘ʳ-≐ʳ (≐ʳ-trans
                         (cong-ren-≐ʳ (Δ ᴱ)
                           (∅-ren-≐ʳ _ (eq-ren (sym (toCtxᴱ-[] St)))))
                         (cong-ren-eq-ren-≐ʳ (Δ ᴱ) (sym (toCtxᴱ-[] St))))
                      ≐ʳ-refl)))

    rhs-eq : castᶜ (eStar St Δ op ε)
               (castᶜ (++ᶜ-identityˡ {[] ++ᶜ D~ Δ B op ε})
                 (castᶜ (++ᶜ-assoc ([] ᴱ) [] (D~ Δ B op ε))
                   (castᶜ (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                                          ∷ [ mapᵉ (op-grade op) ]
                                              (type-of-gtype (arity op)
                                                ⇒ B ‼ ε))
                                (ᴱ-++ᶜ [] Δ))
                          (K op ε))))
           ≡ subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε))
                   (cong (_++ᶜ Dcl B op ε) Efull) (K op ε)
    rhs-eq =
      trans (cast-chain₄
               (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                               ∷ [ mapᵉ (op-grade op) ]
                                   (type-of-gtype (arity op) ⇒ B ‼ ε))
                     (ᴱ-++ᶜ [] Δ))
               (++ᶜ-assoc ([] ᴱ) [] (D~ Δ B op ε))
               (++ᶜ-identityˡ {[] ++ᶜ D~ Δ B op ε})
               (eStar St Δ op ε) (K op ε))
            (cong (λ p → subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) p (K op ε)) uip)
-- a reach's restriction is a transport between provably-empty state parts

env-Hˢ-ᴱ {B = B} (reachᵉ {St} {St'} γ q) Δ K op ε =
  trans (C-rename-eq-≡ Ewhole hren (env-Hˢ γ Δ K op ε))
    (trans (substᶜ-≡ Ewhole (env-Hˢ-ᴱ γ Δ K op ε))
      ((trans (cong (subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) Ewhole)
                         (castᶜ≡subst (eStar St Δ op ε) _))
              (trans (subst-fuseᶜ (eStar St Δ op ε) Ewhole _)
                (trans (cong (λ p → subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) p _)
                             (uip {p = trans (eStar St Δ op ε) Ewhole}
                                  {q = eStar St' Δ op ε}))
                       (sym (castᶜ≡subst (eStar St' Δ op ε) _)))))))
  where
    EStSt' = trans (toCtxᴱ-[] St) (sym (toCtxᴱ-[] St'))

    Einner = trans (ᴱ-++ᶜ (toCtx St) Δ)
                   (trans (cong (_++ᶜ Δ ᴱ) EStSt')
                          (sym (ᴱ-++ᶜ (toCtx St') Δ)))

    Ewhole = cong (_++ᶜ Dcl B op ε) Einner

    hren : cong-∷-ren (cong-∷-ren
             (restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (reach-renᵘ q))))
         ≐ʳ eq-ren Ewhole
    hren =
      ≐ʳ-trans (cong-ren-≐ʳ (Dcl B op ε) inner)
               (cong-ren-eq-ren-≐ʳ (Dcl B op ε) Einner)
      where
        inner : restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (reach-renᵘ q))
              ≐ʳ eq-ren Einner
        inner =
          conj-eq-≐ʳ (ᴱ-++ᶜ (toCtx St) Δ) (cong (_++ᶜ Δ ᴱ) EStSt')
                    (sym (ᴱ-++ᶜ (toCtx St') Δ))
            (≐ʳ-trans
              (restrict-cong-≐ʳ (reach-renᵘ q) Δ (ᴱ-++ᶜ (toCtx St) Δ)
                                                (ᴱ-++ᶜ (toCtx St') Δ))
              (∘ʳ-≐ʳ ≐ʳ-refl
                (∘ʳ-≐ʳ (≐ʳ-trans
                         (cong-ren-≐ʳ (Δ ᴱ)
                           (empty-src-≐ʳ (toCtxᴱ-[] St) _ EStSt'))
                         (cong-ren-eq-ren-≐ʳ (Δ ᴱ) EStSt'))
                      ≐ʳ-refl)))
-- a lock: the recursion at the lock-absorbing suffix; the crossing
-- renaming restricts to a transport, and the suffix relocation moves
-- inside `env-eternal-C`

env-Hˢ-ᴱ {B = B} (_⟨_⟩ᵉ {St} {St'} {Γ} {ρ} γ q) Δ K op ε =
  trans (C-rename-eq-≡ EW hren _)
    (trans
      (substᶜ-≡ EW (castᶜ-≡ eo (env-Hˢ-ᴱ γ Δ' K' op ε)))
      (step))
  where
    CT = B ‼ (op-grade op ·ₑ ε)

    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) (K op' ε')

    eo = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))

    E₁₂ = trans (toCtxᴱ-[] St) (sym (toCtxᴱ-[] St'))

    EI = trans (ᴱ-++ᶜ (toCtx St ⟨ ρ ⟩) Δ)
               (trans (cong (_++ᶜ Δ ᴱ) E₁₂)
                      (sym (ᴱ-++ᶜ (toCtx St') Δ)))

    EW = cong (_++ᶜ Dcl B op ε) EI

    hren : cong-∷-ren (cong-∷-ren
             (restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (unbox-ren q))))
         ≐ʳ eq-ren EW
    hren =
      ≐ʳ-trans (cong-ren-≐ʳ (Dcl B op ε) inner)
               (cong-ren-eq-ren-≐ʳ (Dcl B op ε) EI)
      where
        inner : restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (unbox-ren q))
              ≐ʳ eq-ren EI
        inner =
          conj-eq-≐ʳ (ᴱ-++ᶜ (toCtx St ⟨ ρ ⟩) Δ) (cong (_++ᶜ Δ ᴱ) E₁₂)
                    (sym (ᴱ-++ᶜ (toCtx St') Δ))
            (≐ʳ-trans
              (restrict-cong-≐ʳ (unbox-ren q) Δ (ᴱ-++ᶜ (toCtx St ⟨ ρ ⟩) Δ)
                                               (ᴱ-++ᶜ (toCtx St') Δ))
              (∘ʳ-≐ʳ ≐ʳ-refl
                (∘ʳ-≐ʳ (≐ʳ-trans
                         (cong-ren-≐ʳ (Δ ᴱ)
                           (empty-src-≐ʳ (toCtxᴱ-[] St) _ E₁₂))
                         (cong-ren-eq-ren-≐ʳ (Δ ᴱ) E₁₂))
                      ≐ʳ-refl)))

    eΔ'Δ : Δ' ᴱ ≡ Δ ᴱ
    eΔ'Δ = trans (ᴱ-++ᶜ ([] ⟨ ρ ⟩) Δ) (++ᶜ-identityˡ {Δ ᴱ})

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ ([] ++ᶜ D~ Δ B op ε)
    eSuf = cong (λ Γ₁ → [] ++ᶜ (Γ₁ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ]
                                      (type-of-gtype (arity op) ⇒ B ‼ ε)))
                eΔ'Δ

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    cE = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (ᴱ-++ᶜ (Γ ⟨ ρ ⟩) Δ)

    X' = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
             (castᶜ cE' (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
               (sym (cast-chain₂ cE (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                                 (K op ε))))

    step : subst (_⊢C⦂ CT) EW
             (castᶜ eo (castᶜ (eStar St Δ' op ε) X'))
         ≡ castᶜ (eStar St' Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
               (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))))
    step =
      trans (cong (subst (_⊢C⦂ CT) EW)
                  (cast-chain₂ (eStar St Δ' op ε) eo X'))
        (trans (subst-fuseᶜ (trans (eStar St Δ' op ε) eo) EW X')
          (trans (cong (λ p → subst (_⊢C⦂ CT) p X') uip)
            (trans (sym (cast-chain₂ eSuf (eStar St' Δ op ε) X'))
              (cong (castᶜ (eStar St' Δ op ε))
                (trans (env-eternal-C-suffix eSuf (ᴱ-lock-free Γ)
                                             (env-ᴱ γ) _)
                       (cong (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ))
                             inner-eq))))))
-- a telescope entry, and the eternal prefix. Both are open; see the note
-- below `env-eternal-C-swap` and `notes/adequacy-plan.md` for what they
-- need and why `with eternal? A` is not the way in.

env-Hˢ-ᴱ {B = B} (_∷ᵉ_ {St} {Γ} {A} γ W) Δ K op ε =
  trans
    (env-Hˢ-ᴱ-∷ γ W Δ K op ε
       (trans (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε))
                    (ᴱ-++ᶜ (Γ ∷ A) Δ))
              (++ᶜ-assoc ((Γ ∷ A) ᴱ) [] (D~ Δ B op ε)))
       (eternal? A) refl (λ Δ₀ K₀ → env-Hˢ-ᴱ γ Δ₀ K₀ op ε))
    ((cong (λ z → castᶜ (eStar St Δ op ε)
                         (env-eternal-C (ᴱ-lock-free (Γ ∷ A))
                                        (env-ᴱ (γ ∷ᵉ W)) z))
                (trans (castᶜ≡subst _ (K op ε))
                  (sym (cast-chain₂
                          (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                                          ∷ [ mapᵉ (op-grade op) ]
                                              (type-of-gtype (arity op)
                                                ⇒ B ‼ ε))
                                (ᴱ-++ᶜ (Γ ∷ A) Δ))
                          (++ᶜ-assoc ((Γ ∷ A) ᴱ) [] (D~ Δ B op ε))
                          (K op ε))))))

env-Hˢ-ᴱ {B = B} (liftᵉ {St} {Γ} {A} {ρ} V γ) Δ K op ε =
  trans (castᶜ-≡ eo (env-Hˢ-ᴱ γ Δ' K' op ε)) (step)
  where
    CT = B ‼ (op-grade op ·ₑ ε)

    Δ' = [] ∷ [ ρ ] A ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) (K op' ε')

    eo = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))

    eΔ'Δ : Δ' ᴱ ≡ Δ ᴱ
    eΔ'Δ = trans (ᴱ-++ᶜ ([] ∷ [ ρ ] A) Δ) (++ᶜ-identityˡ {Δ ᴱ})

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ ([] ++ᶜ D~ Δ B op ε)
    eSuf = cong (λ Γ₁ → [] ++ᶜ (Γ₁ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ]
                                      (type-of-gtype (arity op) ⇒ B ‼ ε)))
                eΔ'Δ

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    cE = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (ᴱ-++ᶜ (Γ ∷ [ ρ ] A) Δ)

    X' = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
             (castᶜ cE' (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
               (sym (cast-chain₂ cE (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                                 (K op ε))))

    step : castᶜ eo (castᶜ (eStar St Δ' op ε) X')
         ≡ castᶜ (eStar (St ∷ₛ V) Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
               (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))))
    step =
      trans (cast-chain₂ (eStar St Δ' op ε) eo X')
        (trans (cong (λ p → subst (_⊢C⦂ CT) p X') uip)
          (trans (sym (cast-chain₂ eSuf (eStar (St ∷ₛ V) Δ op ε) X'))
            (cong (castᶜ (eStar (St ∷ₛ V) Δ op ε))
              (trans (env-eternal-C-suffix eSuf (ᴱ-lock-free Γ)
                                           (env-ᴱ γ) _)
                     (cong (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ))
                           inner-eq)))))
-- an eternal zone: `env-Hˢ` runs it before the zones to its left, the
-- restriction peels it last. `env-eternal-H-C` turns the zone's clause
-- action into a chain at `Δ₀ ᴱ`, and `env-eternal-C-++` splits the
-- restriction's own chain at `Δ₀ ᴱ ++ᶜ Γ ᴱ` into the same two halves.

env-Hˢ-ᴱ {St} {B = B} (eternalˡ {Γ = Γ} Δ₀ lf η γ) Δ K op ε =
  trans (env-Hˢ-ᴱ γ Δ K₂ op ε)
    (castᶜ-≡ (eStar St Δ op ε)
      (trans
        (env-eternal-C-≡ (ᴱ-lock-free Γ) (env-ᴱ γ)
          (trans
            (castᶜ-≡ a₁ (castᶜ-≡ cR (env-eternal-H-C lf η K₃ op ε)))
            (midEq)))
        (trans
          (sym (env-eternal-C-++ (ᴱ-lock-free Δ₀) (ᴱ-lock-free Γ)
                     lf₁₂ (ηᴱ η) (env-ᴱ γ) M₀))
          (preEq))))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Θ  = [] ++ᶜ D~ Δ B op ε
    Γ₊ = Γ ++ᶜ Δ

    K₃ : Fam B ((Δ₀ ++ᶜ Γ₊) ᴱ)
    K₃ op' ε' = Cl-cast op' ε' (++ᶜ-assoc Δ₀ Γ Δ) (K op' ε')

    K₂ : Fam B ((Γ ++ᶜ Δ) ᴱ)
    K₂ = env-eternal-H {Δ₀} {Γ₊} lf η K₃

    a₁ = ++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε)

    cR = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (ᴱ-++ᶜ Γ Δ)

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Δ₀ Γ Δ)

    cRᴿ = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ (Δ₀ ++ᶜ Γ) Δ)

    lf₁₂ : Lock-free (Δ₀ ᴱ ++ᶜ Γ ᴱ)
    lf₁₂ = subst Lock-free (ᴱ-++ᶜ Δ₀ Γ) (ᴱ-lock-free (Δ₀ ++ᶜ Γ))

    Y₀ = castᶜ (++ᶜ-assoc ((Δ₀ ++ᶜ Γ) ᴱ) [] (D~ Δ B op ε))
           (castᶜ cRᴿ (K op ε))

    M₀ = castᶜ (cong (_++ᶜ Θ) (ᴱ-++ᶜ Δ₀ Γ)) Y₀

    -- the two casts between the halves move inside the inner chain, and
    -- both towers are transports of the same clause
    midEq : castᶜ a₁
              (castᶜ cR
                (env-eternal-C {_} {Γ₊ ᴱ ++ᶜ Dcl B op ε}
                   (ᴱ-lock-free Δ₀) (ηᴱ η)
                   (castᶜ (eH Δ₀ Γ₊ B op ε) (K₃ op ε))))
          ≡ env-eternal-C (ᴱ-lock-free Δ₀) (ηᴱ η)
              (castᶜ (++ᶜ-assoc (Δ₀ ᴱ) (Γ ᴱ) Θ) M₀)
    midEq =
      trans (cong (castᶜ a₁)
               (env-eternal-C-suffix cR (ᴱ-lock-free Δ₀) (ηᴱ η) _))
        (trans (env-eternal-C-suffix a₁ (ᴱ-lock-free Δ₀) (ηᴱ η) _)
          (cong (env-eternal-C (ᴱ-lock-free Δ₀) (ηᴱ η))
            (trans (cast-chain₄ cKassoc (eH Δ₀ Γ₊ B op ε)
                      (cong (Δ₀ ᴱ ++ᶜ_) cR) (cong (Δ₀ ᴱ ++ᶜ_) a₁) (K op ε))
              (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
                     (sym (cast-chain₄ cRᴿ
                             (++ᶜ-assoc ((Δ₀ ++ᶜ Γ) ᴱ) [] (D~ Δ B op ε))
                             (cong (_++ᶜ Θ) (ᴱ-++ᶜ Δ₀ Γ))
                             (++ᶜ-assoc (Δ₀ ᴱ) (Γ ᴱ) Θ) (K op ε)))))))

    -- `env-ᴱ` at an eternal zone *is* the concatenated values
    hη : ∀ {A ρ} → (x : A ∈[ ρ ] ((Δ₀ ++ᶜ Γ) ᴱ))
       → env-ᴱ (eternalˡ Δ₀ lf η γ) x
       ≡ splitVal (ηᴱ η) (env-ᴱ γ)
           (∈-++ᶜ-split (Δ₀ ᴱ) (Γ ᴱ)
             (subst (λ Γ₁ → _ ∈[ _ ] Γ₁) (ᴱ-++ᶜ Δ₀ Γ) x))
    hη x
      with ∈-++ᶜ-split (Δ₀ ᴱ) (Γ ᴱ)
             (subst (λ Γ₁ → _ ∈[ _ ] Γ₁) (ᴱ-++ᶜ Δ₀ Γ) x)
    ... | inj₁ (ρ' , y) = refl
    ... | inj₂ y        = refl

    hpre : ∀ {A ρ} → (y : A ∈[ ρ ] (Δ₀ ᴱ ++ᶜ Γ ᴱ))
         → ++ᶜᵛ (ᴱ-lock-free Γ) (ηᴱ η) (env-ᴱ γ) y
         ≡ env-ᴱ (eternalˡ Δ₀ lf η γ)
             (subst (λ Γ₁ → A ∈[ ρ ] Γ₁) (sym (ᴱ-++ᶜ Δ₀ Γ)) y)
    hpre y =
      trans (++ᶜᵛ-split (ᴱ-lock-free Γ) (ηᴱ η) (env-ᴱ γ) y)
        (sym (trans (hη (subst (λ Γ₁ → _ ∈[ _ ] Γ₁) (sym (ᴱ-++ᶜ Δ₀ Γ)) y))
               (cong (λ z → splitVal (ηᴱ η) (env-ᴱ γ)
                              (∈-++ᶜ-split (Δ₀ ᴱ) (Γ ᴱ) z))
                     (subst-subst-sym′ (ᴱ-++ᶜ Δ₀ Γ) y))))

    preEq : env-eternal-C lf₁₂ (++ᶜᵛ (ᴱ-lock-free Γ) (ηᴱ η) (env-ᴱ γ)) M₀
          ≡ env-eternal-C (ᴱ-lock-free (Δ₀ ++ᶜ Γ))
              (env-ᴱ (eternalˡ Δ₀ lf η γ)) Y₀
    preEq =
      trans (env-eternal-C-pre (sym (ᴱ-++ᶜ Δ₀ Γ)) lf₁₂
               (ᴱ-lock-free (Δ₀ ++ᶜ Γ)) _ (env-ᴱ (eternalˡ Δ₀ lf η γ))
               hpre M₀)
            (cong (env-eternal-C (ᴱ-lock-free (Δ₀ ++ᶜ Γ))
                                 (env-ᴱ (eternalˡ Δ₀ lf η γ)))
                  (cast-loop₂ (cong (_++ᶜ Θ) (ᴱ-++ᶜ Δ₀ Γ))
                              (cong (_++ᶜ Θ) (sym (ᴱ-++ᶜ Δ₀ Γ))) Y₀))

------------------------------------------------------------------------
-- THE ASSEMBLY: `env-Hˢ-clause` FROM THE STATE-FREE CORE
--
-- The outer weakening decomposes onto `cong-ren {Δ ᴱ ∷ p ∷ k} (∅-ren St₁)`
-- — exactly the renaming `env-Cˢ (env-clause γ St₁)` applies — and the
-- leftover transports loop.
------------------------------------------------------------------------

env-Hˢ-clause : ∀ {St Γ B} → (γ : Env St Γ) → (St₁ : 𝕊 []) → (Δ : Ctx)
               → (K : Fam B ((Γ ++ᶜ Δ) ᴱ)) → (op : Op) → (ε : E)
               → C-rename (cong-∷-ren (cong-∷-ren
                             (eq-ren (toCtxᴱ-++ᶜ St Δ) ∘ʳ clause-ren St₁ Δ)))
                          (env-Hˢ γ Δ K op ε)
               ≡ env-Cˢ (env-clause γ St₁)
                         (Δ ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε))
                         (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ) (K op ε))

env-Hˢ-clause {St} {Γ} {B} γ St₁ Δ K op ε =
  trans
    (C-rename-cong _ (env-Hˢ-ᴱ γ Δ K op ε))
    (trans
      (C-rename-conj eIn eOut hconj
         (castᶜ (eStar St Δ op ε) X))
      (        (trans (cong (subst (_⊢C⦂ CT) eOut)
                 (cong (C-rename (cong-ren {Γ'' = D~ Δ B op ε} (∅-ren St₁)))
                   (trans (cong (subst (_⊢C⦂ CT) eIn)
                                (castᶜ≡subst (eStar St Δ op ε) X))
                     (trans (subst-fuseᶜ (eStar St Δ op ε) eIn X)
                            (subst-loopᶜ _ X)))))
               (subst-loopᶜ eOut _))))
  where
    CT = B ‼ (op-grade op ·ₑ ε)

    X = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
          (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
            (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ) (K op ε)))

    eIn : ((toCtx St ++ᶜ Δ) ᴱ ∷ type-of-gtype (param op)
             ∷ [ mapᵉ (op-grade op) ]
                 (type-of-gtype (arity op) ⇒ B ‼ ε))
        ≡ ([] ++ᶜ D~ Δ B op ε)
    eIn = sym (eStar St Δ op ε)

    eOut : (toCtx St₁ ++ᶜ D~ Δ B op ε)
         ≡ (toCtx St₁ ++ᶜ D~ Δ B op ε)
    eOut = refl

    hconj : cong-∷-ren (cong-∷-ren
              (eq-ren (toCtxᴱ-++ᶜ St Δ) ∘ʳ clause-ren St₁ Δ))
          ≐ʳconj⟨ eIn , cong-ren {Γ'' = D~ Δ B op ε} (∅-ren St₁) , eOut ⟩
    hconj =
      ≐ʳ-trans
        (conj-cong-ren (Dcl B op ε) EA refl
          (≐ʳ-trans
            (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl hsplit) (≐ʳ-sym (∘ʳ-assoc-≐ʳ _ _ _)))
            (≐ʳ-trans
              (∘ʳ-≐ʳ (eq-ren-∘-≐ʳ (toCtxᴱ-++ᶜ St Δ)
                                (sym (++ᶜ-identityˡ {Δ ᴱ})))
                    ≐ʳ-refl)
              (∘ʳ-≐ʳ (eq-ren-≐ʳ _ EA) (≐ʳ-sym (∘ʳ-identityʳ-≐ʳ _))))))
        (≐ʳ-trans
          (conj-fuse (cong (_++ᶜ Dcl B op ε) EA) refl
             (++ᶜ-assoc [] (Δ ᴱ) (Dcl B op ε))
             (sym (++ᶜ-assoc (toCtx St₁) (Δ ᴱ) (Dcl B op ε)))
             (cong-ren-assoc-≐ʳ (Δ ᴱ) (Dcl B op ε) (∅-ren St₁)))
          (∘ʳ-≐ʳ (eq-ren-≐ʳ _ eIn) (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-≐ʳ _ eOut))))
      where
        EA = trans (toCtxᴱ-++ᶜ St Δ) (sym (++ᶜ-identityˡ {Δ ᴱ}))

        hsplit : clause-ren St₁ Δ
               ≐ʳ (eq-ren (sym (++ᶜ-identityˡ {Δ ᴱ}))
                   ∘ʳ cong-ren {Γ'' = Δ ᴱ} (∅-ren St₁))
        hsplit = ≐ʳ-refl

-- at a non-eternal entry the whole zone disappears from both sides: the
-- clause substitution is a transport and so is the entry's contribution
-- to the restriction, so this is `liftᵉ`'s case with one transport more

env-Hˢ-ᴱ-∷ {St} {Γ} {A} {B} γ W Δ K op ε e₁ (no ¬et) eq ih rewrite eq =
  trans
    (trans (cl-ne-≡ ¬et (split-≡-++ᶜ {toCtx St ∷ A} {Δ}) W Kᵢ op ε)
           (substᶜ-≡′ (λ Γ₀ → Γ₀ ++ᶜ Dc) dropM
             (castᶜ-≡ eo (ih Δ' K'))))
    (step)
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε

    Δ' = [] ∷ A ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ A) Δ) (K op' ε')

    dropM = ᴱ-drop-split ¬et (split-≡-++ᶜ {toCtx St ∷ A} {Δ})

    eo = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))

    -- the family the zone's substitution is applied to
    Kᵢ : Fam B (((toCtx St ∷ A) ++ᶜ Δ) ᴱ)
    Kᵢ op' ε' = Cl-cast op' ε' (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
                  (env-Hˢ γ Δ' K' op' ε')

    -- `A` is not eternal, so it drops out of the restricted suffix
    eΔ'Δ : Δ' ᴱ ≡ Δ ᴱ
    eΔ'Δ = trans (ᴱ-++ᶜ ([] ∷ A) Δ)
             (trans (cong (_++ᶜ Δ ᴱ) (ᴱ-∷-drop {[]} {A} ¬et))
                    (++ᶜ-identityˡ {Δ ᴱ}))

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ ([] ++ᶜ D~ Δ B op ε)
    eSuf = cong (λ Γ₁ → [] ++ᶜ (Γ₁ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ]
                                      (type-of-gtype (arity op) ⇒ B ‼ ε)))
                eΔ'Δ

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ∷ A) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    X' = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
             (castᶜ cE' (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ e₁ (K op ε)
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
               (sym (castᶜ≡subst e₁ (K op ε))))

    step : subst (λ Γ₀ → (Γ₀ ++ᶜ Dc) ⊢C⦂ CT) dropM
             (castᶜ eo (castᶜ (eStar St Δ' op ε) X'))
         ≡ castᶜ (eStar St Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ) (castᶜ e₁ (K op ε)))
    step =
      trans (cong (subst (λ Γ₀ → (Γ₀ ++ᶜ Dc) ⊢C⦂ CT) dropM)
                  (cast-chain₂ (eStar St Δ' op ε) eo X'))
        (trans (subst-++ᶜʳ Dc dropM _)
          (trans (subst-fuseᶜ (trans (eStar St Δ' op ε) eo)
                              (cong (_++ᶜ Dc) dropM) X')
            (trans (cong (λ p → subst (_⊢C⦂ CT) p X') uip)
              (trans (sym (cast-chain₂ eSuf (eStar St Δ op ε) X'))
                (cong (castᶜ (eStar St Δ op ε))
                  (trans (env-eternal-C-suffix eSuf (ᴱ-lock-free Γ)
                                               (env-ᴱ γ) _)
                         (cong (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ))
                               inner-eq)))))))
-- at an eternal entry both sides substitute the restricted value, but at
-- different prefixes: the clause zone at the state's (provably empty)
-- one, `env-eternal-C` at `Γ ᴱ`, and only after the chain to its left.
-- `cl-yes` presents the former as a `sub-atᶜ`, `sub-at-≡` aligns the two,
-- and `env-eternal-C-swap` moves the latter past the chain.

env-Hˢ-ᴱ-∷ {St} {Γ} {A} {B} γ W Δ K op ε e₁ (yes et) eq ih rewrite eq =
  trans lhs-step
    (castᶜ-≡ (eStar St Δ op ε)
      (env-eternal-C-swap lf (env-ᴱ γ) Θ' V₂ (castᶜ e₁ (K op ε))))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε
    lf = ᴱ-lock-free Γ

    Θ' = [] ++ᶜ D~ Δ B op ε
    Δ' = [] ∷ A ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ A) Δ) (K op' ε')

    Krec : Fam B (((toCtx St ∷ A) ++ᶜ Δ) ᴱ)
    Krec op' ε' = Cl-cast op' ε' (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
                    (env-Hˢ γ Δ' K' op' ε')

    s = split-≡-++ᶜ {toCtx St ∷ A} {Δ}

    V₂ = castᵛ (toCtxᴱ-[] St) (eternal-val-restrict et W)

    eclx = eCl et s B op ε

    X₁ = subst (_⊢C⦂ CT) eclx (Krec op ε)

    X₂ = env-eternal-C lf (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) ([] ∷ A) Θ') (castᶜ e₁ (K op ε)))

    -- the state's half of the splitting is empty, the other half is `Δ`
    eΓ : toCtx St ᴱ ≡ []
    eΓ = toCtxᴱ-[] St

    eΘ : (Δ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘ = sym (++ᶜ-identityˡ {D~ Δ B op ε})

    e  = cong₂ (λ Γ₁ Θ₁ → (Γ₁ ∷ A) ++ᶜ Θ₁) eΓ eΘ
    e' = cong₂ _++ᶜ_ eΓ eΘ

    -- `A` is eternal, so it survives into the recursion's restricted suffix
    eΔsuf : ([] ++ᶜ Δ' ᴱ) ≡ (([] ∷ A) ++ᶜ ([] ++ᶜ Δ ᴱ))
    eΔsuf = trans (++ᶜ-identityˡ {Δ' ᴱ})
              (trans (ᴱ-++ᶜ ([] ∷ A) Δ)
                (trans (cong (_++ᶜ Δ ᴱ) (ᴱ-∷-keep {[]} {A} et))
                       (cong (([] ∷ A) ++ᶜ_) (sym (++ᶜ-identityˡ {Δ ᴱ})))))

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ (([] ∷ A) ++ᶜ Θ')
    eSuf = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B ‼ ε))
                eΔsuf

    cAssoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                            ∷ [ mapᵉ (op-grade op) ]
                                (type-of-gtype (arity op) ⇒ B ‼ ε))
                  (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ∷ A) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    Y = env-eternal-C lf (env-ᴱ γ)
          (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
            (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ') (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ (++ᶜ-assoc (Γ ᴱ) ([] ∷ A) Θ') (castᶜ e₁ (K op ε))
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ q → subst (_⊢C⦂ CT) q (K op ε)) uip)
               (sym (cast-chain₂ e₁ (++ᶜ-assoc (Γ ᴱ) ([] ∷ A) Θ') (K op ε))))

    collapse : subst (_⊢C⦂ CT) e
                 (subst (_⊢C⦂ CT) eclx
                   (castᶜ cAssoc (castᶜ (eStar St Δ' op ε) Y)))
             ≡ X₂
    collapse =
      trans (cong (λ z → subst (_⊢C⦂ CT) e (subst (_⊢C⦂ CT) eclx z))
                  (cast-chain₂ (eStar St Δ' op ε) cAssoc Y))
        (trans (cong (subst (_⊢C⦂ CT) e)
                     (subst-fuseᶜ (trans (eStar St Δ' op ε) cAssoc) eclx Y))
          (trans (subst-fuseᶜ (trans (trans (eStar St Δ' op ε) cAssoc) eclx) e Y)
            (trans (cong (λ q → subst (_⊢C⦂ CT) q Y) uip)
              (trans (sym (castᶜ≡subst eSuf Y))
                (trans (env-eternal-C-suffix eSuf lf (env-ᴱ γ) _)
                       (cong (env-eternal-C lf (env-ᴱ γ)) inner-eq))))))

    mid : X₂ ≡ subst (_⊢C⦂ CT) e X₁
    mid =
      sym
        (trans (substᶜ-≡ e (substᶜ-≡ eclx (castᶜ-≡ cAssoc (ih Δ' K'))))
                  (collapse))

    eVal : subst (_⊢V⦂ A) eΓ (eternal-val-restrict et W) ≡ V₂
    eVal = sym (castᵛ≡subst (toCtxᴱ-[] St) (eternal-val-restrict et W))

    S₁ = sub-atᶜ {toCtx St ᴱ} {A} (Δ ᴱ ++ᶜ Dc) X₁
                 (eternal-val-restrict et W)

    S₂ = sub-atᶜ {[]} {A} Θ' X₂ V₂

    swapStep : S₂ ≡ subst (_⊢C⦂ CT) e' S₁
    swapStep =
      sub-at-≡ eΓ eΘ X₁ X₂ e mid (eternal-val-restrict et W) V₂ eVal e'

    isL = cl-yes et s W Krec op ε eclx

    isMid : IsSub S₁ (subst (_⊢C⦂ CT) e' S₁)
    isMid = e' , refl

    isR = isSub-cast _ (eStar St Δ op ε)
            (isSub-cast _ (++ᶜ-identityˡ {Θ'}) (isSub-refl S₂))

    lhs-step = isSub-≡ (isSub-reassoc isL isMid) isR (sym swapStep)

