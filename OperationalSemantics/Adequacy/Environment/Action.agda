------------------------------------------------------------------------
-- The action of an environment on terms, and its commutation with every former.
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

module OperationalSemantics.Adequacy.Environment.Action (Spec : LanguageSpec) where

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
open import Syntax.Substitutions.At        Spec
open import Syntax.Substitutions.Clauses   Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec
open import OperationalSemantics.Adequacy.Environment.Core Spec


------------------------------------------------------------------------
-- THE ACTION
--
-- Iterated single substitutions. Two things make it go through with only the
-- prefix-typed substitution `_[_↦_]c` the formalisation has:
--
--   * the variable to replace sits under whatever the recursion has already
--     passed, so the action is defined under an arbitrary *suffix* `Δ`. A lock
--     is absorbed into that suffix (`(Γ ⟨ ρ ⟩) ++ᶜ Δ ≡ Γ ++ᶜ ([] ⟨ ρ ⟩ ++ᶜ Δ)`),
--     which is what lets the substitution cross it: crossing is the
--     grade-lowering case of `⟨_,_⟩[_↦_]var`, licensed by the `var` rule's own
--     premise, and needs nothing from here;
--
--   * a telescope entry is substituted *last*: it rides along in the suffix
--     (`[] ∷ A ++ᶜ Δ`) and its variable is substituted afterwards. Its value
--     already lives over the prefix `toCtx St`, so it needs no weakening, and
--     `env-C (γ ∷ᵉ W) M ≡ (env-Cˢ γ ([] ∷ A) M) [ split-[] ↦ W ]c` holds
--     definitionally — the order `APP` wants.
------------------------------------------------------------------------

-- THE ETERNAL ZONE
--
-- Substitute each prefix variable by its closed value, outermost first, each
-- weakened into the prefix left of the variable it replaces (`empty-ren`).

env-eternal-V : ∀ {Δ Γ A} → Lock-free Δ → ClosedVals Δ
              → (Δ ++ᶜ Γ) ⊢V⦂ A → Γ ⊢V⦂ A
env-eternal-V lf-[] η V = castᵛ ++ᶜ-identityˡ V
env-eternal-V {Δ ∷ B} {Γ} (lf-∷ lf) η V =
  env-eternal-V lf (λ x → η (Tl-∷ x))
    (sub-atᵛ Γ V (V-rename (empty-ren lf) (η Hd)))

env-eternal-C : ∀ {Δ Γ C} → Lock-free Δ → ClosedVals Δ
              → (Δ ++ᶜ Γ) ⊢C⦂ C → Γ ⊢C⦂ C
env-eternal-C lf-[] η M = castᶜ ++ᶜ-identityˡ M
env-eternal-C {Δ ∷ B} {Γ} (lf-∷ lf) η M =
  env-eternal-C lf (λ x → η (Tl-∷ x))
    (sub-atᶜ Γ M (V-rename (empty-ren lf) (η Hd)))

-- The action under a suffix.

env-Vˢ : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢V⦂ A
       → (toCtx St ++ᶜ Δ) ⊢V⦂ A

env-Cˢ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢C⦂ C
       → (toCtx St ++ᶜ Δ) ⊢C⦂ C

env-Vˢ ⌊ St ⌋ Δ V = V
env-Vˢ (∅ᵉ St) Δ V = V-rename (cong-ren (∅-ren St)) V
env-Vˢ (reachᵉ γ q) Δ V = V-rename (cong-ren (reach-renᵘ q)) (env-Vˢ γ Δ V)
env-Vˢ (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  V-rename (cong-ren (unbox-ren q))
    (castᵛ (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))
      (env-Vˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
        (castᵛ (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) V)))
env-Vˢ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ V =
  sub-atᵛ Δ
    (castᵛ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
      (env-Vˢ γ ([] ∷ A ++ᶜ Δ) (castᵛ (++ᶜ-assoc Γ ([] ∷ A) Δ) V)))
    W
env-Vˢ (liftᵉ {St = St} {Γ = Γ} {A = A} {ρ = ρ} V γ) Δ V₀ =
  castᵛ (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))
    (env-Vˢ γ ([] ∷ [ ρ ] A ++ᶜ Δ)
      (castᵛ (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) V₀))
env-Vˢ (eternalˡ Δ₀ lf η γ) Δ V =
  env-Vˢ γ Δ (env-eternal-V lf η (castᵛ (++ᶜ-assoc Δ₀ _ Δ) V))

env-Cˢ ⌊ St ⌋ Δ M = M
env-Cˢ (∅ᵉ St) Δ M = C-rename (cong-ren (∅-ren St)) M
env-Cˢ (reachᵉ γ q) Δ M = C-rename (cong-ren (reach-renᵘ q)) (env-Cˢ γ Δ M)
env-Cˢ (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M =
  C-rename (cong-ren (unbox-ren q))
    (castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))
      (env-Cˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
        (castᶜ (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) M)))
env-Cˢ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ M =
  sub-atᶜ Δ
    (castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
      (env-Cˢ γ ([] ∷ A ++ᶜ Δ) (castᶜ (++ᶜ-assoc Γ ([] ∷ A) Δ) M)))
    W
env-Cˢ (liftᵉ {St = St} {Γ = Γ} {A = A} {ρ = ρ} V γ) Δ M =
  castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))
    (env-Cˢ γ ([] ∷ [ ρ ] A ++ᶜ Δ)
      (castᶜ (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) M))
env-Cˢ (eternalˡ Δ₀ lf η γ) Δ M =
  env-Cˢ γ Δ (env-eternal-C lf η (castᶜ (++ᶜ-assoc Δ₀ _ Δ) M))

-- THE ACTION COMMUTES WITH `lam`
--
-- Each single substitution does: the substitution at suffix `Δ ∷ A` is
-- `cong-∷-sub` of the one at `Δ` — definitionally, since `split-≡-++ᶜ` is
-- `≡-split refl` and both it and `sub-split₀` recurse on the suffix — and that
-- congruence is exactly what the action inserts at a binder.

env-eternal-lam : ∀ {Δ Γ A B ε} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (M : (Δ ++ᶜ Γ) ∷ A ⊢C⦂ B ‼ ε)
                → env-eternal-V lf η (lam M) ≡ lam (env-eternal-C lf η M)

env-eternal-lam {A = A} lf-[] η M =
  trans (cast-lam ++ᶜ-identityˡ M)
        (cong lam (castᶜ-irr (cong (_∷ A) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))

env-eternal-lam {Δ ∷ B} {Γ} {A} (lf-∷ lf) η M =
  env-eternal-lam lf (λ x → η (Tl-∷ x))
    (sub-atᶜ (Γ ∷ A) M (V-rename (empty-ren lf) (η Hd)))

env-Vˢ-lam : ∀ {St Γ A B ε} → (γ : Env St Γ) → (Δ : Ctx)
           → (M : (Γ ++ᶜ Δ) ∷ A ⊢C⦂ B ‼ ε)
           → env-Vˢ γ Δ (lam M) ≡ lam (env-Cˢ γ (Δ ∷ A) M)

env-Vˢ-lam ⌊ St ⌋ Δ M = refl
env-Vˢ-lam (∅ᵉ St) Δ M = refl
env-Vˢ-lam (reachᵉ γ q) Δ M = cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-lam γ Δ M)

env-Vˢ-lam {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (lam M)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-lam ei M) ⟩
      castᵛ eo (env-Vˢ γ Δ' (lam (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-lam γ Δ' (castᶜ (cong (_∷ A) ei) M)) ⟩
      castᵛ eo (lam (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cast-lam eo _ ⟩
      lam (castᶜ (cong (_∷ A) eo) (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cong lam (castᶜ-irr (cong (_∷ A) eo) eo' _) ⟩
      lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cong (λ z → lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) z)))
            (castᶜ-irr (cong (_∷ A) ei) ei' M) ⟩
      lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ ei' M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo' = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ A))
    ei' = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ A)

env-Vˢ-lam {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ M =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (lam M)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-lam ei M) ⟩
    castᵛ eo (env-Vˢ γ Δ' (lam (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-lam γ Δ' (castᶜ (cong (_∷ A) ei) M)) ⟩
    castᵛ eo (lam (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cast-lam eo _ ⟩
    lam (castᶜ (cong (_∷ A) eo) (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cong lam (castᶜ-irr (cong (_∷ A) eo) eo' _) ⟩
    lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cong (λ z → lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) z)))
          (castᶜ-irr (cong (_∷ A) ei) ei' M) ⟩
    lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ ei' M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo' = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ A))
    ei' = ++ᶜ-assoc Γ Δ₁ (Δ ∷ A)

env-Vˢ-lam {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (lam M)))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ z)) W) (cast-lam eA M) ⟩
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (lam (castᶜ (cong (_∷ A) eA) M)))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W)
          (env-Vˢ-lam γ Δ₁ (castᶜ (cong (_∷ A) eA) M)) ⟩
    sub-atᵛ Δ (castᵛ eIn (lam body)) W
  ≡⟨ cong (λ z → sub-atᵛ Δ z W) (cast-lam eIn body) ⟩
    sub-atᵛ Δ (lam (castᶜ (cong (_∷ A) eIn) body)) W
  ≡⟨ cong (λ z → lam (sub-atᶜ (Δ ∷ A) z W))
          (castᶜ-irr (cong (_∷ A) eIn) eIn' body) ⟩
    lam (sub-atᶜ (Δ ∷ A) (castᶜ eIn' body) W)
  ≡⟨ cong (λ z → lam (sub-atᶜ (Δ ∷ A)
             (castᶜ eIn' (env-Cˢ γ (Δ₁ ∷ A) z)) W))
          (castᶜ-irr (cong (_∷ A) eA) eA' M) ⟩
    lam (sub-atᶜ (Δ ∷ A) (castᶜ eIn' (env-Cˢ γ (Δ₁ ∷ A) (castᶜ eA' M))) W)
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn'  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA'   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ A)
    body  = env-Cˢ γ (Δ₁ ∷ A) (castᶜ (cong (_∷ A) eA) M)

env-Vˢ-lam {A = A} (eternalˡ Δ₀ lf η γ) Δ M =
  begin
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e (lam M)))
  ≡⟨ cong (λ z → env-Vˢ γ Δ (env-eternal-V lf η z)) (cast-lam e M) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (lam (castᶜ (cong (_∷ A) e) M)))
  ≡⟨ cong (env-Vˢ γ Δ) (env-eternal-lam lf η (castᶜ (cong (_∷ A) e) M)) ⟩
    env-Vˢ γ Δ (lam (env-eternal-C lf η (castᶜ (cong (_∷ A) e) M)))
  ≡⟨ env-Vˢ-lam γ Δ (env-eternal-C lf η (castᶜ (cong (_∷ A) e) M)) ⟩
    lam (env-Cˢ γ (Δ ∷ A) (env-eternal-C lf η (castᶜ (cong (_∷ A) e) M)))
  ≡⟨ cong (λ z → lam (env-Cˢ γ (Δ ∷ A) (env-eternal-C lf η z)))
          (castᶜ-irr (cong (_∷ A) e) e' M) ⟩
    lam (env-Cˢ γ (Δ ∷ A) (env-eternal-C lf η (castᶜ e' M)))
  ∎
  where
    e  = ++ᶜ-assoc Δ₀ _ Δ
    e' = ++ᶜ-assoc Δ₀ _ (Δ ∷ A)

env-eternal-pair : ∀ {Δ Γ A B} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                 → (V : (Δ ++ᶜ Γ) ⊢V⦂ A) → (W : (Δ ++ᶜ Γ) ⊢V⦂ B)
                 → env-eternal-V lf η ⦉ V , W ⦊
                 ≡ ⦉ env-eternal-V lf η V , env-eternal-V lf η W ⦊
env-eternal-pair lf-[]     η V W = cast-pair ++ᶜ-identityˡ
env-eternal-pair (lf-∷ lf) η V W =
  trans (cong (env-eternal-V lf _) (cast-pair _))
        (env-eternal-pair lf _ _ _)

env-eternal-ret : ∀ {Δ Γ A} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ A)
                → env-eternal-C lf η (return V) ≡ return (env-eternal-V lf η V)
env-eternal-ret lf-[]     η V = cast-ret ++ᶜ-identityˡ
env-eternal-ret (lf-∷ lf) η V =
  trans (cong (env-eternal-C lf _) (cast-ret _)) (env-eternal-ret lf _ _)

env-eternal-app : ∀ {Δ Γ A C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ A ⇒ C) → (W : (Δ ++ᶜ Γ) ⊢V⦂ A)
                → env-eternal-C lf η (V · W)
                ≡ (env-eternal-V lf η V) · (env-eternal-V lf η W)
env-eternal-app lf-[]     η V W = cast-app ++ᶜ-identityˡ
env-eternal-app (lf-∷ lf) η V W =
  trans (cong (env-eternal-C lf _) (cast-app _)) (env-eternal-app lf _ _ _)

env-eternal-if : ∀ {Δ Γ C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
               → (V : (Δ ++ᶜ Γ) ⊢V⦂ Bool) → (M N : (Δ ++ᶜ Γ) ⊢C⦂ C)
               → env-eternal-C lf η (if V `then M `else N)
               ≡ if (env-eternal-V lf η V) `then (env-eternal-C lf η M)
                                           `else (env-eternal-C lf η N)
env-eternal-if lf-[]     η V M N = cast-if ++ᶜ-identityˡ
env-eternal-if (lf-∷ lf) η V M N =
  trans (cong (env-eternal-C lf _) (cast-if _)) (env-eternal-if lf _ _ _ _)

env-eternal-coerce : ∀ {Δ Γ A ε ε'} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                   → {p : ε ≾ₑ ε'} → (M : (Δ ++ᶜ Γ) ⊢C⦂ A ‼ ε)
                   → env-eternal-C lf η (coerce p M)
                   ≡ coerce p (env-eternal-C lf η M)
env-eternal-coerce lf-[]     η M = cast-coerce ++ᶜ-identityˡ
env-eternal-coerce (lf-∷ lf) η M =
  trans (cong (env-eternal-C lf _) (cast-coerce _))
        (env-eternal-coerce lf _ _)

env-Cˢ-ret : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx) → (V : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Cˢ γ Δ (return V) ≡ return (env-Vˢ γ Δ V)

env-Cˢ-ret ⌊ St ⌋ Δ V = refl
env-Cˢ-ret (∅ᵉ St) Δ V = refl
env-Cˢ-ret (reachᵉ γ q) Δ V = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-ret γ Δ V)

env-Cˢ-ret (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (return V)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-ret ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (return (castᵛ ei V)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-ret γ Δ' (castᵛ ei V)) ⟩
      castᶜ eo (return (env-Vˢ γ Δ' (castᵛ ei V)))
    ≡⟨ cast-ret eo ⟩
      return (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-ret (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (return V)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-ret ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (return (castᵛ ei V)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-ret γ Δ' (castᵛ ei V)) ⟩
    castᶜ eo (return (env-Vˢ γ Δ' (castᵛ ei V)))
  ≡⟨ cast-ret eo ⟩
    return (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-ret (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (return V)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-ret eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (return (castᵛ eA V)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-ret γ Δ₁ (castᵛ eA V)) ⟩
    sub-atᶜ Δ (castᶜ eIn (return (env-Vˢ γ Δ₁ (castᵛ eA V)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-ret eIn) ⟩
    sub-atᶜ Δ (return (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))) W
  ≡⟨⟩
    return (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-ret (eternalˡ Δ₀ lf η γ) Δ V =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (return V)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-ret e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (return (castᵛ e V)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-ret lf η (castᵛ e V)) ⟩
    env-Cˢ γ Δ (return (env-eternal-V lf η (castᵛ e V)))
  ≡⟨ env-Cˢ-ret γ Δ (env-eternal-V lf η (castᵛ e V)) ⟩
    return (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V)))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Cˢ-app : ∀ {St Γ A C} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A ⇒ C) → (U : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Cˢ γ Δ (V · U) ≡ (env-Vˢ γ Δ V) · (env-Vˢ γ Δ U)

env-Cˢ-app ⌊ St ⌋ Δ V U = refl
env-Cˢ-app (∅ᵉ St) Δ V U = refl
env-Cˢ-app (reachᵉ γ q) Δ V U = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-app γ Δ V U)

env-Cˢ-app (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V U =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (V · U)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-app ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (castᵛ ei V · castᵛ ei U))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-app γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
      castᶜ eo (env-Vˢ γ Δ' (castᵛ ei V) · env-Vˢ γ Δ' (castᵛ ei U))
    ≡⟨ cast-app eo ⟩
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) · castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-app (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V U =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (V · U)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-app ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (castᵛ ei V · castᵛ ei U))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-app γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
    castᶜ eo (env-Vˢ γ Δ' (castᵛ ei V) · env-Vˢ γ Δ' (castᵛ ei U))
  ≡⟨ cast-app eo ⟩
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) · castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-app (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V U =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (V · U)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-app eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᵛ eA V · castᵛ eA U))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-app γ Δ₁ (castᵛ eA V) (castᵛ eA U)) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)
                            · env-Vˢ γ Δ₁ (castᵛ eA U))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-app eIn) ⟩
    sub-atᶜ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))
                 · castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) W
  ≡⟨⟩
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
      · sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) W
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-app (eternalˡ Δ₀ lf η γ) Δ V U =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (V · U)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-app e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (castᵛ e V · castᵛ e U))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-app lf η (castᵛ e V) (castᵛ e U)) ⟩
    env-Cˢ γ Δ (env-eternal-V lf η (castᵛ e V) · env-eternal-V lf η (castᵛ e U))
  ≡⟨ env-Cˢ-app γ Δ (env-eternal-V lf η (castᵛ e V)) (env-eternal-V lf η (castᵛ e U)) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V)) · env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e U))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Cˢ-if : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
          → (V : (Γ ++ᶜ Δ) ⊢V⦂ Bool) → (M N : (Γ ++ᶜ Δ) ⊢C⦂ C)
          → env-Cˢ γ Δ (if V `then M `else N)
          ≡ if (env-Vˢ γ Δ V) `then (env-Cˢ γ Δ M) `else (env-Cˢ γ Δ N)

env-Cˢ-if ⌊ St ⌋ Δ V M N = refl
env-Cˢ-if (∅ᵉ St) Δ V M N = refl
env-Cˢ-if (reachᵉ γ q) Δ V M N =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-if γ Δ V M N)

env-Cˢ-if (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (if V `then M `else N)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-if ei) ⟩
      castᶜ eo (env-Cˢ γ Δ'
        (if castᵛ ei V `then castᶜ ei M `else castᶜ ei N))
    ≡⟨ cong (castᶜ eo)
            (env-Cˢ-if γ Δ' (castᵛ ei V) (castᶜ ei M) (castᶜ ei N)) ⟩
      castᶜ eo (if env-Vˢ γ Δ' (castᵛ ei V)
                 `then env-Cˢ γ Δ' (castᶜ ei M)
                 `else env-Cˢ γ Δ' (castᶜ ei N))
    ≡⟨ cast-if eo ⟩
      if castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
        `then castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
        `else castᶜ eo (env-Cˢ γ Δ' (castᶜ ei N))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-if (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M N =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (if V `then M `else N)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-if ei) ⟩
    castᶜ eo (env-Cˢ γ Δ'
      (if castᵛ ei V `then castᶜ ei M `else castᶜ ei N))
  ≡⟨ cong (castᶜ eo)
          (env-Cˢ-if γ Δ' (castᵛ ei V) (castᶜ ei M) (castᶜ ei N)) ⟩
    castᶜ eo (if env-Vˢ γ Δ' (castᵛ ei V)
               `then env-Cˢ γ Δ' (castᶜ ei M)
               `else env-Cˢ γ Δ' (castᶜ ei N))
  ≡⟨ cast-if eo ⟩
    if castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
      `then castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
      `else castᶜ eo (env-Cˢ γ Δ' (castᶜ ei N))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-if (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M N =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (if V `then M `else N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-if eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
      (if castᵛ eA V `then castᶜ eA M `else castᶜ eA N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-if γ Δ₁ (castᵛ eA V) (castᶜ eA M) (castᶜ eA N)) ⟩
    sub-atᶜ Δ (castᶜ eIn (if env-Vˢ γ Δ₁ (castᵛ eA V)
                           `then env-Cˢ γ Δ₁ (castᶜ eA M)
                           `else env-Cˢ γ Δ₁ (castᶜ eA N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-if eIn) ⟩
    sub-atᶜ Δ (if castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))
                `then castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))
                `else castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA N))) W
  ≡⟨⟩
    if sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
      `then sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W
      `else sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA N))) W
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-if (eternalˡ Δ₀ lf η γ) Δ V M N =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (if V `then M `else N)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-if e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η
      (if castᵛ e V `then castᶜ e M `else castᶜ e N))
  ≡⟨ cong (env-Cˢ γ Δ)
          (env-eternal-if lf η (castᵛ e V) (castᶜ e M) (castᶜ e N)) ⟩
    env-Cˢ γ Δ (if env-eternal-V lf η (castᵛ e V)
                 `then env-eternal-C lf η (castᶜ e M)
                 `else env-eternal-C lf η (castᶜ e N))
  ≡⟨ env-Cˢ-if γ Δ (env-eternal-V lf η (castᵛ e V))
                   (env-eternal-C lf η (castᶜ e M))
                   (env-eternal-C lf η (castᶜ e N)) ⟩
    if env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))
      `then env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M))
      `else env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e N))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Cˢ-coerce : ∀ {St Γ A ε ε'} → (γ : Env St Γ) → (Δ : Ctx) → {p : ε ≾ₑ ε'}
              → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ‼ ε)
              → env-Cˢ γ Δ (coerce p M) ≡ coerce p (env-Cˢ γ Δ M)

env-Cˢ-coerce ⌊ St ⌋ Δ M = refl
env-Cˢ-coerce (∅ᵉ St) Δ M = refl
env-Cˢ-coerce (reachᵉ γ q) Δ M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-coerce γ Δ M)

env-Cˢ-coerce (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (coerce _ (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-coerce ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (coerce _ (castᶜ ei M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-coerce γ Δ' (castᶜ ei M)) ⟩
      castᶜ eo (coerce _ (env-Cˢ γ Δ' (castᶜ ei M)))
    ≡⟨ cast-coerce eo ⟩
      coerce _ (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-coerce (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (coerce _ (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-coerce ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (coerce _ (castᶜ ei M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-coerce γ Δ' (castᶜ ei M)) ⟩
    castᶜ eo (coerce _ (env-Cˢ γ Δ' (castᶜ ei M)))
  ≡⟨ cast-coerce eo ⟩
    coerce _ (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-coerce (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (coerce _ (M))))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-coerce eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (coerce _ (castᶜ eA M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-coerce γ Δ₁ (castᶜ eA M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (coerce _ (env-Cˢ γ Δ₁ (castᶜ eA M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-coerce eIn) ⟩
    sub-atᶜ Δ (coerce _ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M)))) W
  ≡⟨⟩
    coerce _ (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-coerce (eternalˡ Δ₀ lf η γ) Δ M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (coerce _ (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-coerce e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (coerce _ (castᶜ e M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-coerce lf η (castᶜ e M)) ⟩
    env-Cˢ γ Δ (coerce _ (env-eternal-C lf η (castᶜ e M)))
  ≡⟨ env-Cˢ-coerce γ Δ (env-eternal-C lf η (castᶜ e M)) ⟩
    coerce _ (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Vˢ-pair : ∀ {St Γ A B} → (γ : Env St Γ) → (Δ : Ctx)
            → (V : (Γ ++ᶜ Δ) ⊢V⦂ A) → (U : (Γ ++ᶜ Δ) ⊢V⦂ B)
            → env-Vˢ γ Δ ⦉ V , U ⦊ ≡ ⦉ env-Vˢ γ Δ V , env-Vˢ γ Δ U ⦊

env-Vˢ-pair ⌊ St ⌋ Δ V U = refl
env-Vˢ-pair (∅ᵉ St) Δ V U = refl
env-Vˢ-pair (reachᵉ γ q) Δ V U = cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-pair γ Δ V U)

env-Vˢ-pair (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V U =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (⦉ V , U ⦊)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-pair ei) ⟩
      castᵛ eo (env-Vˢ γ Δ' (⦉ castᵛ ei V , castᵛ ei U ⦊))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-pair γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
      castᵛ eo (⦉ env-Vˢ γ Δ' (castᵛ ei V) , env-Vˢ γ Δ' (castᵛ ei U) ⦊)
    ≡⟨ cast-pair eo ⟩
      ⦉ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) , castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U)) ⦊
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-pair (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V U =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (⦉ V , U ⦊)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-pair ei) ⟩
    castᵛ eo (env-Vˢ γ Δ' (⦉ castᵛ ei V , castᵛ ei U ⦊))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-pair γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
    castᵛ eo (⦉ env-Vˢ γ Δ' (castᵛ ei V) , env-Vˢ γ Δ' (castᵛ ei U) ⦊)
  ≡⟨ cast-pair eo ⟩
    ⦉ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) , castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U)) ⦊
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-pair (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V U =
  begin
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (⦉ V , U ⦊)))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ z)) W) (cast-pair eA) ⟩
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (⦉ castᵛ eA V , castᵛ eA U ⦊))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W)
          (env-Vˢ-pair γ Δ₁ (castᵛ eA V) (castᵛ eA U)) ⟩
    sub-atᵛ Δ (castᵛ eIn (⦉ env-Vˢ γ Δ₁ (castᵛ eA V)
                          , env-Vˢ γ Δ₁ (castᵛ eA U) ⦊)) W
  ≡⟨ cong (λ z → sub-atᵛ Δ z W) (cast-pair eIn) ⟩
    sub-atᵛ Δ (⦉ castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))
               , castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U)) ⦊) W
  ≡⟨⟩
    ⦉ sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
    , sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) W ⦊
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Vˢ-pair (eternalˡ Δ₀ lf η γ) Δ V U =
  begin
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e (⦉ V , U ⦊)))
  ≡⟨ cong (λ z → env-Vˢ γ Δ (env-eternal-V lf η z)) (cast-pair e) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (⦉ castᵛ e V , castᵛ e U ⦊))
  ≡⟨ cong (env-Vˢ γ Δ) (env-eternal-pair lf η (castᵛ e V) (castᵛ e U)) ⟩
    env-Vˢ γ Δ (⦉ env-eternal-V lf η (castᵛ e V) , env-eternal-V lf η (castᵛ e U) ⦊)
  ≡⟨ env-Vˢ-pair γ Δ (env-eternal-V lf η (castᵛ e V)) (env-eternal-V lf η (castᵛ e U)) ⟩
    ⦉ env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V)) , env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e U)) ⦊
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

-- THE ACTION COMMUTES WITH THE BINDING FORMERS
--
-- The body sits at an extended suffix, so the two sides carry casts along
-- different (but equal) proofs, reconciled by `castᶜ-irr`.

env-eternal-delay : ∀ {Δ Γ A ε τ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                  → (M : (Δ ++ᶜ Γ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                  → env-eternal-C lf η (delay τ M)
                  ≡ delay τ (env-eternal-C lf η M)
env-eternal-delay {τ = τ} lf-[] η M =
  trans (cast-delay ++ᶜ-identityˡ)
        (cong (delay τ)
          (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))
env-eternal-delay {Δ ∷ B} {Γ} {τ = τ} (lf-∷ lf) η M =
  env-eternal-delay lf (λ v → η (Tl-∷ v))
    (sub-atᶜ (Γ ⟨ of-natʳ τ ⟩) M (V-rename (empty-ren lf) (η Hd)))

env-Cˢ-delay : ∀ {St Γ A ε τ} → (γ : Env St Γ) → (Δ : Ctx)
             → (M : (Γ ++ᶜ Δ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
             → env-Cˢ γ Δ (delay τ M) ≡ delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩) M)

env-Cˢ-delay ⌊ St ⌋ Δ M = refl
env-Cˢ-delay (∅ᵉ St) Δ M = refl
env-Cˢ-delay (reachᵉ γ q) Δ M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-delay γ Δ M)

env-Cˢ-delay {τ = τ} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ'} γ q) Δ M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (delay τ M)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-delay ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-delay γ Δ' (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)) ⟩
      castᶜ eo (delay τ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩)
                          (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cast-delay eo ⟩
      delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) eo)
                (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cong (delay τ) (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) eo) eo₂ _) ⟩
      delay τ (castᶜ eo₂
                (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cong (λ z → delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) z)))
            (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) ei) ei₂ M) ⟩
      delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ' ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) (Δ ⟨ of-natʳ τ ⟩))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) (Δ ⟨ of-natʳ τ ⟩)

env-Cˢ-delay {τ = τ} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ'} V₀ γ) Δ M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (delay τ M)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-delay ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-delay γ Δ' (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)) ⟩
    castᶜ eo (delay τ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩)
                        (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cast-delay eo ⟩
    delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) eo)
              (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cong (delay τ) (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) eo) eo₂ _) ⟩
    delay τ (castᶜ eo₂
              (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cong (λ z → delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) z)))
          (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) ei) ei₂ M) ⟩
    delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ' ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ of-natʳ τ ⟩))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ of-natʳ τ ⟩)

env-Cˢ-delay {τ = τ} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (delay τ M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-delay eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (delay τ (castᶜ (exτ eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-delay γ Δ₁ (castᶜ (exτ eA) M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (delay τ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                                    (castᶜ (exτ eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-delay eIn) ⟩
    sub-atᶜ Δ (delay τ (castᶜ (exτ eIn) (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                                          (castᶜ (exτ eA) M)))) W
  ≡⟨ cong (λ z → delay τ (sub-atᶜ (Δ ⟨ of-natʳ τ ⟩) z W))
          (castᶜ-irr (exτ eIn) eIn₂ _) ⟩
    delay τ (sub-atᶜ (Δ ⟨ of-natʳ τ ⟩)
               (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                             (castᶜ (exτ eA) M))) W)
  ≡⟨ cong (λ z → delay τ (sub-atᶜ (Δ ⟨ of-natʳ τ ⟩)
             (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩) z)) W))
          (castᶜ-irr (exτ eA) eA₂ M) ⟩
    delay τ (sub-atᶜ (Δ ⟨ of-natʳ τ ⟩)
               (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩) (castᶜ eA₂ M))) W)
  ∎
  where
    exτ   = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong (_⟨ of-natʳ τ ⟩) e
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ of-natʳ τ ⟩))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ of-natʳ τ ⟩)

env-Cˢ-delay {τ = τ} (eternalˡ Δ₀ lf η γ) Δ M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (delay τ M)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-delay e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)))
  ≡⟨ cong (env-Cˢ γ Δ)
          (env-eternal-delay lf η (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)) ⟩
    env-Cˢ γ Δ (delay τ (env-eternal-C lf η
                          (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)))
  ≡⟨ env-Cˢ-delay γ Δ (env-eternal-C lf η (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)) ⟩
    delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩)
              (env-eternal-C lf η (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)))
  ≡⟨ cong (λ z → delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩) (env-eternal-C lf η z)))
          (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) e) e₂ M) ⟩
    delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩) (env-eternal-C lf η (castᶜ e₂ M)))
  ∎
  where
    e  = ++ᶜ-assoc Δ₀ _ Δ
    e₂ = ++ᶜ-assoc Δ₀ _ (Δ ⟨ of-natʳ τ ⟩)

env-eternal-seq : ∀ {Δ Γ A B ε ε'} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (M : (Δ ++ᶜ Γ) ⊢C⦂ A ‼ ε)
                → (N : (Δ ++ᶜ Γ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
                → env-eternal-C lf η (M ⨟ N)
                ≡ (env-eternal-C lf η M) ⨟ (env-eternal-C lf η N)

env-eternal-seq {A = A} {ε = ε} lf-[] η M N =
  trans (cast-seq ++ᶜ-identityˡ)
        (cong ((castᶜ ++ᶜ-identityˡ M) ⨟_)
          (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) ++ᶜ-identityˡ)
                     ++ᶜ-identityˡ N))

env-eternal-seq {Δ ∷ B₀} {Γ} {A} {ε = ε} (lf-∷ lf) η M N =
  env-eternal-seq lf (λ v → η (Tl-∷ v))
    (sub-atᶜ Γ M W) (sub-atᶜ (Γ ⟨ mapᵉ ε ⟩ ∷ A) N W)
  where
    W = V-rename (empty-ren lf) (η Hd)

env-Cˢ-seq : ∀ {St Γ A B ε ε'} → (γ : Env St Γ) → (Δ : Ctx)
           → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ‼ ε)
           → (N : (Γ ++ᶜ Δ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
           → env-Cˢ γ Δ (M ⨟ N)
           ≡ (env-Cˢ γ Δ M) ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) N)

env-Cˢ-seq ⌊ St ⌋ Δ M N = refl
env-Cˢ-seq (∅ᵉ St) Δ M N = refl
env-Cˢ-seq (reachᵉ γ q) Δ M N = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-seq γ Δ M N)

env-Cˢ-seq {A = A} {ε = ε} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (M ⨟ N)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-seq ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' ((castᶜ ei M) ⨟ (castᶜ (exε ei) N)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-seq γ Δ' (castᶜ ei M) (castᶜ (exε ei) N)) ⟩
      castᶜ eo ((env-Cˢ γ Δ' (castᶜ ei M))
                  ⨟ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cast-seq eo ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ (exε eo) (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cong ((castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) ⨟_)
            (castᶜ-irr (exε eo) eo₂ _) ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cong (λ z → (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
                     ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) z)))
            (castᶜ-irr (exε ei) ei₂ N) ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ ei₂ N)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ M N =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (M ⨟ N)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-seq ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' ((castᶜ ei M) ⨟ (castᶜ (exε ei) N)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-seq γ Δ' (castᶜ ei M) (castᶜ (exε ei) N)) ⟩
    castᶜ eo ((env-Cˢ γ Δ' (castᶜ ei M))
                ⨟ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cast-seq eo ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ (exε eo) (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cong ((castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) ⨟_)
          (castᶜ-irr (exε eo) eo₂ _) ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cong (λ z → (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
                   ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) z)))
          (castᶜ-irr (exε ei) ei₂ N) ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ ei₂ N)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M N =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (M ⨟ N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-seq eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ ((castᶜ eA M) ⨟ (castᶜ (exε eA) N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-seq γ Δ₁ (castᶜ eA M) (castᶜ (exε eA) N)) ⟩
    sub-atᶜ Δ (castᶜ eIn ((env-Cˢ γ Δ₁ (castᶜ eA M))
                           ⨟ (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A)
                                (castᶜ (exε eA) N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-seq eIn) ⟩
    sub-atᶜ Δ ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M)))
                 ⨟ (castᶜ (exε eIn) (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A)
                                      (castᶜ (exε eA) N)))) W
  ≡⟨ cong (λ z → (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
                   ⨟ (sub-atᶜ (Δ ⟨ mapᵉ ε ⟩ ∷ A) z W))
          (castᶜ-irr (exε eIn) eIn₂ _) ⟩
    (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
      ⨟ (sub-atᶜ (Δ ⟨ mapᵉ ε ⟩ ∷ A)
           (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε eA) N))) W)
  ≡⟨ cong (λ z → (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
                   ⨟ (sub-atᶜ (Δ ⟨ mapᵉ ε ⟩ ∷ A)
                        (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) z)) W))
          (castᶜ-irr (exε eA) eA₂ N) ⟩
    (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
      ⨟ (sub-atᶜ (Δ ⟨ mapᵉ ε ⟩ ∷ A)
           (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ eA₂ N))) W)
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (eternalˡ Δ₀ lf η γ) Δ M N =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (M ⨟ N)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-seq e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η ((castᶜ e M) ⨟ (castᶜ (exε e) N)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-seq lf η (castᶜ e M) (castᶜ (exε e) N)) ⟩
    env-Cˢ γ Δ ((env-eternal-C lf η (castᶜ e M))
                  ⨟ (env-eternal-C lf η (castᶜ (exε e) N)))
  ≡⟨ env-Cˢ-seq γ Δ (env-eternal-C lf η (castᶜ e M))
                    (env-eternal-C lf η (castᶜ (exε e) N)) ⟩
    (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
      ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) (env-eternal-C lf η (castᶜ (exε e) N)))
  ≡⟨ cong (λ z → (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
                   ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) (env-eternal-C lf η z)))
          (castᶜ-irr (exε e) e₂ N) ⟩
    (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
      ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) (env-eternal-C lf η (castᶜ e₂ N)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    e₂  = ++ᶜ-assoc Δ₀ _ (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-eternal-perform : ∀ {Δ Γ A ε} {op : Op} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ type-of-gtype (param op))
                → (M : (Δ ++ᶜ Γ) ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                → env-eternal-C lf η (perform op (V) (M))
                ≡ perform op (env-eternal-V lf η V) (env-eternal-C lf η M)

env-eternal-perform {op = op} lf-[] η V M =
  trans (cast-perform ++ᶜ-identityˡ)
        (cong (λ z → perform op (castᵛ ++ᶜ-identityˡ V) (z))
          (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))

env-eternal-perform {Δ ∷ B₀} {Γ} {op = op} (lf-∷ lf) η V M =
  env-eternal-perform lf (λ v → η (Tl-∷ v))
    (sub-atᵛ Γ V W)
    (sub-atᶜ (Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) M W)
  where
    W = V-rename (empty-ren lf) (η Hd)

env-Cˢ-perform : ∀ {St Γ A ε} {op : Op} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ type-of-gtype (param op))
           → (M : (Γ ++ᶜ Δ) ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
           → env-Cˢ γ Δ (perform op (V) (M))
           ≡ perform op (env-Vˢ γ Δ V) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) M)

env-Cˢ-perform ⌊ St ⌋ Δ V M = refl
env-Cˢ-perform (∅ᵉ St) Δ V M = refl
env-Cˢ-perform (reachᵉ γ q) Δ V M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-perform γ Δ V M)

env-Cˢ-perform {op = op} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (perform op (V) (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-perform ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (perform op (castᵛ ei V) (castᶜ (exf ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-perform γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
      castᶜ eo (perform op (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
    ≡⟨ cast-perform eo ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ (exf eo) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (z))
            (castᶜ-irr (exf eo) eo₂ _) ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) z)))
            (castᶜ-irr (exf ei) ei₂ M) ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-Cˢ-perform {op = op} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (perform op (V) (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-perform ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (perform op (castᵛ ei V) (castᶜ (exf ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-perform γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
    castᶜ eo (perform op (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
  ≡⟨ cast-perform eo ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ (exf eo) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (z))
          (castᶜ-irr (exf eo) eo₂ _) ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) z)))
          (castᶜ-irr (exf ei) ei₂ M) ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-Cˢ-perform {op = op} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (perform op (V) (M))))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-perform eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (perform op (castᵛ eA V) (castᶜ (exf eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-perform γ Δ₁ (castᵛ eA V) (castᶜ (exf eA) M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (perform op (env-Vˢ γ Δ₁ (castᵛ eA V))
                            (env-Cˢ γ Δ₂ (castᶜ (exf eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-perform eIn) ⟩
    sub-atᶜ Δ (perform op (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))
                 (castᶜ (exf eIn) (env-Cˢ γ Δ₂ (castᶜ (exf eA) M)))) W
  ≡⟨ cong (λ z → perform op (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
                    (sub-atᶜ Δ₃ z W))
          (castᶜ-irr (exf eIn) eIn₂ _) ⟩
    perform op (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
      (sub-atᶜ Δ₃ (castᶜ eIn₂ (env-Cˢ γ Δ₂ (castᶜ (exf eA) M))) W)
  ≡⟨ cong (λ z → perform op (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
                    (sub-atᶜ Δ₃ (castᶜ eIn₂ (env-Cˢ γ Δ₂ z)) W))
          (castᶜ-irr (exf eA) eA₂ M) ⟩
    perform op (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
      (sub-atᶜ Δ₃ (castᶜ eIn₂ (env-Cˢ γ Δ₂ (castᶜ eA₂ M))) W)
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    Δ₂    = Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
    Δ₃    = Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-Cˢ-perform {op = op} (eternalˡ Δ₀ lf η γ) Δ V M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (perform op (V) (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-perform e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (perform op (castᵛ e V) (castᶜ (exf e) M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-perform lf η (castᵛ e V) (castᶜ (exf e) M)) ⟩
    env-Cˢ γ Δ (perform op (env-eternal-V lf η (castᵛ e V)) (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ env-Cˢ-perform γ Δ (env-eternal-V lf η (castᵛ e V))
                    (env-eternal-C lf η (castᶜ (exf e) M)) ⟩
    perform op (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ cong (λ z → perform op (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (env-eternal-C lf η z)))
          (castᶜ-irr (exf e) e₂ M) ⟩
    perform op (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (env-eternal-C lf η (castᶜ e₂ M)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    e₂  = ++ᶜ-assoc Δ₀ _ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-eternal-match : ∀ {Δ Γ A B C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ A |×| B)
                → (M : (Δ ++ᶜ Γ) ∷ A ∷ B ⊢C⦂ C)
                → env-eternal-C lf η (match (V) `in (M))
                ≡ match (env-eternal-V lf η V) `in (env-eternal-C lf η M)

env-eternal-match {A = A} {B = B} lf-[] η V M =
  trans (cast-match ++ᶜ-identityˡ)
        (cong (λ z → match (castᵛ ++ᶜ-identityˡ V) `in (z))
          (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))

env-eternal-match {Δ ∷ B₀} {Γ} {A = A} {B = B} (lf-∷ lf) η V M =
  env-eternal-match lf (λ v → η (Tl-∷ v))
    (sub-atᵛ Γ V W) (sub-atᶜ (Γ ∷ A ∷ B) M W)
  where
    W = V-rename (empty-ren lf) (η Hd)

env-Cˢ-match : ∀ {St Γ A B C} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A |×| B)
           → (M : (Γ ++ᶜ Δ) ∷ A ∷ B ⊢C⦂ C)
           → env-Cˢ γ Δ (match (V) `in (M))
           ≡ match (env-Vˢ γ Δ V) `in (env-Cˢ γ (Δ ∷ A ∷ B) M)

env-Cˢ-match ⌊ St ⌋ Δ V M = refl
env-Cˢ-match (∅ᵉ St) Δ V M = refl
env-Cˢ-match (reachᵉ γ q) Δ V M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-match γ Δ V M)

env-Cˢ-match {A = A} {B = B} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (match (V) `in (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-match ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (match (castᵛ ei V) `in (castᶜ (exf ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-match γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
      castᶜ eo (match (env-Vˢ γ Δ' (castᵛ ei V)) `in (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
    ≡⟨ cast-match eo ⟩
      match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ (exf eo) (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (z))
            (castᶜ-irr (exf eo) eo₂ _) ⟩
      match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) z)))
            (castᶜ-irr (exf ei) ei₂ M) ⟩
      match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ A ∷ B))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ A ∷ B)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-Cˢ-match {A = A} {B = B} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (match (V) `in (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-match ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (match (castᵛ ei V) `in (castᶜ (exf ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-match γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
    castᶜ eo (match (env-Vˢ γ Δ' (castᵛ ei V)) `in (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
  ≡⟨ cast-match eo ⟩
    match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ (exf eo) (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (z))
          (castᶜ-irr (exf eo) eo₂ _) ⟩
    match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) z)))
          (castᶜ-irr (exf ei) ei₂ M) ⟩
    match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ A ∷ B))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ∷ A ∷ B)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-Cˢ-match {A = A} {B = B} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (match (V) `in (M))))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-match eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (match (castᵛ eA V) `in (castᶜ (exf eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-match γ Δ₁ (castᵛ eA V) (castᶜ (exf eA) M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (match (env-Vˢ γ Δ₁ (castᵛ eA V))
                            `in (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-match eIn) ⟩
    sub-atᶜ Δ (match (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))
                 `in (castᶜ (exf eIn)
                        (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M)))) W
  ≡⟨ cong (λ z → match (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
                   `in (sub-atᶜ (Δ ∷ A ∷ B) z W))
          (castᶜ-irr (exf eIn) eIn₂ _) ⟩
    match (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
      `in (sub-atᶜ (Δ ∷ A ∷ B)
             (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M))) W)
  ≡⟨ cong (λ z → match (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
                   `in (sub-atᶜ (Δ ∷ A ∷ B)
                          (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ∷ A ∷ B) z)) W))
          (castᶜ-irr (exf eA) eA₂ M) ⟩
    match (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
      `in (sub-atᶜ (Δ ∷ A ∷ B)
             (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ eA₂ M))) W)
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A ∷ B))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ A ∷ B)
    exf   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-Cˢ-match {A = A} {B = B} (eternalˡ Δ₀ lf η γ) Δ V M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (match (V) `in (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-match e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (match (castᵛ e V) `in (castᶜ (exf e) M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-match lf η (castᵛ e V) (castᶜ (exf e) M)) ⟩
    env-Cˢ γ Δ (match (env-eternal-V lf η (castᵛ e V)) `in (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ env-Cˢ-match γ Δ (env-eternal-V lf η (castᵛ e V))
                    (env-eternal-C lf η (castᶜ (exf e) M)) ⟩
    match (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) `in (env-Cˢ γ (Δ ∷ A ∷ B) (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ cong (λ z → match (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) `in (env-Cˢ γ (Δ ∷ A ∷ B) (env-eternal-C lf η z)))
          (castᶜ-irr (exf e) e₂ M) ⟩
    match (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) `in (env-Cˢ γ (Δ ∷ A ∷ B) (env-eternal-C lf η (castᶜ e₂ M)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    e₂  = ++ᶜ-assoc Δ₀ _ (Δ ∷ A ∷ B)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-eternal-box : ∀ {Δ Γ A C ρ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⟨ ρ ⟩ ⊢V⦂ A)
                → (M : (Δ ++ᶜ Γ) ∷ [ ρ ] A ⊢C⦂ C)
                → env-eternal-C lf η (box V M)
                ≡ box (env-eternal-V lf η V) (env-eternal-C lf η M)

env-eternal-box {A = A} {ρ = ρ} lf-[] η V M =
  trans (cast-box ++ᶜ-identityˡ)
        (trans (cong (λ z → box z (castᶜ (cong (_∷ [ ρ ] A) ++ᶜ-identityˡ) M))
                 (castᵛ-irr (cong (_⟨ ρ ⟩) ++ᶜ-identityˡ) ++ᶜ-identityˡ V))
               (cong (λ z → box (castᵛ ++ᶜ-identityˡ V) z)
                 (castᶜ-irr (cong (_∷ [ ρ ] A) ++ᶜ-identityˡ) ++ᶜ-identityˡ M)))

env-eternal-box {Δ ∷ B₀} {Γ} {A = A} {ρ = ρ} (lf-∷ lf) η V M =
  env-eternal-box lf (λ v → η (Tl-∷ v))
    (sub-atᵛ (Γ ⟨ ρ ⟩) V W) (sub-atᶜ (Γ ∷ [ ρ ] A) M W)
  where
    W = V-rename (empty-ren lf) (η Hd)

env-Cˢ-box : ∀ {St Γ A C ρ} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⟨ ρ ⟩ ⊢V⦂ A)
           → (M : (Γ ++ᶜ Δ) ∷ [ ρ ] A ⊢C⦂ C)
           → env-Cˢ γ Δ (box V M)
           ≡ box (env-Vˢ γ (Δ ⟨ ρ ⟩) V) (env-Cˢ γ (Δ ∷ [ ρ ] A) M)

env-Cˢ-box ⌊ St ⌋ Δ V M = refl
env-Cˢ-box (∅ᵉ St) Δ V M = refl
env-Cˢ-box (reachᵉ γ q) Δ V M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-box γ Δ V M)

env-Cˢ-box {A = A} {ρ = ρ} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ'} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (box (V) (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-box ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (box (castᵛ (exV ei) V) (castᶜ (exM ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-box γ Δ' (castᵛ (exV ei) V) (castᶜ (exM ei) M)) ⟩
      castᶜ eo (box (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V)) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cast-box eo ⟩
      box (castᵛ (exV eo) (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (z) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
            (castᵛ-irr (exV eo) eoV₂ _) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (z))
            (castᶜ-irr (exM eo) eoM₂ _) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) z)) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
            (castᵛ-irr (exV ei) eiV₂ V) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) z)))
            (castᶜ-irr (exM ei) eiM₂ M) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ eiM₂ M)))
     ∎)
  where
    Δ'   = [] ⟨ ρ' ⟩ ++ᶜ Δ
    eo   = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) Δ)
    ei   = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) Δ
    eoV₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) (Δ ⟨ ρ ⟩))
    eoM₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) (Δ ∷ [ ρ ] A))
    eiV₂ = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) (Δ ⟨ ρ ⟩)
    eiM₂ = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) (Δ ∷ [ ρ ] A)
    exV  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

env-Cˢ-box {A = A} {ρ = ρ} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ'} V₀ γ) Δ V M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (box (V) (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-box ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (box (castᵛ (exV ei) V) (castᶜ (exM ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-box γ Δ' (castᵛ (exV ei) V) (castᶜ (exM ei) M)) ⟩
    castᶜ eo (box (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V)) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cast-box eo ⟩
    box (castᵛ (exV eo) (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (z) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
          (castᵛ-irr (exV eo) eoV₂ _) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (z))
          (castᶜ-irr (exM eo) eoM₂ _) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) z)) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
          (castᵛ-irr (exV ei) eiV₂ V) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) z)))
          (castᶜ-irr (exM ei) eiM₂ M) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ eiM₂ M)))
   ∎
  where
    Δ₁   = [] ∷ [ ρ' ] A₀
    Δ'   = Δ₁ ++ᶜ Δ
    eo   = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei   = ++ᶜ-assoc Γ Δ₁ Δ
    eoV₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ ρ ⟩))
    eoM₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ [ ρ ] A))
    eiV₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ ρ ⟩)
    eiM₂ = ++ᶜ-assoc Γ Δ₁ (Δ ∷ [ ρ ] A)
    exV  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

env-Cˢ-box {A = A} {ρ = ρ} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (box (V) (M))))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-box eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (box (castᵛ (exV eA) V) (castᶜ (exM eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-box γ Δ₁ (castᵛ (exV eA) V) (castᶜ (exM eA) M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (box (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))
                            (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-box eIn) ⟩
    sub-atᶜ Δ (box (castᵛ (exV eIn) (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V)))
                 (castᶜ (exM eIn)
                    (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M)))) W
  ≡⟨ cong (λ z → box (sub-atᵛ (Δ ⟨ ρ ⟩) z W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A)
                      (castᶜ (exM eIn)
                         (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W))
          (castᵛ-irr (exV eIn) eInV₂ _) ⟩
    box (sub-atᵛ (Δ ⟨ ρ ⟩)
           (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) W)
      (sub-atᶜ (Δ ∷ [ ρ ] A)
         (castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W)
  ≡⟨ cong (λ z → box (sub-atᵛ (Δ ⟨ ρ ⟩)
                        (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A) z W))
          (castᶜ-irr (exM eIn) eInM₂ _) ⟩
    box (sub-atᵛ (Δ ⟨ ρ ⟩)
           (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) W)
      (sub-atᶜ (Δ ∷ [ ρ ] A)
         (castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W)
  ≡⟨ cong (λ z → box (sub-atᵛ (Δ ⟨ ρ ⟩)
                        (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) z)) W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A)
                      (castᶜ eInM₂
                         (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W))
          (castᵛ-irr (exV eA) eAV₂ V) ⟩
    box (sub-atᵛ (Δ ⟨ ρ ⟩)
           (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) W)
      (sub-atᶜ (Δ ∷ [ ρ ] A)
         (castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W)
  ≡⟨ cong (λ z → box (sub-atᵛ (Δ ⟨ ρ ⟩)
                        (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A)
                      (castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) z)) W))
          (castᶜ-irr (exM eA) eAM₂ M) ⟩
    box (sub-atᵛ (Δ ⟨ ρ ⟩)
           (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) W)
      (sub-atᶜ (Δ ∷ [ ρ ] A)
         (castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ eAM₂ M))) W)
  ∎
  where
    Δ₁     = [] ∷ A₀ ++ᶜ Δ
    eIn    = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eInV₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ ρ ⟩))
    eInM₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ [ ρ ] A))
    eA     = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eAV₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ ρ ⟩)
    eAM₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ [ ρ ] A)
    exV    = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM    = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

env-Cˢ-box {A = A} {ρ = ρ} (eternalˡ Δ₀ lf η γ) Δ V M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (box (V) (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-box e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (box (castᵛ (exV e) V) (castᶜ (exM e) M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-box lf η (castᵛ (exV e) V) (castᶜ (exM e) M)) ⟩
    env-Cˢ γ Δ (box (env-eternal-V lf η (castᵛ (exV e) V)) (env-eternal-C lf η (castᶜ (exM e) M)))
  ≡⟨ env-Cˢ-box γ Δ (env-eternal-V lf η (castᵛ (exV e) V)) (env-eternal-C lf η (castᶜ (exM e) M)) ⟩
    box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ (exV e) V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ (exM e) M)))
  ≡⟨ cong (λ z → box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η z)) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ (exM e) M))))
          (castᵛ-irr (exV e) eV₂ V) ⟩
    box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ eV₂ V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ (exM e) M)))
  ≡⟨ cong (λ z → box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ eV₂ V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η z)))
          (castᶜ-irr (exM e) eM₂ M) ⟩
    box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ eV₂ V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ eM₂ M)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    eV₂ = ++ᶜ-assoc Δ₀ _ (Δ ⟨ ρ ⟩)
    eM₂ = ++ᶜ-assoc Δ₀ _ (Δ ∷ [ ρ ] A)
    exV = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

-- The action, at the empty suffix.

env-V : ∀ {St Γ A} → Env St Γ → Γ ⊢V⦂ A → toCtx St ⊢V⦂ A
env-V γ V = env-Vˢ γ [] V

env-C : ∀ {St Γ C} → Env St Γ → Γ ⊢C⦂ C → toCtx St ⊢C⦂ C
env-C γ M = env-Cˢ γ [] M

env-C-id : ∀ {St C} → (M : toCtx St ⊢C⦂ C) → env-C ⌊ St ⌋ M ≡ M
env-C-id M = refl

------------------------------------------------------------------------
-- CLAUSE FAMILIES AND THE ETERNAL ZONE
------------------------------------------------------------------------

-- The action commutes with substituting a telescope entry, definitionally:
-- at the empty suffix every cast is `refl` (`++ᶜ-assoc Γ Γ' []` is, and so is
-- `cong₂ _++ᶜ_ refl refl`) and the variable is `Hd`.

env-Cˢ-head : ∀ {St Γ A C} → (γ : Env St Γ) → (M : Γ ∷ A ⊢C⦂ C)
            → (W : toCtx St ⊢V⦂ A)
            → (env-Cˢ γ ([] ∷ A) M) [ split-[] ↦ W ]c ≡ env-C (γ ∷ᵉ W) M
env-Cˢ-head γ M W = refl

-- The eternal zone's own action on a clause family: each of its substitutions
-- reaches the clauses through `_[_↦_]cl`, as `_∷ᵉ_`'s does.

env-eternal-H : ∀ {Δ Γ B} → (lf : Lock-free Δ) → ClosedVals Δ
              → Fam B ((Δ ++ᶜ Γ) ᴱ) → Fam B (Γ ᴱ)

env-eternal-H {Γ = Γ} {B = B} lf-[] η K op ε =
  Cl-cast op ε (++ᶜ-identityˡ {Γ}) (K op ε)

env-eternal-H {Δ ∷ B₀} {Γ} {B} (lf-∷ lf) η K =
  env-eternal-H {Δ} {Γ} {B} lf (λ x → η (Tl-∷ x))
    (sub-atᴴ Γ K (V-rename (empty-ren lf) (η Hd)))

-- Hence the eternal zone commutes with `handle`: `env-eternal-C`'s two clauses
-- against `cast-handle`, whose clause transport is `Cl-cast` on the nose.

env-eternal-handle : ∀ {Δ Γ A B ε ε'} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                   → (M : (Δ ++ᶜ Γ) ⊢C⦂ A ‼ ε)
                   → (H : Fam B ((Δ ++ᶜ Γ) ᴱ))
                   → (N : (Δ ++ᶜ Γ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
                   → env-eternal-C lf η (handle M `with H `in N)
                   ≡ handle (env-eternal-C lf η M)
                      `with env-eternal-H {Δ} {Γ} {B} lf η H
                      `in (env-eternal-C {Γ = Γ ⟨ mapᵉ ε ⟩ ∷ A} lf η N)

env-eternal-handle {Γ = Γ} {A = A} {ε = ε} lf-[] η M H N =
  trans (cast-handle (++ᶜ-identityˡ {Γ}))
        (cong (λ z → handle (castᶜ ++ᶜ-identityˡ M)
                      `with env-eternal-H {[]} {Γ} lf-[] η H `in z)
              (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) (++ᶜ-identityˡ {Γ}))
                         (++ᶜ-identityˡ {Γ ⟨ mapᵉ ε ⟩ ∷ A}) N))

env-eternal-handle {Δ ∷ B₀} {Γ} {A = A} {ε = ε} (lf-∷ lf) η M H N =
  env-eternal-handle lf (λ x → η (Tl-∷ x))
    (sub-atᶜ Γ M W) (sub-atᴴ Γ H W) (sub-atᶜ (Γ ⟨ mapᵉ ε ⟩ ∷ A) N W)
  where
    W = V-rename (empty-ren lf) (η Hd)

-- THE ACTION ON A CLAUSE FAMILY
--
-- A handler's clauses close over the *eternal* part of the context, so the
-- action reaches them restricted: each zone contributes `restrict-ren` of its
-- own renaming, or — at the substituting zones — `_[_↦_]cl`, which is why this
-- is stated on a whole family rather than one clause. There is no closed form
-- for it in terms of `env-Cˢ`: `env-clause γ St` will not do, its action landing
-- over `toCtx St` where the `handle` former wants `(Γ ++ᶜ Δ) ᴱ`.

env-Hˢ : ∀ {St Γ B} → (γ : Env St Γ) → (Δ : Ctx)
       → Fam B ((Γ ++ᶜ Δ) ᴱ) → Fam B ((toCtx St ++ᶜ Δ) ᴱ)

env-Hˢ ⌊ St ⌋ Δ K = K

env-Hˢ (∅ᵉ St) Δ K op ε =
  C-rename (cong-∷-ren (cong-∷-ren
             (restrict-ren (cong-ren {Γ'' = Δ} (∅-ren St))))) (K op ε)

env-Hˢ (reachᵉ γ q) Δ K op ε =
  C-rename (cong-∷-ren (cong-∷-ren
             (restrict-ren (cong-ren {Γ'' = Δ} (reach-renᵘ q)))))
    (env-Hˢ γ Δ K op ε)

env-Hˢ {B = B} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ K op ε =
  C-rename (cong-∷-ren (cong-∷-ren
             (restrict-ren (cong-ren {Γ'' = Δ} (unbox-ren q)))))
    (Cl-cast op ε (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))
      (env-Hˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
        (λ op' ε' → Cl-cast op' ε' (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) (K op' ε'))
        op ε))

env-Hˢ {B = B} (liftᵉ {St = St} {Γ = Γ} {A = A} {ρ = ρ} V γ) Δ K op ε =
  Cl-cast op ε (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))
    (env-Hˢ γ ([] ∷ [ ρ ] A ++ᶜ Δ)
      (λ op' ε' → Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) (K op' ε'))
      op ε)

env-Hˢ {B = B} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ K op ε =
  sub-atᴴ Δ
    (λ op' ε' →
       Cl-cast op' ε' (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
         (env-Hˢ γ ([] ∷ A ++ᶜ Δ)
           (λ op'' ε'' → Cl-cast op'' ε'' (++ᶜ-assoc Γ ([] ∷ A) Δ)
                           (K op'' ε''))
           op' ε'))
    W op ε

env-Hˢ {B = B} (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ K op ε =
  env-Hˢ γ Δ
    (λ op' ε' →
       env-eternal-H {Δ₀} {Γ₁ ++ᶜ Δ} {B} lf η
         (λ op'' ε'' → Cl-cast op'' ε'' (++ᶜ-assoc Δ₀ Γ₁ Δ) (K op'' ε''))
         op' ε')
    op ε

-- THE ACTION COMMUTES WITH `handle`
--
-- The last of the structural laws. Its clauses need no eternality dispatch —
-- renaming maps `handle` to `handle` and so does `_[_↦_]c`, the split sitting
-- in `_[_↦_]cl` — and `env-Hˢ`'s transports are `Cl-cast`, which is exactly
-- what `cast-handle` produces, so the two sides meet on the nose.

env-Cˢ-handle : ∀ {St Γ A B ε ε'} → (γ : Env St Γ) → (Δ : Ctx)
              → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ‼ ε)
              → (H : Fam B ((Γ ++ᶜ Δ) ᴱ))
              → (N : (Γ ++ᶜ Δ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
              → env-Cˢ γ Δ (handle M `with H `in N)
              ≡ handle (env-Cˢ γ Δ M)
                 `with env-Hˢ γ Δ H
                 `in (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) N)

env-Cˢ-handle ⌊ St ⌋ Δ M H N = refl
env-Cˢ-handle (∅ᵉ St) Δ M H N = refl
env-Cˢ-handle (reachᵉ γ q) Δ M H N =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-handle γ Δ M H N)

env-Cˢ-handle {A = A} {ε = ε} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M H N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-handle ei))
      (trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' (handle _ `with _ `in z)))
                   (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) ei) ei₂ N))
        (trans (cong (castᶜ eo) (env-Cˢ-handle γ Δ' _ _ _))
          (trans (cast-handle eo)
                 (cong (λ z → handle _ `with _ `in z)
                       (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eo) eo₂ _))))))
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A)

env-Cˢ-handle {A = A} {ε = ε}
              (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ M H N =
  trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-handle ei))
    (trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' (handle _ `with _ `in z)))
                 (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) ei) ei₂ N))
      (trans (cong (castᶜ eo) (env-Cˢ-handle γ Δ' _ _ _))
        (trans (cast-handle eo)
               (cong (λ z → handle _ `with _ `in z)
                     (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eo) eo₂ _)))))
  where
    Δ'  = [] ∷ [ ρ ] A₀ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A₀) Δ)
    ei  = ++ᶜ-assoc Γ ([] ∷ [ ρ ] A₀) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ∷ [ ρ ] A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A)

env-Cˢ-handle {A = A} {B = B} {ε = ε} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M H N =
  trans (cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ' z)) W)
              (cast-handle eA))
    (trans (cong (λ z → sub-atᶜ Δ
                          (castᶜ eIn (env-Cˢ γ Δ' (handle Mi `with Hi `in z))) W)
                 (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eA) eA₂ N))
      (trans (cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
                   (env-Cˢ-handle γ Δ' _ _ _))
        (trans (cong (λ z → sub-atᶜ Δ z W) (cast-handle eIn))
               (cong (λ z → handle (sub-atᶜ Δ (castᶜ eIn Mγ) W)
                             `with sub-atᴴ Δ Hγc W
                             `in (sub-atᶜ (Δ ⟨ mapᵉ ε ⟩ ∷ A) z W))
                     (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eIn)
                                eIn₂ Nγ)))))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eIn₂ = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    eA₂  = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A)

    Mi  = castᶜ eA M
    Hi  = λ op ε₀ → Cl-cast op ε₀ eA (H op ε₀)
    Mγ  = env-Cˢ γ Δ' Mi
    Hγ  = env-Hˢ γ Δ' Hi
    Nγ  = env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ eA₂ N)
    Hγc = λ op ε₀ → Cl-cast op ε₀ eIn (Hγ op ε₀)

env-Cˢ-handle {A = A} {ε = ε} (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ M H N =
  trans (cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-handle eA))
    (trans (cong (λ z → env-Cˢ γ Δ
                          (env-eternal-C lf η (handle _ `with _ `in z)))
                 (castᶜ-irr (cong (λ Γ₁' → Γ₁' ⟨ mapᵉ ε ⟩ ∷ A) eA) eA₂ N))
      (trans (cong (env-Cˢ γ Δ) (env-eternal-handle lf η _ _ _))
             (env-Cˢ-handle γ Δ _ _ _)))
  where
    eA  = ++ᶜ-assoc Δ₀ Γ₁ Δ
    eA₂ = ++ᶜ-assoc Δ₀ Γ₁ (Δ ⟨ mapᵉ ε ⟩ ∷ A)

-- THE ETERNAL RESTRICTION OF AN ENVIRONMENT
--
-- A handler clause closes over `Γ ᴱ` (`Language.agda:153`), so the `handle`
-- case of the fundamental lemma needs closed values for it. They are there:
-- the state contributes nothing (`toCtxᴱ-[]` — cells are box-typed, never
-- eternal), an eternal-typed telescope entry is a value over `toCtx St` of
-- eternal type and so *is* closed (`eternal-val-restrict`), and the eternal
-- prefix already holds closed values.

-- A variable of the eternal restriction comes from the context itself
-- (`∈-ᴱ⁻`, in `Syntax.Renamings.Equivalence`), and every variable of the
-- eternal restriction has eternal type.

ᴱ-eternal : ∀ {A ρ} → (Δ : Ctx) → A ∈[ ρ ] Δ ᴱ → Eternal A
ᴱ-eternal []        x with x
... | ()
ᴱ-eternal (Δ ∷ B)   x with eternal? B
ᴱ-eternal (Δ ∷ B)   Hd       | yes et = et
ᴱ-eternal (Δ ∷ B)   (Tl-∷ y) | yes _  = ᴱ-eternal Δ y
ᴱ-eternal (Δ ∷ B)   x        | no  _  = ᴱ-eternal Δ x
ᴱ-eternal (Δ ⟨ ρ ⟩) x = ᴱ-eternal Δ x

env-ᴱ   : ∀ {St Γ} → (γ : Env St Γ) → ClosedVals (Γ ᴱ)

-- as `ᴱ-lock-free-∷`: the telescope entry's decision is taken as an
-- argument, so a caller that has decided it sees the values reduce
env-ᴱ-∷ : ∀ {St Γ A} → (γ : Env St Γ) → (V : toCtx St ⊢V⦂ A)
        → (d : Dec (Eternal A)) → ClosedVals (ᴱ-∷ (Γ ᴱ) A d)

env-ᴱ-∷ {St = St} γ V (yes et) Hd       =
  castᵛ (toCtxᴱ-[] St) (eternal-val-restrict et V)
env-ᴱ-∷           γ V (yes et) (Tl-∷ y) = env-ᴱ γ y
env-ᴱ-∷           γ V (no ¬et) x        = env-ᴱ γ x


env-ᴱ ⌊ St ⌋ x =
  ⊥-elim (not-in-empty-ctx (subst (λ Γ' → _ ∈[ _ ] Γ') (toCtxᴱ-[] St) x))
env-ᴱ (∅ᵉ St) x = ⊥-elim (not-in-empty-ctx x)
-- a cell's type is a box type, never eternal, so the prefix is unchanged
env-ᴱ (liftᵉ {A = A} {ρ = ρ} V γ) x with eternal? ([ ρ ] A)
... | yes ()
... | no ¬et = env-ᴱ γ x
env-ᴱ (γ ⟨ q ⟩ᵉ) x = env-ᴱ γ x
env-ᴱ (reachᵉ γ q) x = env-ᴱ γ x
env-ᴱ (_∷ᵉ_ {A = A} γ V) = env-ᴱ-∷ γ V (eternal? A)
env-ᴱ (eternalˡ {Γ = Γ} Δ lf η γ) x
  with ∈-++ᶜ-split (Δ ᴱ) (Γ ᴱ) (subst (λ Γ' → _ ∈[ _ ] Γ') (ᴱ-++ᶜ Δ Γ) x)
... | inj₁ (ρ' , y) = η (proj₂ (∈-ᴱ⁻ Δ y))
... | inj₂ y        = env-ᴱ γ y

-- A CLAUSE'S CLOSING ENVIRONMENT, AT ANY STATE
--
-- What `∅ᵉ` is for. A handler clause closes over `Γ ᴱ`, whose values are the
-- closed ones `env-ᴱ` supplies; the state contributes nothing, so its zone is
-- `∅ᵉ` and the reducibility asks for no store. Routing through `⌊ St₁ ⌋` instead
-- would demand `SRed St₁`, for cells the clause cannot mention.

env-clause : ∀ {St Γ} → (γ : Env St Γ) → (St₁ : 𝕊 []) → Env St₁ (Γ ᴱ)
env-clause {Γ = Γ} γ St₁ =
  eternalˡ (Γ ᴱ) (ᴱ-lock-free Γ) (env-ᴱ γ) (∅ᵉ St₁)

env-clause-rel : ∀ {St Γ} → (γ : Env St Γ) → (St₁ : 𝕊 [])
               → Rel-Env (env-clause γ St₁)
env-clause-rel {Γ = Γ} γ St₁ = tt , ᴱ-eternal Γ

-- THE CLAUSE ACTION AGAINST THE CLAUSE ENVIRONMENT
--
-- `env-Hˢ γ Δ` reaches a clause zone by zone, each contributing its own
-- `restrict-ren` or — at the substituting zones — its `_[_↦_]cl`, and the
-- weakening into a state's context comes only afterwards (`Fired`).
-- `env-clause γ St₁` instead substitutes every closed value `env-ᴱ γ` computes
-- and weakens once, at the base. The two agree, and only up to `≡`: lining them
-- up moves each zone's renaming past the substitutions to its right, which
-- `Ren` being unquotiented does not do on the nose.
--
-- It is proved at the end of this module (`env-Hˢ-clause`), on the two
-- developments that go before it there: `sub-swap`, since the `_∷ᵉ_` zone
-- substitutes *after* the zones to its left while `env-eternal-C`
-- substitutes before; and `env-Hˢ-ᴱ`, the state-free core.

-- A state contributes nothing to a restriction, at any suffix.

toCtxᴱ-++ᶜ : (St : 𝕊 []) → (Δ : Ctx) → (toCtx St ++ᶜ Δ) ᴱ ≡ Δ ᴱ
toCtxᴱ-++ᶜ St Δ =
  trans (ᴱ-++ᶜ (toCtx St) Δ)
        (trans (cong (_++ᶜ Δ ᴱ) (toCtxᴱ-[] St)) (++ᶜ-identityˡ {Δ ᴱ}))

-- The weakening `env-clause` ends with, at a suffix.

clause-ren : (St₁ : 𝕊 []) → (Δ : Ctx) → Ren [] (toCtx St₁ ++ᶜ Δ ᴱ) (Δ ᴱ)
clause-ren St₁ Δ =
  eq-ren (sym (++ᶜ-identityˡ {Δ ᴱ})) ∘ʳ cong-ren {Γ'' = Δ ᴱ} (∅-ren St₁)

-- Relocating a clause along an equality of the *restricted* context it is
-- already stated over — `Cl-cast`'s shape, one `_ᴱ` further in.

Cl-castᴿ : ∀ {Γ₀ Γ₀' B} → (op : Op) → (ε : E) → Γ₀ ≡ Γ₀'
         → Cl B op ε Γ₀ → Cl B op ε Γ₀'
Cl-castᴿ {B = B} op ε e X =
  castᶜ (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              e)
        X

------------------------------------------------------------------------
-- FUNCTORIALITY IN THE STATE
--
-- `BOX` steps `⟨St, box V M⟩ ↝ ⟨St ∷ₛ V', M⟩`, so the `box` case of the
-- fundamental lemma must move an environment to the extended state. The term
-- needs no reindexing — `toCtx (St ∷ₛ V) = toCtx St ∷ [ρ]A` is the context the
-- action already produced, and moving the environment is recording the
-- allocation reach.
------------------------------------------------------------------------

