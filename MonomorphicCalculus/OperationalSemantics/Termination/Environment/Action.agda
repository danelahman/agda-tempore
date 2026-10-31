------------------------------------------------------------------------
-- The action of an environment on terms, and its commutation with every former.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (yes; no; ¬_; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Termination.Environment.Action (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import Language.Comparisons using (Cmp)
open import MonomorphicCalculus.Syntax.Contexts      Spec
open import MonomorphicCalculus.Syntax.Terms      Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming      Spec
open import MonomorphicCalculus.Syntax.Substitution  Spec
open import MonomorphicCalculus.Syntax.Types Spec

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
open import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Core Spec


-- Iterated single substitutions, defined under an arbitrary suffix `Δ`. A
-- telescope entry is substituted last, riding along in the suffix until its
-- variable is substituted.

-- The action under a suffix.

env-Vˢ : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢V⦂ A
       → (toCtx St ++ᶜ Δ) ⊢V⦂ A

env-Cˢ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢C⦂ C
       → (toCtx St ++ᶜ Δ) ⊢C⦂ C

env-Vˢ ⌊ St ⌋ Δ V = V
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

env-Cˢ ⌊ St ⌋ Δ M = M
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

-- Commutes with `lam` via `cong-∷-sub` at the suffix `Δ ∷ A`.

env-Vˢ-lam : ∀ {St Γ A B ε} → (γ : Env St Γ) → (Δ : Ctx)
           → (M : (Γ ++ᶜ Δ) ∷ A ⊢C⦂ B ! ε)
           → env-Vˢ γ Δ (lam M) ≡ lam (env-Cˢ γ (Δ ∷ A) M)

env-Vˢ-lam ⌊ St ⌋ Δ M = refl
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

env-Cˢ-ret : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx) → (V : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Cˢ γ Δ (return V) ≡ return (env-Vˢ γ Δ V)

env-Cˢ-ret ⌊ St ⌋ Δ V = refl
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

env-Cˢ-app : ∀ {St Γ A C} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A ⇒ C) → (U : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Cˢ γ Δ (V · U) ≡ (env-Vˢ γ Δ V) · (env-Vˢ γ Δ U)

env-Cˢ-app ⌊ St ⌋ Δ V U = refl
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

env-Cˢ-cmp : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx) → (⋈ : Cmp)
           → (V U : (Γ ++ᶜ Δ) ⊢V⦂ A) → (et : Et A)
           → env-Cˢ γ Δ (cmp ⋈ V U et) ≡ cmp ⋈ (env-Vˢ γ Δ V) (env-Vˢ γ Δ U) et

env-Cˢ-cmp ⌊ St ⌋ Δ ⋈ V U et = refl
env-Cˢ-cmp (reachᵉ γ q) Δ ⋈ V U et =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-cmp γ Δ ⋈ V U et)

env-Cˢ-cmp (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ ⋈ V U et =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (cmp ⋈ V U et)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-cmp ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (cmp ⋈ (castᵛ ei V) (castᵛ ei U) et))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-cmp γ Δ' ⋈ (castᵛ ei V) (castᵛ ei U) et) ⟩
      castᶜ eo (cmp ⋈ (env-Vˢ γ Δ' (castᵛ ei V)) (env-Vˢ γ Δ' (castᵛ ei U)) et)
    ≡⟨ cast-cmp eo ⟩
      cmp ⋈ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
            (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U))) et
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-cmp (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ ⋈ V U et =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (cmp ⋈ V U et)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-cmp ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (cmp ⋈ (castᵛ ei V) (castᵛ ei U) et))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-cmp γ Δ' ⋈ (castᵛ ei V) (castᵛ ei U) et) ⟩
    castᶜ eo (cmp ⋈ (env-Vˢ γ Δ' (castᵛ ei V)) (env-Vˢ γ Δ' (castᵛ ei U)) et)
  ≡⟨ cast-cmp eo ⟩
    cmp ⋈ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
          (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U))) et
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-cmp (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ ⋈ V U et =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (cmp ⋈ V U et)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-cmp eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (cmp ⋈ (castᵛ eA V) (castᵛ eA U) et))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-cmp γ Δ₁ ⋈ (castᵛ eA V) (castᵛ eA U) et) ⟩
    sub-atᶜ Δ (castᶜ eIn (cmp ⋈ (env-Vˢ γ Δ₁ (castᵛ eA V))
                                (env-Vˢ γ Δ₁ (castᵛ eA U)) et)) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-cmp eIn) ⟩
    sub-atᶜ Δ (cmp ⋈ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))
                     (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) et) W
  ≡⟨⟩
    cmp ⋈ (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
          (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) W) et
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-if : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
          → (V : (Γ ++ᶜ Δ) ⊢V⦂ bool) → (M N : (Γ ++ᶜ Δ) ⊢C⦂ C)
          → env-Cˢ γ Δ (if V `then M `else N)
          ≡ if (env-Vˢ γ Δ V) `then (env-Cˢ γ Δ M) `else (env-Cˢ γ Δ N)

env-Cˢ-if ⌊ St ⌋ Δ V M N = refl
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

-- Subsumption commutes with the action at both judgements.

env-Vˢ-sub : ∀ {St Γ A A'} → (γ : Env St Γ) → (Δ : Ctx) → {p : A <:ᵛ A'}
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Vˢ γ Δ (subV V p) ≡ subV (env-Vˢ γ Δ V) p

env-Vˢ-sub ⌊ St ⌋ Δ V = refl
env-Vˢ-sub (reachᵉ γ q) Δ V =
  cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-sub γ Δ V)

env-Vˢ-sub (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (subV V _)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-subV ei) ⟩
      castᵛ eo (env-Vˢ γ Δ' (subV (castᵛ ei V) _))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-sub γ Δ' (castᵛ ei V)) ⟩
      castᵛ eo (subV (env-Vˢ γ Δ' (castᵛ ei V)) _)
    ≡⟨ cast-subV eo ⟩
      subV (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) _
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-sub (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (subV V _)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-subV ei) ⟩
    castᵛ eo (env-Vˢ γ Δ' (subV (castᵛ ei V) _))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-sub γ Δ' (castᵛ ei V)) ⟩
    castᵛ eo (subV (env-Vˢ γ Δ' (castᵛ ei V)) _)
  ≡⟨ cast-subV eo ⟩
    subV (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) _
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-sub (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V =
  begin
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (subV V _)))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ z)) W) (cast-subV eA) ⟩
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (subV (castᵛ eA V) _))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W)
          (env-Vˢ-sub γ Δ₁ (castᵛ eA V)) ⟩
    sub-atᵛ Δ (castᵛ eIn (subV (env-Vˢ γ Δ₁ (castᵛ eA V)) _)) W
  ≡⟨ cong (λ z → sub-atᵛ Δ z W) (cast-subV eIn) ⟩
    sub-atᵛ Δ (subV (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) _) W
  ≡⟨⟩
    subV (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W) _
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-sub : ∀ {St Γ C C'} → (γ : Env St Γ) → (Δ : Ctx) → {p : C <:ᶜ C'}
           → (M : (Γ ++ᶜ Δ) ⊢C⦂ C)
           → env-Cˢ γ Δ (subC M p) ≡ subC (env-Cˢ γ Δ M) p

env-Cˢ-sub ⌊ St ⌋ Δ M = refl
env-Cˢ-sub (reachᵉ γ q) Δ M =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-sub γ Δ M)

env-Cˢ-sub (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (subC M _)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-subC ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (subC (castᶜ ei M) _))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-sub γ Δ' (castᶜ ei M)) ⟩
      castᶜ eo (subC (env-Cˢ γ Δ' (castᶜ ei M)) _)
    ≡⟨ cast-subC eo ⟩
      subC (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) _
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-sub (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (subC M _)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-subC ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (subC (castᶜ ei M) _))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-sub γ Δ' (castᶜ ei M)) ⟩
    castᶜ eo (subC (env-Cˢ γ Δ' (castᶜ ei M)) _)
  ≡⟨ cast-subC eo ⟩
    subC (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) _
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-sub (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (subC M _)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-subC eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (subC (castᶜ eA M) _))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-sub γ Δ₁ (castᶜ eA M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (subC (env-Cˢ γ Δ₁ (castᶜ eA M)) _)) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-subC eIn) ⟩
    sub-atᶜ Δ (subC (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) _) W
  ≡⟨⟩
    subC (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W) _
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ


env-Vˢ-pair : ∀ {St Γ A B} → (γ : Env St Γ) → (Δ : Ctx)
            → (V : (Γ ++ᶜ Δ) ⊢V⦂ A) → (U : (Γ ++ᶜ Δ) ⊢V⦂ B)
            → env-Vˢ γ Δ ⦉ V , U ⦊ ≡ ⦉ env-Vˢ γ Δ V , env-Vˢ γ Δ U ⦊

env-Vˢ-pair ⌊ St ⌋ Δ V U = refl
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

-- The body sits at an extended suffix, so the two sides carry casts along
-- different (but equal) proofs, reconciled by `castᶜ-irr`.

env-Cˢ-delay : ∀ {St Γ A ε τ} → (γ : Env St Γ) → (Δ : Ctx)
             → (M : (Γ ++ᶜ Δ) ⟨ ιᵣ τ ⟩ ⊢C⦂ A ! ε)
             → env-Cˢ γ Δ (delay τ M) ≡ delay τ (env-Cˢ γ (Δ ⟨ ιᵣ τ ⟩) M)

env-Cˢ-delay ⌊ St ⌋ Δ M = refl
env-Cˢ-delay (reachᵉ γ q) Δ M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-delay γ Δ M)

env-Cˢ-delay {τ = τ} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ'} γ q) Δ M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (delay τ M)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-delay ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (delay τ (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-delay γ Δ' (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)) ⟩
      castᶜ eo (delay τ (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩)
                          (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
    ≡⟨ cast-delay eo ⟩
      delay τ (castᶜ (cong (_⟨ ιᵣ τ ⟩) eo)
                (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
    ≡⟨ cong (delay τ) (castᶜ-irr (cong (_⟨ ιᵣ τ ⟩) eo) eo₂ _) ⟩
      delay τ (castᶜ eo₂
                (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
    ≡⟨ cong (λ z → delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) z)))
            (castᶜ-irr (cong (_⟨ ιᵣ τ ⟩) ei) ei₂ M) ⟩
      delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ' ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) (Δ ⟨ ιᵣ τ ⟩))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) (Δ ⟨ ιᵣ τ ⟩)

env-Cˢ-delay {τ = τ} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ'} V₀ γ) Δ M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (delay τ M)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-delay ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (delay τ (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-delay γ Δ' (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)) ⟩
    castᶜ eo (delay τ (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩)
                        (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
  ≡⟨ cast-delay eo ⟩
    delay τ (castᶜ (cong (_⟨ ιᵣ τ ⟩) eo)
              (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
  ≡⟨ cong (delay τ) (castᶜ-irr (cong (_⟨ ιᵣ τ ⟩) eo) eo₂ _) ⟩
    delay τ (castᶜ eo₂
              (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) (castᶜ (cong (_⟨ ιᵣ τ ⟩) ei) M)))
  ≡⟨ cong (λ z → delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) z)))
          (castᶜ-irr (cong (_⟨ ιᵣ τ ⟩) ei) ei₂ M) ⟩
    delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ιᵣ τ ⟩) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ' ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ ιᵣ τ ⟩))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ ιᵣ τ ⟩)

env-Cˢ-delay {τ = τ} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (delay τ M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-delay eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (delay τ (castᶜ (exτ eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-delay γ Δ₁ (castᶜ (exτ eA) M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (delay τ (env-Cˢ γ (Δ₁ ⟨ ιᵣ τ ⟩)
                                    (castᶜ (exτ eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-delay eIn) ⟩
    sub-atᶜ Δ (delay τ (castᶜ (exτ eIn) (env-Cˢ γ (Δ₁ ⟨ ιᵣ τ ⟩)
                                          (castᶜ (exτ eA) M)))) W
  ≡⟨ cong (λ z → delay τ (sub-atᶜ (Δ ⟨ ιᵣ τ ⟩) z W))
          (castᶜ-irr (exτ eIn) eIn₂ _) ⟩
    delay τ (sub-atᶜ (Δ ⟨ ιᵣ τ ⟩)
               (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ ιᵣ τ ⟩)
                             (castᶜ (exτ eA) M))) W)
  ≡⟨ cong (λ z → delay τ (sub-atᶜ (Δ ⟨ ιᵣ τ ⟩)
             (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ ιᵣ τ ⟩) z)) W))
          (castᶜ-irr (exτ eA) eA₂ M) ⟩
    delay τ (sub-atᶜ (Δ ⟨ ιᵣ τ ⟩)
               (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ ιᵣ τ ⟩) (castᶜ eA₂ M))) W)
  ∎
  where
    exτ   = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong (_⟨ ιᵣ τ ⟩) e
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ ιᵣ τ ⟩))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ ιᵣ τ ⟩)

env-Cˢ-seq : ∀ {St Γ A B ε ε'} → (γ : Env St Γ) → (Δ : Ctx)
           → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ! ε)
           → (N : (Γ ++ᶜ Δ) ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
           → env-Cˢ γ Δ (M ⨟ N)
           ≡ (env-Cˢ γ Δ M) ⨟ (env-Cˢ γ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) N)

env-Cˢ-seq ⌊ St ⌋ Δ M N = refl
env-Cˢ-seq (reachᵉ γ q) Δ M N = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-seq γ Δ M N)

env-Cˢ-seq {A = A} {ε = ε} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (M ⨟ N)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-seq ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' ((castᶜ ei M) ⨟ (castᶜ (exε ei) N)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-seq γ Δ' (castᶜ ei M) (castᶜ (exε ei) N)) ⟩
      castᶜ eo ((env-Cˢ γ Δ' (castᶜ ei M))
                  ⨟ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cast-seq eo ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ (exε eo) (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cong ((castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) ⨟_)
            (castᶜ-irr (exε eo) eo₂ _) ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cong (λ z → (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
                     ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) z)))
            (castᶜ-irr (exε ei) ei₂ N) ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ ei₂ N)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ M N =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (M ⨟ N)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-seq ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' ((castᶜ ei M) ⨟ (castᶜ (exε ei) N)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-seq γ Δ' (castᶜ ei M) (castᶜ (exε ei) N)) ⟩
    castᶜ eo ((env-Cˢ γ Δ' (castᶜ ei M))
                ⨟ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cast-seq eo ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ (exε eo) (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cong ((castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) ⨟_)
          (castᶜ-irr (exε eo) eo₂ _) ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cong (λ z → (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
                   ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) z)))
          (castᶜ-irr (exε ei) ei₂ N) ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ ei₂ N)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M N =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (M ⨟ N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-seq eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ ((castᶜ eA M) ⨟ (castᶜ (exε eA) N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-seq γ Δ₁ (castᶜ eA M) (castᶜ (exε eA) N)) ⟩
    sub-atᶜ Δ (castᶜ eIn ((env-Cˢ γ Δ₁ (castᶜ eA M))
                           ⨟ (env-Cˢ γ (Δ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
                                (castᶜ (exε eA) N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-seq eIn) ⟩
    sub-atᶜ Δ ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M)))
                 ⨟ (castᶜ (exε eIn) (env-Cˢ γ (Δ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
                                      (castᶜ (exε eA) N)))) W
  ≡⟨ cong (λ z → (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
                   ⨟ (sub-atᶜ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) z W))
          (castᶜ-irr (exε eIn) eIn₂ _) ⟩
    (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
      ⨟ (sub-atᶜ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
           (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ (exε eA) N))) W)
  ≡⟨ cong (λ z → (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
                   ⨟ (sub-atᶜ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
                        (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) z)) W))
          (castᶜ-irr (exε eA) eA₂ N) ⟩
    (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
      ⨟ (sub-atᶜ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
           (castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ eA₂ N))) W)
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)
    exε   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) p

env-Cˢ-perform : ∀ {St Γ A ε} {op : Op} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ ⌜ param op ⌝ᵍ)
           → (M : (Γ ++ᶜ Δ) ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε)
           → env-Cˢ γ Δ (perform op (V) (M))
           ≡ perform op (env-Vˢ γ Δ V) (env-Cˢ γ (Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) M)

env-Cˢ-perform ⌊ St ⌋ Δ V M = refl
env-Cˢ-perform (reachᵉ γ q) Δ V M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-perform γ Δ V M)

env-Cˢ-perform {op = op} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (perform op (V) (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-perform ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (perform op (castᵛ ei V) (castᶜ (exf ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-perform γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
      castᶜ eo (perform op (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ (exf ei) M)))
    ≡⟨ cast-perform eo ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ (exf eo) (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (z))
            (castᶜ-irr (exf eo) eo₂ _) ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) z)))
            (castᶜ-irr (exf ei) ei₂ M) ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) p

env-Cˢ-perform {op = op} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (perform op (V) (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-perform ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (perform op (castᵛ ei V) (castᶜ (exf ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-perform γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
    castᶜ eo (perform op (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ (exf ei) M)))
  ≡⟨ cast-perform eo ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ (exf eo) (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (z))
          (castᶜ-irr (exf eo) eo₂ _) ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) z)))
          (castᶜ-irr (exf ei) ei₂ M) ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) p

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
    Δ₂    = Δ₁ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
    Δ₃    = Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ)
    exf   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) p

env-Cˢ-match : ∀ {St Γ A B C} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A |×| B)
           → (M : (Γ ++ᶜ Δ) ∷ A ∷ B ⊢C⦂ C)
           → env-Cˢ γ Δ (match (V) `in (M))
           ≡ match (env-Vˢ γ Δ V) `in (env-Cˢ γ (Δ ∷ A ∷ B) M)

env-Cˢ-match ⌊ St ⌋ Δ V M = refl
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

-- Natural-number elimination: the zero branch sits at the suffix itself, the
-- successor branch at the suffix extended by its binder, reconciled by
-- `castᶜ-irr` as for `case+`.

env-Cˢ-caseℕ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
             → (V : (Γ ++ᶜ Δ) ⊢V⦂ nat)
             → (M : (Γ ++ᶜ Δ) ⊢C⦂ C)
             → (N : (Γ ++ᶜ Δ) ∷ nat ⊢C⦂ C)
             → env-Cˢ γ Δ (caseℕ V `zero M `succ N)
             ≡ caseℕ (env-Vˢ γ Δ V) `zero (env-Cˢ γ Δ M)
                                    `succ (env-Cˢ γ (Δ ∷ nat) N)

env-Cˢ-caseℕ ⌊ St ⌋ Δ V M N = refl
env-Cˢ-caseℕ (reachᵉ γ q) Δ V M N =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-caseℕ γ Δ V M N)

env-Cˢ-caseℕ (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (caseℕ V `zero M `succ N)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-caseℕ ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (caseℕ castᵛ ei V `zero castᶜ ei M
                                              `succ castᶜ (exN ei) N))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-caseℕ γ Δ' (castᵛ ei V) (castᶜ ei M)
                                          (castᶜ (exN ei) N)) ⟩
      castᶜ eo (caseℕ env-Vˢ γ Δ' (castᵛ ei V)
                  `zero env-Cˢ γ Δ' (castᶜ ei M)
                  `succ env-Cˢ γ (Δ' ∷ nat) (castᶜ (exN ei) N))
    ≡⟨ cast-caseℕ eo ⟩
      caseℕ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
        `zero castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
        `succ castᶜ (exN eo) (env-Cˢ γ (Δ' ∷ nat) (castᶜ (exN ei) N))
    ≡⟨ cong (λ z → caseℕ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
                     `zero castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)) `succ z)
            (trans (castᶜ-irr (exN eo) eoN _)
                   (cong (λ z → castᶜ eoN (env-Cˢ γ (Δ' ∷ nat) z))
                         (castᶜ-irr (exN ei) eiN N))) ⟩
      caseℕ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
        `zero castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
        `succ castᶜ eoN (env-Cˢ γ (Δ' ∷ nat) (castᶜ eiN N))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eoN = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ nat))
    eiN = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ nat)
    exN = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ nat) p

env-Cˢ-caseℕ (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M N =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (caseℕ V `zero M `succ N)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-caseℕ ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (caseℕ castᵛ ei V `zero castᶜ ei M
                                            `succ castᶜ (exN ei) N))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-caseℕ γ Δ' (castᵛ ei V) (castᶜ ei M)
                                        (castᶜ (exN ei) N)) ⟩
    castᶜ eo (caseℕ env-Vˢ γ Δ' (castᵛ ei V)
                `zero env-Cˢ γ Δ' (castᶜ ei M)
                `succ env-Cˢ γ (Δ' ∷ nat) (castᶜ (exN ei) N))
  ≡⟨ cast-caseℕ eo ⟩
    caseℕ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
      `zero castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
      `succ castᶜ (exN eo) (env-Cˢ γ (Δ' ∷ nat) (castᶜ (exN ei) N))
  ≡⟨ cong (λ z → caseℕ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
                   `zero castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)) `succ z)
          (trans (castᶜ-irr (exN eo) eoN _)
                 (cong (λ z → castᶜ eoN (env-Cˢ γ (Δ' ∷ nat) z))
                       (castᶜ-irr (exN ei) eiN N))) ⟩
    caseℕ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
      `zero castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
      `succ castᶜ eoN (env-Cˢ γ (Δ' ∷ nat) (castᶜ eiN N))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eoN = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ nat))
    eiN = ++ᶜ-assoc Γ Δ₁ (Δ ∷ nat)
    exN = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ nat) p

env-Cˢ-caseℕ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M N =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (caseℕ V `zero M `succ N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-caseℕ eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (caseℕ castᵛ eA V `zero castᶜ eA M `succ castᶜ (exN eA) N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-caseℕ γ Δ₁ (castᵛ eA V) (castᶜ eA M) (castᶜ (exN eA) N)) ⟩
    sub-atᶜ Δ (castᶜ eIn (caseℕ env-Vˢ γ Δ₁ (castᵛ eA V)
                            `zero env-Cˢ γ Δ₁ (castᶜ eA M)
                            `succ env-Cˢ γ (Δ₁ ∷ nat) (castᶜ (exN eA) N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-caseℕ eIn) ⟩
    sub-atᶜ Δ (caseℕ castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))
                 `zero castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))
                 `succ castᶜ (exN eIn) (env-Cˢ γ (Δ₁ ∷ nat) (castᶜ (exN eA) N))) W
  ≡⟨ cong (λ z → caseℕ sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
                   `zero sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W
                   `succ sub-atᶜ (Δ ∷ nat) z W)
          (trans (castᶜ-irr (exN eIn) eInN _)
                 (cong (λ z → castᶜ eInN (env-Cˢ γ (Δ₁ ∷ nat) z))
                       (castᶜ-irr (exN eA) eAN N))) ⟩
    caseℕ sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
      `zero sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W
      `succ sub-atᶜ (Δ ∷ nat) (castᶜ eInN (env-Cˢ γ (Δ₁ ∷ nat) (castᶜ eAN N))) W
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eInN  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ nat))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eAN   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ nat)
    exN   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ nat) p

-- Primitive recursion: the base sits at the suffix itself, the step at the
-- suffix extended by the barrier, the predecessor, the lock and the result,
-- reconciled by `castᶜ-irr` as for `caseℕ`.

env-Cˢ-recℕ : ∀ {St Γ B ε} → (γ : Env St Γ) → (Δ : Ctx)
            → (V : (Γ ++ᶜ Δ) ⊢V⦂ nat)
            → (M : (Γ ++ᶜ Δ) ⊢C⦂ B ! ε)
            → (N : ((Γ ++ᶜ Δ) ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
            → (p : ε ·ₑ ε ≾ₑ ε)
            → env-Cˢ γ Δ (recℕ V M N p)
            ≡ recℕ (env-Vˢ γ Δ V) (env-Cˢ γ Δ M)
                   (env-Cˢ γ ((Δ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) N) p

env-Cˢ-recℕ ⌊ St ⌋ Δ V M N p = refl
env-Cˢ-recℕ (reachᵉ γ q) Δ V M N p =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-recℕ γ Δ V M N p)

env-Cˢ-recℕ {B = B} {ε = ε} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M N p =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (recℕ V M N p)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-recℕ ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (recℕ (castᵛ ei V) (castᶜ ei M) (castᶜ (exN ei) N) p))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-recℕ γ Δ' (castᵛ ei V) (castᶜ ei M)
                                         (castᶜ (exN ei) N) p) ⟩
      castᶜ eo (recℕ (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ Δ' (castᶜ ei M))
                     (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N)) p)
    ≡⟨ cast-recℕ eo ⟩
      recℕ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
           (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
           (castᶜ (exN eo) (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N))) p
    ≡⟨ cong (λ z → recℕ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
                        (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) z p)
            (trans (castᶜ-irr (exN eo) eoN _)
                   (cong (λ z → castᶜ eoN (env-Cˢ γ (stepΔ Δ') z))
                         (castᶜ-irr (exN ei) eiN N))) ⟩
      recℕ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
           (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
           (castᶜ eoN (env-Cˢ γ (stepΔ Δ') (castᶜ eiN N))) p
     ∎)
  where
    stepΔ : Ctx → Ctx
    stepΔ X = (X ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eoN = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (stepΔ Δ))
    eiN = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (stepΔ Δ)
    exN = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong stepΔ e

env-Cˢ-recℕ {B = B} {ε = ε} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M N p =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (recℕ V M N p)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-recℕ ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (recℕ (castᵛ ei V) (castᶜ ei M) (castᶜ (exN ei) N) p))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-recℕ γ Δ' (castᵛ ei V) (castᶜ ei M)
                                       (castᶜ (exN ei) N) p) ⟩
    castᶜ eo (recℕ (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ Δ' (castᶜ ei M))
                   (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N)) p)
  ≡⟨ cast-recℕ eo ⟩
    recℕ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
         (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
         (castᶜ (exN eo) (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N))) p
  ≡⟨ cong (λ z → recℕ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
                      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) z p)
          (trans (castᶜ-irr (exN eo) eoN _)
                 (cong (λ z → castᶜ eoN (env-Cˢ γ (stepΔ Δ') z))
                       (castᶜ-irr (exN ei) eiN N))) ⟩
    recℕ (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
         (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
         (castᶜ eoN (env-Cˢ γ (stepΔ Δ') (castᶜ eiN N))) p
   ∎
  where
    stepΔ : Ctx → Ctx
    stepΔ X = (X ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eoN = sym (++ᶜ-assoc (toCtx St) Δ₁ (stepΔ Δ))
    eiN = ++ᶜ-assoc Γ Δ₁ (stepΔ Δ)
    exN = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong stepΔ e

env-Cˢ-recℕ {B = B} {ε = ε} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M N p =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (recℕ V M N p)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-recℕ eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (recℕ (castᵛ eA V) (castᶜ eA M) (castᶜ (exN eA) N) p))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-recℕ γ Δ₁ (castᵛ eA V) (castᶜ eA M) (castᶜ (exN eA) N) p) ⟩
    sub-atᶜ Δ (castᶜ eIn (recℕ (env-Vˢ γ Δ₁ (castᵛ eA V))
                               (env-Cˢ γ Δ₁ (castᶜ eA M))
                               (env-Cˢ γ (stepΔ Δ₁) (castᶜ (exN eA) N)) p)) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-recℕ eIn) ⟩
    sub-atᶜ Δ (recℕ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))
                    (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M)))
                    (castᶜ (exN eIn) (env-Cˢ γ (stepΔ Δ₁) (castᶜ (exN eA) N))) p) W
  ≡⟨ cong (λ z → recℕ (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
                      (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
                      (sub-atᶜ (stepΔ Δ) z W) p)
          (trans (castᶜ-irr (exN eIn) eInN _)
                 (cong (λ z → castᶜ eInN (env-Cˢ γ (stepΔ Δ₁) z))
                       (castᶜ-irr (exN eA) eAN N))) ⟩
    recℕ (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
         (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
         (sub-atᶜ (stepΔ Δ) (castᶜ eInN (env-Cˢ γ (stepΔ Δ₁) (castᶜ eAN N))) W) p
  ∎
  where
    stepΔ : Ctx → Ctx
    stepΔ X = (X ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eInN  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (stepΔ Δ))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eAN   = ++ᶜ-assoc Γ ([] ∷ A₀) (stepΔ Δ)
    exN   = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong stepΔ e

-- The injections: the action passes the injection, as it passes a pair.

env-Vˢ-inl : ∀ {St Γ A B} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Vˢ γ Δ (inl {B = B} V) ≡ inl (env-Vˢ γ Δ V)

env-Vˢ-inl ⌊ St ⌋ Δ V = refl
env-Vˢ-inl (reachᵉ γ q) Δ V =
  cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-inl γ Δ V)

env-Vˢ-inl {B = B} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  cong (V-rename (cong-ren (unbox-ren q)))
    (trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-inl ei))
    (trans (cong (castᵛ eo) (env-Vˢ-inl {B = B} γ Δ' (castᵛ ei V)))
           (cast-inl eo)))
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-inl {B = B} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V =
  trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-inl ei))
  (trans (cong (castᵛ eo) (env-Vˢ-inl {B = B} γ Δ' (castᵛ ei V)))
         (cast-inl eo))
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-inl {B = B} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V =
  trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ z)) W) (cast-inl eA))
  (trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W)
               (env-Vˢ-inl {B = B} γ Δ₁ (castᵛ eA V)))
         (cong (λ z → sub-atᵛ Δ z W) (cast-inl eIn)))
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Vˢ-inr : ∀ {St Γ A B} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ B)
           → env-Vˢ γ Δ (inr {A = A} V) ≡ inr (env-Vˢ γ Δ V)

env-Vˢ-inr ⌊ St ⌋ Δ V = refl
env-Vˢ-inr (reachᵉ γ q) Δ V =
  cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-inr γ Δ V)

env-Vˢ-inr {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  cong (V-rename (cong-ren (unbox-ren q)))
    (trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-inr ei))
    (trans (cong (castᵛ eo) (env-Vˢ-inr {A = A} γ Δ' (castᵛ ei V)))
           (cast-inr eo)))
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-inr {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V =
  trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-inr ei))
  (trans (cong (castᵛ eo) (env-Vˢ-inr {A = A} γ Δ' (castᵛ ei V)))
         (cast-inr eo))
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-inr {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V =
  trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ z)) W) (cast-inr eA))
  (trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W)
               (env-Vˢ-inr {A = A} γ Δ₁ (castᵛ eA V)))
         (cong (λ z → sub-atᵛ Δ z W) (cast-inr eIn)))
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

-- Sum elimination: each branch sits at the suffix extended by its own binder,
-- the two casts reconciled by `castᶜ-irr` as for `match`.

env-Cˢ-case+ : ∀ {St Γ A B C} → (γ : Env St Γ) → (Δ : Ctx)
             → (V : (Γ ++ᶜ Δ) ⊢V⦂ A |+| B)
             → (M : (Γ ++ᶜ Δ) ∷ A ⊢C⦂ C)
             → (N : (Γ ++ᶜ Δ) ∷ B ⊢C⦂ C)
             → env-Cˢ γ Δ (case+ V `inl M `inr N)
             ≡ case+ (env-Vˢ γ Δ V) `inl (env-Cˢ γ (Δ ∷ A) M)
                                    `inr (env-Cˢ γ (Δ ∷ B) N)

env-Cˢ-case+ ⌊ St ⌋ Δ V M N = refl
env-Cˢ-case+ (reachᵉ γ q) Δ V M N =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-case+ γ Δ V M N)

env-Cˢ-case+ {A = A} {B = B} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (case+ V `inl M `inr N)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-case+ ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (case+ castᵛ ei V `inl castᶜ (exA ei) M
                                              `inr castᶜ (exB ei) N))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-case+ γ Δ' (castᵛ ei V) (castᶜ (exA ei) M)
                                          (castᶜ (exB ei) N)) ⟩
      castᶜ eo (case+ env-Vˢ γ Δ' (castᵛ ei V)
                  `inl env-Cˢ γ (Δ' ∷ A) (castᶜ (exA ei) M)
                  `inr env-Cˢ γ (Δ' ∷ B) (castᶜ (exB ei) N))
    ≡⟨ cast-case+ eo ⟩
      case+ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
        `inl castᶜ (exA eo) (env-Cˢ γ (Δ' ∷ A) (castᶜ (exA ei) M))
        `inr castᶜ (exB eo) (env-Cˢ γ (Δ' ∷ B) (castᶜ (exB ei) N))
    ≡⟨ cong₂ (λ y z → case+ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) `inl y `inr z)
             (trans (castᶜ-irr (exA eo) eoA _)
                    (cong (λ z → castᶜ eoA (env-Cˢ γ (Δ' ∷ A) z))
                          (castᶜ-irr (exA ei) eiA M)))
             (trans (castᶜ-irr (exB eo) eoB _)
                    (cong (λ z → castᶜ eoB (env-Cˢ γ (Δ' ∷ B) z))
                          (castᶜ-irr (exB ei) eiB N))) ⟩
      case+ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
        `inl castᶜ eoA (env-Cˢ γ (Δ' ∷ A) (castᶜ eiA M))
        `inr castᶜ eoB (env-Cˢ γ (Δ' ∷ B) (castᶜ eiB N))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eoA = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ A))
    eiA = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ A)
    eoB = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ B))
    eiB = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ B)
    exA = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ A) p
    exB = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ B) p

env-Cˢ-case+ {A = A} {B = B} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M N =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (case+ V `inl M `inr N)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-case+ ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (case+ castᵛ ei V `inl castᶜ (exA ei) M
                                            `inr castᶜ (exB ei) N))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-case+ γ Δ' (castᵛ ei V) (castᶜ (exA ei) M)
                                        (castᶜ (exB ei) N)) ⟩
    castᶜ eo (case+ env-Vˢ γ Δ' (castᵛ ei V)
                `inl env-Cˢ γ (Δ' ∷ A) (castᶜ (exA ei) M)
                `inr env-Cˢ γ (Δ' ∷ B) (castᶜ (exB ei) N))
  ≡⟨ cast-case+ eo ⟩
    case+ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
      `inl castᶜ (exA eo) (env-Cˢ γ (Δ' ∷ A) (castᶜ (exA ei) M))
      `inr castᶜ (exB eo) (env-Cˢ γ (Δ' ∷ B) (castᶜ (exB ei) N))
  ≡⟨ cong₂ (λ y z → case+ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) `inl y `inr z)
           (trans (castᶜ-irr (exA eo) eoA _)
                  (cong (λ z → castᶜ eoA (env-Cˢ γ (Δ' ∷ A) z))
                        (castᶜ-irr (exA ei) eiA M)))
           (trans (castᶜ-irr (exB eo) eoB _)
                  (cong (λ z → castᶜ eoB (env-Cˢ γ (Δ' ∷ B) z))
                        (castᶜ-irr (exB ei) eiB N))) ⟩
    case+ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
      `inl castᶜ eoA (env-Cˢ γ (Δ' ∷ A) (castᶜ eiA M))
      `inr castᶜ eoB (env-Cˢ γ (Δ' ∷ B) (castᶜ eiB N))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eoA = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ A))
    eiA = ++ᶜ-assoc Γ Δ₁ (Δ ∷ A)
    eoB = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ B))
    eiB = ++ᶜ-assoc Γ Δ₁ (Δ ∷ B)
    exA = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ A) p
    exB = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ B) p

env-Cˢ-case+ {A = A} {B = B} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M N =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (case+ V `inl M `inr N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-case+ eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (case+ castᵛ eA V `inl castᶜ (exA eA) M `inr castᶜ (exB eA) N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-case+ γ Δ₁ (castᵛ eA V) (castᶜ (exA eA) M) (castᶜ (exB eA) N)) ⟩
    sub-atᶜ Δ (castᶜ eIn (case+ env-Vˢ γ Δ₁ (castᵛ eA V)
                            `inl env-Cˢ γ (Δ₁ ∷ A) (castᶜ (exA eA) M)
                            `inr env-Cˢ γ (Δ₁ ∷ B) (castᶜ (exB eA) N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-case+ eIn) ⟩
    sub-atᶜ Δ (case+ castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))
                 `inl castᶜ (exA eIn) (env-Cˢ γ (Δ₁ ∷ A) (castᶜ (exA eA) M))
                 `inr castᶜ (exB eIn) (env-Cˢ γ (Δ₁ ∷ B) (castᶜ (exB eA) N))) W
  ≡⟨ cong₂ (λ y z → case+ sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
                      `inl sub-atᶜ (Δ ∷ A) y W `inr sub-atᶜ (Δ ∷ B) z W)
           (trans (castᶜ-irr (exA eIn) eInA _)
                  (cong (λ z → castᶜ eInA (env-Cˢ γ (Δ₁ ∷ A) z))
                        (castᶜ-irr (exA eA) eAA M)))
           (trans (castᶜ-irr (exB eIn) eInB _)
                  (cong (λ z → castᶜ eInB (env-Cˢ γ (Δ₁ ∷ B) z))
                        (castᶜ-irr (exB eA) eAB N))) ⟩
    case+ sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
      `inl sub-atᶜ (Δ ∷ A) (castᶜ eInA (env-Cˢ γ (Δ₁ ∷ A) (castᶜ eAA M))) W
      `inr sub-atᶜ (Δ ∷ B) (castᶜ eInB (env-Cˢ γ (Δ₁ ∷ B) (castᶜ eAB N))) W
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eInA  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A))
    eInB  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ B))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eAA   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ A)
    eAB   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ B)
    exA   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ A) p
    exB   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ B) p

-- Lists: `nil` and `cons` as constants and pairs; the `cons` branch of
-- `caseL` at the suffix extended by its two binders, and the step of `recL` as
-- for `recℕ`, each reconciled by `castᶜ-irr`.

env-Vˢ-nil : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx)
           → env-Vˢ γ Δ (nil {A = A}) ≡ nil

env-Vˢ-nil ⌊ St ⌋ Δ = refl
env-Vˢ-nil (reachᵉ γ q) Δ =
  cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-nil γ Δ)

env-Vˢ-nil {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ =
  cong (V-rename (cong-ren (unbox-ren q)))
    (trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-nil ei))
    (trans (cong (castᵛ eo) (env-Vˢ-nil {A = A} γ Δ')) (cast-nil eo)))
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-nil {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ =
  trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-nil ei))
  (trans (cong (castᵛ eo) (env-Vˢ-nil {A = A} γ Δ')) (cast-nil eo))
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-nil {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ =
  trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ z)) W) (cast-nil eA))
  (trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W) (env-Vˢ-nil {A = A} γ Δ₁))
         (cong (λ z → sub-atᵛ Δ z W) (cast-nil eIn)))
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Vˢ-cons : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx)
            → (V : (Γ ++ᶜ Δ) ⊢V⦂ A) → (U : (Γ ++ᶜ Δ) ⊢V⦂ list A)
            → env-Vˢ γ Δ (cons V U) ≡ cons (env-Vˢ γ Δ V) (env-Vˢ γ Δ U)

env-Vˢ-cons ⌊ St ⌋ Δ V U = refl
env-Vˢ-cons (reachᵉ γ q) Δ V U = cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-cons γ Δ V U)

env-Vˢ-cons (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V U =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (cons V U)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-cons ei) ⟩
      castᵛ eo (env-Vˢ γ Δ' (cons (castᵛ ei V) (castᵛ ei U)))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-cons γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
      castᵛ eo (cons (env-Vˢ γ Δ' (castᵛ ei V)) (env-Vˢ γ Δ' (castᵛ ei U)))
    ≡⟨ cast-cons eo ⟩
      cons (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U)))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-cons (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V U =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (cons V U)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-cons ei) ⟩
    castᵛ eo (env-Vˢ γ Δ' (cons (castᵛ ei V) (castᵛ ei U)))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-cons γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
    castᵛ eo (cons (env-Vˢ γ Δ' (castᵛ ei V)) (env-Vˢ γ Δ' (castᵛ ei U)))
  ≡⟨ cast-cons eo ⟩
    cons (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U)))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-cons (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V U =
  begin
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (cons V U)))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ z)) W) (cast-cons eA) ⟩
    sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (cons (castᵛ eA V) (castᵛ eA U)))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W)
          (env-Vˢ-cons γ Δ₁ (castᵛ eA V) (castᵛ eA U)) ⟩
    sub-atᵛ Δ (castᵛ eIn (cons (env-Vˢ γ Δ₁ (castᵛ eA V))
                               (env-Vˢ γ Δ₁ (castᵛ eA U)))) W
  ≡⟨ cong (λ z → sub-atᵛ Δ z W) (cast-cons eIn) ⟩
    sub-atᵛ Δ (cons (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))
                    (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U)))) W
  ≡⟨⟩
    cons (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
         (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) W)
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-caseL : ∀ {St Γ A C} → (γ : Env St Γ) → (Δ : Ctx)
             → (V : (Γ ++ᶜ Δ) ⊢V⦂ list A)
             → (M : (Γ ++ᶜ Δ) ⊢C⦂ C)
             → (N : (Γ ++ᶜ Δ) ∷ A ∷ list A ⊢C⦂ C)
             → env-Cˢ γ Δ (caseL V `nil M `cons N)
             ≡ caseL (env-Vˢ γ Δ V) `nil (env-Cˢ γ Δ M)
                                    `cons (env-Cˢ γ (Δ ∷ A ∷ list A) N)

env-Cˢ-caseL ⌊ St ⌋ Δ V M N = refl
env-Cˢ-caseL (reachᵉ γ q) Δ V M N =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-caseL γ Δ V M N)

env-Cˢ-caseL {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (caseL V `nil M `cons N)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-caseL ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (caseL castᵛ ei V `nil castᶜ ei M
                                              `cons castᶜ (exN ei) N))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-caseL γ Δ' (castᵛ ei V) (castᶜ ei M)
                                          (castᶜ (exN ei) N)) ⟩
      castᶜ eo (caseL env-Vˢ γ Δ' (castᵛ ei V)
                  `nil env-Cˢ γ Δ' (castᶜ ei M)
                  `cons env-Cˢ γ (Δ' ∷ A ∷ list A) (castᶜ (exN ei) N))
    ≡⟨ cast-caseL eo ⟩
      caseL castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
        `nil castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
        `cons castᶜ (exN eo) (env-Cˢ γ (Δ' ∷ A ∷ list A) (castᶜ (exN ei) N))
    ≡⟨ cong (λ z → caseL castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
                     `nil castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)) `cons z)
            (trans (castᶜ-irr (exN eo) eoN _)
                   (cong (λ z → castᶜ eoN (env-Cˢ γ (Δ' ∷ A ∷ list A) z))
                         (castᶜ-irr (exN ei) eiN N))) ⟩
      caseL castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
        `nil castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
        `cons castᶜ eoN (env-Cˢ γ (Δ' ∷ A ∷ list A) (castᶜ eiN N))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eoN = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ A ∷ list A))
    eiN = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ A ∷ list A)
    exN = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ X → X ∷ A ∷ list A) p

env-Cˢ-caseL {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M N =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (caseL V `nil M `cons N)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-caseL ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (caseL castᵛ ei V `nil castᶜ ei M
                                            `cons castᶜ (exN ei) N))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-caseL γ Δ' (castᵛ ei V) (castᶜ ei M)
                                        (castᶜ (exN ei) N)) ⟩
    castᶜ eo (caseL env-Vˢ γ Δ' (castᵛ ei V)
                `nil env-Cˢ γ Δ' (castᶜ ei M)
                `cons env-Cˢ γ (Δ' ∷ A ∷ list A) (castᶜ (exN ei) N))
  ≡⟨ cast-caseL eo ⟩
    caseL castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
      `nil castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
      `cons castᶜ (exN eo) (env-Cˢ γ (Δ' ∷ A ∷ list A) (castᶜ (exN ei) N))
  ≡⟨ cong (λ z → caseL castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
                   `nil castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)) `cons z)
          (trans (castᶜ-irr (exN eo) eoN _)
                 (cong (λ z → castᶜ eoN (env-Cˢ γ (Δ' ∷ A ∷ list A) z))
                       (castᶜ-irr (exN ei) eiN N))) ⟩
    caseL castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))
      `nil castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))
      `cons castᶜ eoN (env-Cˢ γ (Δ' ∷ A ∷ list A) (castᶜ eiN N))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eoN = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ A ∷ list A))
    eiN = ++ᶜ-assoc Γ Δ₁ (Δ ∷ A ∷ list A)
    exN = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ X → X ∷ A ∷ list A) p

env-Cˢ-caseL {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M N =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (caseL V `nil M `cons N)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-caseL eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (caseL castᵛ eA V `nil castᶜ eA M `cons castᶜ (exN eA) N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-caseL γ Δ₁ (castᵛ eA V) (castᶜ eA M) (castᶜ (exN eA) N)) ⟩
    sub-atᶜ Δ (castᶜ eIn (caseL env-Vˢ γ Δ₁ (castᵛ eA V)
                            `nil env-Cˢ γ Δ₁ (castᶜ eA M)
                            `cons env-Cˢ γ (Δ₁ ∷ A ∷ list A) (castᶜ (exN eA) N))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-caseL eIn) ⟩
    sub-atᶜ Δ (caseL castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))
                 `nil castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))
                 `cons castᶜ (exN eIn) (env-Cˢ γ (Δ₁ ∷ A ∷ list A) (castᶜ (exN eA) N))) W
  ≡⟨ cong (λ z → caseL sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
                   `nil sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W
                   `cons sub-atᶜ (Δ ∷ A ∷ list A) z W)
          (trans (castᶜ-irr (exN eIn) eInN _)
                 (cong (λ z → castᶜ eInN (env-Cˢ γ (Δ₁ ∷ A ∷ list A) z))
                       (castᶜ-irr (exN eA) eAN N))) ⟩
    caseL sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W
      `nil sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W
      `cons sub-atᶜ (Δ ∷ A ∷ list A) (castᶜ eInN (env-Cˢ γ (Δ₁ ∷ A ∷ list A) (castᶜ eAN N))) W
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eInN  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A ∷ list A))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eAN   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ A ∷ list A)
    exN   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ X → X ∷ A ∷ list A) p

env-Cˢ-recL : ∀ {St Γ A B ε} → (γ : Env St Γ) → (Δ : Ctx)
            → (V : (Γ ++ᶜ Δ) ⊢V⦂ list A)
            → (M : (Γ ++ᶜ Δ) ⊢C⦂ B ! ε)
            → (N : ((Γ ++ᶜ Δ) ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
            → (p : ε ·ₑ ε ≾ₑ ε)
            → env-Cˢ γ Δ (recL V M N p)
            ≡ recL (env-Vˢ γ Δ V) (env-Cˢ γ Δ M)
                   (env-Cˢ γ ((Δ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) N) p

env-Cˢ-recL ⌊ St ⌋ Δ V M N p = refl
env-Cˢ-recL (reachᵉ γ q) Δ V M N p =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-recL γ Δ V M N p)

env-Cˢ-recL {A = A} {B = B} {ε = ε} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M N p =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (recL V M N p)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-recL ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (recL (castᵛ ei V) (castᶜ ei M) (castᶜ (exN ei) N) p))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-recL γ Δ' (castᵛ ei V) (castᶜ ei M)
                                         (castᶜ (exN ei) N) p) ⟩
      castᶜ eo (recL (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ Δ' (castᶜ ei M))
                     (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N)) p)
    ≡⟨ cast-recL eo ⟩
      recL (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
           (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
           (castᶜ (exN eo) (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N))) p
    ≡⟨ cong (λ z → recL (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
                        (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) z p)
            (trans (castᶜ-irr (exN eo) eoN _)
                   (cong (λ z → castᶜ eoN (env-Cˢ γ (stepΔ Δ') z))
                         (castᶜ-irr (exN ei) eiN N))) ⟩
      recL (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
           (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
           (castᶜ eoN (env-Cˢ γ (stepΔ Δ') (castᶜ eiN N))) p
     ∎)
  where
    stepΔ : Ctx → Ctx
    stepΔ X = (X ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eoN = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (stepΔ Δ))
    eiN = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (stepΔ Δ)
    exN = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong stepΔ e

env-Cˢ-recL {A = A} {B = B} {ε = ε} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M N p =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (recL V M N p)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-recL ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (recL (castᵛ ei V) (castᶜ ei M) (castᶜ (exN ei) N) p))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-recL γ Δ' (castᵛ ei V) (castᶜ ei M)
                                       (castᶜ (exN ei) N) p) ⟩
    castᶜ eo (recL (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ Δ' (castᶜ ei M))
                   (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N)) p)
  ≡⟨ cast-recL eo ⟩
    recL (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
         (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
         (castᶜ (exN eo) (env-Cˢ γ (stepΔ Δ') (castᶜ (exN ei) N))) p
  ≡⟨ cong (λ z → recL (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
                      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) z p)
          (trans (castᶜ-irr (exN eo) eoN _)
                 (cong (λ z → castᶜ eoN (env-Cˢ γ (stepΔ Δ') z))
                       (castᶜ-irr (exN ei) eiN N))) ⟩
    recL (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
         (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
         (castᶜ eoN (env-Cˢ γ (stepΔ Δ') (castᶜ eiN N))) p
   ∎
  where
    stepΔ : Ctx → Ctx
    stepΔ X = (X ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eoN = sym (++ᶜ-assoc (toCtx St) Δ₁ (stepΔ Δ))
    eiN = ++ᶜ-assoc Γ Δ₁ (stepΔ Δ)
    exN = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong stepΔ e

env-Cˢ-recL {A = A} {B = B} {ε = ε} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M N p =
  begin
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (recL V M N p)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-recL eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (recL (castᵛ eA V) (castᶜ eA M) (castᶜ (exN eA) N) p))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-recL γ Δ₁ (castᵛ eA V) (castᶜ eA M) (castᶜ (exN eA) N) p) ⟩
    sub-atᶜ Δ (castᶜ eIn (recL (env-Vˢ γ Δ₁ (castᵛ eA V))
                               (env-Cˢ γ Δ₁ (castᶜ eA M))
                               (env-Cˢ γ (stepΔ Δ₁) (castᶜ (exN eA) N)) p)) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-recL eIn) ⟩
    sub-atᶜ Δ (recL (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))
                    (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M)))
                    (castᶜ (exN eIn) (env-Cˢ γ (stepΔ Δ₁) (castᶜ (exN eA) N))) p) W
  ≡⟨ cong (λ z → recL (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
                      (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
                      (sub-atᶜ (stepΔ Δ) z W) p)
          (trans (castᶜ-irr (exN eIn) eInN _)
                 (cong (λ z → castᶜ eInN (env-Cˢ γ (stepΔ Δ₁) z))
                       (castᶜ-irr (exN eA) eAN N))) ⟩
    recL (sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) W)
         (sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) W)
         (sub-atᶜ (stepΔ Δ) (castᶜ eInN (env-Cˢ γ (stepΔ Δ₁) (castᶜ eAN N))) W) p
  ∎
  where
    stepΔ : Ctx → Ctx
    stepΔ X = (X ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eInN  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (stepΔ Δ))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eAN   = ++ᶜ-assoc Γ ([] ∷ A₀) (stepΔ Δ)
    exN   = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong stepΔ e


env-Cˢ-box : ∀ {St Γ A C ρ} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⟨ ρ ⟩ ⊢V⦂ A)
           → (M : (Γ ++ᶜ Δ) ∷ [ ρ ] A ⊢C⦂ C)
           → env-Cˢ γ Δ (box _ V M)
           ≡ box _ (env-Vˢ γ (Δ ⟨ ρ ⟩) V) (env-Cˢ γ (Δ ∷ [ ρ ] A) M)

env-Cˢ-box ⌊ St ⌋ Δ V M = refl
env-Cˢ-box (reachᵉ γ q) Δ V M = cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-box γ Δ V M)

env-Cˢ-box {A = A} {ρ = ρ} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ'} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (box _ (V) (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-box ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (box _ (castᵛ (exV ei) V) (castᶜ (exM ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-box γ Δ' (castᵛ (exV ei) V) (castᶜ (exM ei) M)) ⟩
      castᶜ eo (box _ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V)) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cast-box eo ⟩
      box _ (castᵛ (exV eo) (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box _ (z) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
            (castᵛ-irr (exV eo) eoV₂ _) ⟩
      box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (z))
            (castᶜ-irr (exM eo) eoM₂ _) ⟩
      box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) z)) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
            (castᵛ-irr (exV ei) eiV₂ V) ⟩
      box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) z)))
            (castᶜ-irr (exM ei) eiM₂ M) ⟩
      box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ eiM₂ M)))
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
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (box _ (V) (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-box ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (box _ (castᵛ (exV ei) V) (castᶜ (exM ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-box γ Δ' (castᵛ (exV ei) V) (castᶜ (exM ei) M)) ⟩
    castᶜ eo (box _ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V)) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cast-box eo ⟩
    box _ (castᵛ (exV eo) (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box _ (z) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
          (castᵛ-irr (exV eo) eoV₂ _) ⟩
    box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (z))
          (castᶜ-irr (exM eo) eoM₂ _) ⟩
    box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) z)) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
          (castᵛ-irr (exV ei) eiV₂ V) ⟩
    box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) z)))
          (castᶜ-irr (exM ei) eiM₂ M) ⟩
    box _ (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ eiM₂ M)))
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
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (box _ (V) (M))))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-box eA) ⟩
    sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁
                (box _ (castᵛ (exV eA) V) (castᶜ (exM eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
          (env-Cˢ-box γ Δ₁ (castᵛ (exV eA) V) (castᶜ (exM eA) M)) ⟩
    sub-atᶜ Δ (castᶜ eIn (box _ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))
                            (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M)))) W
  ≡⟨ cong (λ z → sub-atᶜ Δ z W) (cast-box eIn) ⟩
    sub-atᶜ Δ (box _ (castᵛ (exV eIn) (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V)))
                 (castᶜ (exM eIn)
                    (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M)))) W
  ≡⟨ cong (λ z → box _ (sub-atᵛ (Δ ⟨ ρ ⟩) z W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A)
                      (castᶜ (exM eIn)
                         (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W))
          (castᵛ-irr (exV eIn) eInV₂ _) ⟩
    box _ (sub-atᵛ (Δ ⟨ ρ ⟩)
           (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) W)
      (sub-atᶜ (Δ ∷ [ ρ ] A)
         (castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W)
  ≡⟨ cong (λ z → box _ (sub-atᵛ (Δ ⟨ ρ ⟩)
                        (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A) z W))
          (castᶜ-irr (exM eIn) eInM₂ _) ⟩
    box _ (sub-atᵛ (Δ ⟨ ρ ⟩)
           (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) W)
      (sub-atᶜ (Δ ∷ [ ρ ] A)
         (castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W)
  ≡⟨ cong (λ z → box _ (sub-atᵛ (Δ ⟨ ρ ⟩)
                        (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) z)) W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A)
                      (castᶜ eInM₂
                         (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W))
          (castᵛ-irr (exV eA) eAV₂ V) ⟩
    box _ (sub-atᵛ (Δ ⟨ ρ ⟩)
           (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) W)
      (sub-atᶜ (Δ ∷ [ ρ ] A)
         (castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) W)
  ≡⟨ cong (λ z → box _ (sub-atᵛ (Δ ⟨ ρ ⟩)
                        (castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) W)
                   (sub-atᶜ (Δ ∷ [ ρ ] A)
                      (castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) z)) W))
          (castᶜ-irr (exM eA) eAM₂ M) ⟩
    box _ (sub-atᵛ (Δ ⟨ ρ ⟩)
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

-- The action, at the empty suffix.

env-V : ∀ {St Γ A} → Env St Γ → Γ ⊢V⦂ A → toCtx St ⊢V⦂ A
env-V γ V = env-Vˢ γ [] V

env-C : ∀ {St Γ C} → Env St Γ → Γ ⊢C⦂ C → toCtx St ⊢C⦂ C
env-C γ M = env-Cˢ γ [] M

env-C-id : ∀ {St C} → (M : toCtx St ⊢C⦂ C) → env-C ⌊ St ⌋ M ≡ M
env-C-id M = refl

-- The action commutes with substituting a telescope entry, definitionally:
-- at the empty suffix every cast is `refl` (`++ᶜ-assoc Γ Γ' []` is, and so is
-- `cong₂ _++ᶜ_ refl refl`) and the variable is `Hd`.

env-Cˢ-head : ∀ {St Γ A C} → (γ : Env St Γ) → (M : Γ ∷ A ⊢C⦂ C)
            → (W : toCtx St ⊢V⦂ A)
            → (env-Cˢ γ ([] ∷ A) M) [ split-[] ↦ W ]c ≡ env-C (γ ∷ᵉ W) M
env-Cˢ-head γ M W = refl

-- A clause lives over the ambient under the barrier lock and the clause's two
-- binders (`Dcl`), an ordinary suffix, so the action on a family is the action
-- at that suffix.

env-Hˢ : ∀ {St Γ B} → (γ : Env St Γ) → (Δ : Ctx)
       → Fam B ((Γ ++ᶜ Δ) ⟨ ⊤ᵣ ⟩) → Fam B ((toCtx St ++ᶜ Δ) ⟨ ⊤ᵣ ⟩)
env-Hˢ {B = B} γ Δ K op ε = env-Cˢ γ (Δ ++ᶜ Dcl B op ε) (K op ε)

-- The clause transport `cast-handler` produces and the one the suffix
-- `Δ ++ᶜ Dcl` asks for prove the same equation.

Cl-cast-irr : ∀ {Γ₀ Γ₀' B} {op : Op} {ε : E} → (e : Γ₀ ≡ Γ₀')
            → (e' : Γ₀ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                       ∷ [ ∣ op-grade op ∣ᵉ ]
                           (⌜ arity op ⌝ᵍ ⇒ B ! ε)
                  ≡ Γ₀' ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                       ∷ [ ∣ op-grade op ∣ᵉ ]
                           (⌜ arity op ⌝ᵍ ⇒ B ! ε))
            → (X : Cl B op ε (Γ₀ ⟨ ⊤ᵣ ⟩))
            → Cl-cast op ε e X ≡ castᶜ e' X
Cl-cast-irr e e' X = castᶜ-irr _ e' X

-- Every zone acts on the clauses exactly as it acts under any other suffix;
-- what is left is that its transports and the ones `cast-handler` produces are
-- the same by `uip`.

env-Vˢ-handler : ∀ {St Γ A B ε ε'} → (γ : Env St Γ) → (Δ : Ctx)
               → (N : (Γ ++ᶜ Δ) ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
               → (H : Fam B ((Γ ++ᶜ Δ) ⟨ ⊤ᵣ ⟩))
               → env-Vˢ γ Δ (handler N H)
               ≡ handler (env-Cˢ γ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) N) (env-Hˢ γ Δ H)

env-Vˢ-handler ⌊ St ⌋ Δ N H = refl
env-Vˢ-handler (reachᵉ γ q) Δ N H =
  cong (V-rename (cong-ren (reach-renᵘ q))) (env-Vˢ-handler γ Δ N H)

env-Vˢ-handler {A = A} {B = B} {ε = ε}
              (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ N H =
  cong (V-rename (cong-ren (unbox-ren q)))
    (trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-handler ei))
      (trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' (handler z Hi)))
                   (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) ei) ei₂ N))
        (trans (cong (castᵛ eo) (env-Vˢ-handler γ Δ' _ _))
          (trans (cast-handler eo)
                 (handler-≡ (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) eo) eo₂ _)
                            cl)))))
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)

    Hi  = λ op ε₀ → Cl-cast op ε₀ ei (H op ε₀)

    cl : ∀ op ε₀
       → Cl-cast op ε₀ eo
           (env-Cˢ γ (Δ' ++ᶜ Dcl B op ε₀) (Cl-cast op ε₀ ei (H op ε₀)))
       ≡ castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ++ᶜ Dcl B op ε₀)))
           (env-Cˢ γ (Δ' ++ᶜ Dcl B op ε₀)
             (castᶜ (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ++ᶜ Dcl B op ε₀)) (H op ε₀)))
    cl op ε₀ =
      trans (Cl-cast-irr eo (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) D)) _)
            (cong (λ z → castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) D))
                           (env-Cˢ γ (Δ' ++ᶜ Dcl B op ε₀) z))
                  (Cl-cast-irr ei (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) D) (H op ε₀)))
      where
        D = Δ ++ᶜ Dcl B op ε₀

env-Vˢ-handler {A = A} {B = B} {ε = ε}
              (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ N H =
  trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-handler ei))
    (trans (cong (λ z → castᵛ eo (env-Vˢ γ Δ' (handler z Hi)))
                 (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) ei) ei₂ N))
      (trans (cong (castᵛ eo) (env-Vˢ-handler γ Δ' _ _))
        (trans (cast-handler eo)
               (handler-≡ (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) eo) eo₂ _)
                          cl))))
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)

    Hi  = λ op ε₀ → Cl-cast op ε₀ ei (H op ε₀)

    cl : ∀ op ε₀
       → Cl-cast op ε₀ eo
           (env-Cˢ γ (Δ' ++ᶜ Dcl B op ε₀) (Cl-cast op ε₀ ei (H op ε₀)))
       ≡ env-Hˢ (liftᵉ V γ) Δ H op ε₀
    cl op ε₀ =
      trans (Cl-cast-irr eo (sym (++ᶜ-assoc (toCtx St) Δ₁ D)) _)
            (cong (λ z → castᶜ (sym (++ᶜ-assoc (toCtx St) Δ₁ D))
                           (env-Cˢ γ (Δ' ++ᶜ Dcl B op ε₀) z))
                  (Cl-cast-irr ei (++ᶜ-assoc Γ Δ₁ D) (H op ε₀)))
      where
        D = Δ ++ᶜ Dcl B op ε₀

env-Vˢ-handler {A = A} {B = B} {ε = ε}
              (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ N H =
  trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ' z)) W)
              (cast-handler eA))
    (trans (cong (λ z → sub-atᵛ Δ
                          (castᵛ eIn (env-Vˢ γ Δ' (handler z Hi))) W)
                 (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) eA) eA₂ N))
      (trans (cong (λ z → sub-atᵛ Δ (castᵛ eIn z) W)
                   (env-Vˢ-handler γ Δ' _ _))
        (trans (cong (λ z → sub-atᵛ Δ z W) (cast-handler eIn))
               (handler-≡
                 (cong (λ z → sub-atᶜ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) z W)
                       (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) eIn)
                                  eIn₂ Nγ))
                 cl))))
  where
    Δ₁   = [] ∷ A₀
    Δ'   = Δ₁ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    eA   = ++ᶜ-assoc Γ Δ₁ Δ
    eIn₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A))
    eA₂  = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A)

    Hi  = λ op ε₀ → Cl-cast op ε₀ eA (H op ε₀)
    Nγ  = env-Cˢ γ (Δ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) (castᶜ eA₂ N)

    cl : ∀ op ε₀
       → sub-atᶜ (Δ ++ᶜ Dcl B op ε₀)
           (Cl-cast op ε₀ eIn
             (env-Cˢ γ (Δ' ++ᶜ Dcl B op ε₀) (Hi op ε₀)))
           W
       ≡ env-Hˢ (γ ∷ᵉ W) Δ H op ε₀
    cl op ε₀ =
      cong (λ z → sub-atᶜ D z W)
        (trans (Cl-cast-irr eIn (sym (++ᶜ-assoc (toCtx St) Δ₁ D)) _)
               (cong (λ z → castᶜ (sym (++ᶜ-assoc (toCtx St) Δ₁ D))
                              (env-Cˢ γ (Δ' ++ᶜ Dcl B op ε₀) z))
                     (Cl-cast-irr eA (++ᶜ-assoc Γ Δ₁ D) (H op ε₀))))
      where
        D = Δ ++ᶜ Dcl B op ε₀

env-Cˢ-handle : ∀ {St Γ A B ε ε'} → (γ : Env St Γ) → (Δ : Ctx)
              → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ! ε)
              → (V : (Γ ++ᶜ Δ) ⊢V⦂ (A ! ε) ⇛ (B ! ε'))
              → env-Cˢ γ Δ (handle M `with V)
              ≡ handle (env-Cˢ γ Δ M) `with (env-Vˢ γ Δ V)

env-Cˢ-handle ⌊ St ⌋ Δ M V = refl
env-Cˢ-handle (reachᵉ γ q) Δ M V =
  cong (C-rename (cong-ren (reach-renᵘ q))) (env-Cˢ-handle γ Δ M V)

env-Cˢ-handle (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M V =
  cong (C-rename (cong-ren (unbox-ren q)))
    (trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-handle ei))
      (trans (cong (castᶜ eo) (env-Cˢ-handle γ Δ' (castᶜ ei M) (castᵛ ei V)))
             (cast-handle eo)))
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-handle (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ M V =
  trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-handle ei))
    (trans (cong (castᶜ eo) (env-Cˢ-handle γ Δ' (castᶜ ei M) (castᵛ ei V)))
           (cast-handle eo))
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-handle (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M V =
  trans (cong (λ z → sub-atᶜ Δ (castᶜ eIn (env-Cˢ γ Δ₁ z)) W) (cast-handle eA))
    (trans (cong (λ z → sub-atᶜ Δ (castᶜ eIn z) W)
                 (env-Cˢ-handle γ Δ₁ (castᶜ eA M) (castᵛ eA V)))
           (cong (λ z → sub-atᶜ Δ z W) (cast-handle eIn)))
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

