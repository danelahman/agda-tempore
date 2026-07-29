------------------------------------------------------------------------
-- The action on a variable, and its respect for the term equivalence.
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

module OperationalSemantics.Adequacy.Environment.Variables (Spec : LanguageSpec) where

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
open import Syntax.Substitutions.Weakening Spec
open import Syntax.Substitutions.Renaming  Spec
open import Syntax.Substitutions.Swap      Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec
open import OperationalSemantics.Adequacy.Environment.Core Spec
open import OperationalSemantics.Adequacy.Environment.Action Spec

------------------------------------------------------------------------
-- THE ACTION RESPECTS THE TERM EQUIVALENCE
--
-- Recursion on the environment, not on the term: each zone acts by renaming
-- and substitution, both of which are congruences (`V-rename-cong`, `sub-≐ᵛ`).
------------------------------------------------------------------------

env-eternal-V-≐ : ∀ {Δ Γ A} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → {V V' : (Δ ++ᶜ Γ) ⊢V⦂ A} → V ≐ᵛ V'
                → env-eternal-V lf η V ≐ᵛ env-eternal-V lf η V'

env-eternal-V-≐ lf-[]              η eV = castᵛ-≐ ++ᶜ-identityˡ eV
env-eternal-V-≐ {Δ ∷ B} {Γ} (lf-∷ lf) η eV =
  env-eternal-V-≐ lf (λ x → η (Tl-∷ x))
    (castᵛ-≐ _ (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Δ ∷ B} {Γ})) (≐ᵛ-refl _) eV))

env-Vˢ-≐ : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx) → {V V' : (Γ ++ᶜ Δ) ⊢V⦂ A}
         → V ≐ᵛ V' → env-Vˢ γ Δ V ≐ᵛ env-Vˢ γ Δ V'

env-Vˢ-≐ ⌊ St ⌋       Δ eV = eV
env-Vˢ-≐ (∅ᵉ St)       Δ eV = V-rename-cong _ eV
env-Vˢ-≐ (reachᵉ γ q) Δ eV = V-rename-cong _ (env-Vˢ-≐ γ Δ eV)
env-Vˢ-≐ (γ ⟨ q ⟩ᵉ)    Δ eV =
  V-rename-cong _ (castᵛ-≐ _ (env-Vˢ-≐ γ _ (castᵛ-≐ _ eV)))
env-Vˢ-≐ (liftᵉ V γ)   Δ eV = castᵛ-≐ _ (env-Vˢ-≐ γ _ (castᵛ-≐ _ eV))
env-Vˢ-≐ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ eV =
  castᵛ-≐ (cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t))
    (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl (castᵛ (sym (split→∈-split-l t)) W))
      (castᵛ-≐ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
        (env-Vˢ-≐ γ ([] ∷ A ++ᶜ Δ) (castᵛ-≐ (++ᶜ-assoc Γ ([] ∷ A) Δ) eV))))
  where
    t = split-≡-++ᶜ {toCtx St ∷ A} {Δ}
env-Vˢ-≐ (eternalˡ Δ₀ lf η γ) Δ eV =
  env-Vˢ-≐ γ Δ (env-eternal-V-≐ lf η (castᵛ-≐ _ eV))


-- The eternal zone leaves the variables of the context it prefixes alone: each
-- of its substitutions replaces a variable of its own prefix (`sub-var-r`).

env-eternal-V-var-r : ∀ {Δ₀ Γ' A ρ} → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                    → (x : A ∈[ ρ ] Γ') → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
                    → env-eternal-V lf η (var f (∈-++ᶜʳ {Γ = Δ₀} x)) ≐ᵛ var f' x

env-eternal-V-var-r lf-[] η x f f' =
  ≐ᵛ-trans (≡→≐ᵛ (trans (castᵛ-var ++ᶜ-identityˡ f (∈-++ᶜʳ x))
                        (cong (var f) (∈-++ᶜʳ-[] x))))
           var-≐

env-eternal-V-var-r (lf-∷ lf) η x f f' =
  ≐ᵛ-trans (env-eternal-V-≐ lf (λ z → η (Tl-∷ z)) (sub-var-r _ x _ f f))
           (env-eternal-V-var-r lf (λ z → η (Tl-∷ z)) x f f')



-- THE ACTION FIXES A SUFFIX VARIABLE
--
-- Recursion on the environment. Each zone either renames along a congruence
-- renaming (`ren-var-r`) or substitutes at a variable of the prefix
-- (`sub-var-r`); the two zones that re-bracket the suffix pass through
-- `∈-++ᶜʳ-assoc`.

env-Vˢ-var-r : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx) → (x : A ∈[ ρ ] Δ)
             → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → env-Vˢ γ Δ (var f (∈-++ᶜʳ {Γ = Γ} x))
             ≐ᵛ var f' (∈-++ᶜʳ {Γ = toCtx St} x)

env-Vˢ-var-r ⌊ St ⌋ Δ x f f' = var-≐
env-Vˢ-var-r (∅ᵉ St) Δ x f f' = ren-var-r (∅-ren St) x f f'

env-Vˢ-var-r (reachᵉ γ q) Δ x f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren (reach-renᵘ q)) (env-Vˢ-var-r γ Δ x f f))
           (ren-var-r (reach-renᵘ q) x f f')

env-Vˢ-var-r (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ x f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren (unbox-ren q)) step)
           (ren-var-r (unbox-ren q) x f f')
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    y  = ∈-++ᶜʳ {Γ = [] ⟨ ρ ⟩} x

    inner : castᵛ ei (var f (∈-++ᶜʳ {Γ = Γ ⟨ ρ ⟩} x))
          ≡ var f (∈-++ᶜʳ {Γ = Γ} y)
    inner = trans (castᵛ-var ei f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Γ ([] ⟨ ρ ⟩) x))

    outer : castᵛ eo (var f (∈-++ᶜʳ {Γ = toCtx St} y))
          ≡ var f (∈-++ᶜʳ {Γ = toCtx St ⟨ ρ ⟩} x)
    outer =
      trans (castᵛ-var eo f (∈-++ᶜʳ y))
        (cong (var f)
          (trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) eo)
                       (sym (∈-++ᶜʳ-assoc (toCtx St) ([] ⟨ ρ ⟩) x)))
                 (subst-sym-subst′ (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
                                   (∈-++ᶜʳ x))))

    step : castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (var f (∈-++ᶜʳ {Γ = Γ ⟨ ρ ⟩} x))))
         ≐ᵛ var f (∈-++ᶜʳ {Γ = toCtx St ⟨ ρ ⟩} x)
    step =
      ≐ᵛ-trans (≡→≐ᵛ (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) inner))
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ Δ' y f f)) (≡→≐ᵛ outer))

env-Vˢ-var-r (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ x f f' =
  ≐ᵛ-trans (≡→≐ᵛ (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) inner))
    (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ Δ' y f f))
      (≐ᵛ-trans (≡→≐ᵛ outer) var-≐))
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    y  = ∈-++ᶜʳ {Γ = Δ₁} x

    inner : castᵛ ei (var f (∈-++ᶜʳ {Γ = Γ ∷ [ ρ ] A₀} x))
          ≡ var f (∈-++ᶜʳ {Γ = Γ} y)
    inner = trans (castᵛ-var ei f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Γ Δ₁ x))

    outer : castᵛ eo (var f (∈-++ᶜʳ {Γ = toCtx St} y))
          ≡ var f (∈-++ᶜʳ {Γ = toCtx St ∷ [ ρ ] A₀} x)
    outer =
      trans (castᵛ-var eo f (∈-++ᶜʳ y))
        (cong (var f)
          (trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) eo)
                       (sym (∈-++ᶜʳ-assoc (toCtx St) Δ₁ x)))
                 (subst-sym-subst′ (++ᶜ-assoc (toCtx St) Δ₁ Δ) (∈-++ᶜʳ x))))

env-Vˢ-var-r (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ x f f' =
  ≐ᵛ-trans (≡→≐ᵛ (cong (λ z → castᵛ (castOf Δ)
                                (castᵛ eIn (env-Vˢ γ Δ'' z) [ split→∈ t ↦ Ŵ ]v))
                       inner))
    (≐ᵛ-trans
      (castᵛ-≐ (castOf Δ)
        (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl Ŵ)
          (≐ᵛ-trans (castᵛ-≐ eIn (env-Vˢ-var-r γ Δ'' y f f)) (≡→≐ᵛ outer))))
      (sub-var-r Δ x Ŵ f f'))
  where
    Δ'' = [] ∷ A₀ ++ᶜ Δ
    eIn = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA  = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    t   = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    Ŵ   = castᵛ (sym (split→∈-split-l t)) W
    y   = ∈-++ᶜʳ {Γ = [] ∷ A₀} x

    inner : castᵛ eA (var f (∈-++ᶜʳ {Γ = Γ ∷ A₀} x))
          ≡ var f (∈-++ᶜʳ {Γ = Γ} y)
    inner = trans (castᵛ-var eA f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Γ ([] ∷ A₀) x))

    outer : castᵛ eIn (var f (∈-++ᶜʳ {Γ = toCtx St} y))
          ≡ var f (∈-++ᶜʳ {Γ = toCtx St ∷ A₀} x)
    outer =
      trans (castᵛ-var eIn f (∈-++ᶜʳ y))
        (cong (var f)
          (trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) eIn)
                       (sym (∈-++ᶜʳ-assoc (toCtx St) ([] ∷ A₀) x)))
                 (subst-sym-subst′ (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
                                   (∈-++ᶜʳ x))))

env-Vˢ-var-r (eternalˡ {Γ = Γ} Δ₀ lf η γ) Δ x f f' =
  ≐ᵛ-trans
    (env-Vˢ-≐ γ Δ
      (≐ᵛ-trans (≡→≐ᵛ (cong (env-eternal-V lf η) inner))
                (env-eternal-V-var-r lf η (∈-++ᶜʳ {Γ = Γ} x) f f)))
    (env-Vˢ-var-r γ Δ x f f')
  where
    inner : castᵛ (++ᶜ-assoc Δ₀ Γ Δ) (var f (∈-++ᶜʳ {Γ = Δ₀ ++ᶜ Γ} x))
          ≡ var f (∈-++ᶜʳ {Γ = Δ₀} (∈-++ᶜʳ {Γ = Γ} x))
    inner = trans (castᵛ-var (++ᶜ-assoc Δ₀ Γ Δ) f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Δ₀ Γ x))

------------------------------------------------------------------------
-- THE ACTION ON A VARIABLE
--
-- What each zone does to a variable of its own context. The bounds are left
-- free: `_≐ᵛ_` does not see them, and each caller has its own.
------------------------------------------------------------------------

-- A telescope entry is substituted by its value: at the empty suffix the
-- action is `env-Vˢ γ ([] ∷ A)` followed by substituting `Hd`, and the entry's
-- own variable is a suffix variable.

env-var-hd : ∀ {St Γ A} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A)
           → (f : ¬ Eternal A → uᵣ ≾ᵣ uᵣ)
           → env-V (γ ∷ᵉ W) (var f Hd) ≐ᵛ W
env-var-hd γ W f =
  sub-≐ᵛ Hd (≐ᵛ-refl W) (env-Vˢ-var-r γ ([] ∷ _) Hd f f)

-- Any other variable is untouched by the entry, and is the action of the rest.
--
-- Both are the same lemma at a one-entry suffix: the action under a suffix `Δ`
-- of a variable of the *prefix* is the action at the empty suffix, pushed under
-- `Δ` by `push-ren`. The suffix must be arbitrary, because `env-Vˢ` grows it at
-- `_⟨_⟩ᵉ` and `_∷ᵉ_`; `push-ren` is pinned up to `_≐ʳ_` by `push-ren-tgt`, which
-- is why no renaming needs to be quantified over.
--
-- The two zones that grow the suffix use the induction hypothesis **twice** —
-- at `[] ∷ A ++ᶜ Δ` (resp. `[] ⟨ ρ ⟩ ++ᶜ Δ`) for the goal's left side and at
-- `[] ∷ A` (resp. `[] ⟨ ρ ⟩`) for its right, whose own action is at suffix `[]`.
-- Both land on the same `env-Vˢ γ [] (var _ x)`, leaving an equation between two
-- composite renamings, which `push-ren-++ᶜ` and `push-ren-nat` settle.
--
-- `¬ Eternal A` is what makes the lock case go through: it supplies the lock's
-- own bound by `≾ᵣ-zero-product*`, where at an eternal type `f` is vacuous. It
-- also rules out `eternalˡ`'s prefix, whose every variable is eternal — which is
-- what `Eternal-Env` is for.

env-Vˢ-var-l : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → Eternal-Env γ → ¬ Eternal A
             → (p : ctx-grade Δ ≾ᵣ uᵣ)
             → (x : A ∈[ ρ ] Γ)
             → (f  : ¬ Eternal A → grade-++ᶜˡ ρ Δ ≾ᵣ uᵣ)
             → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → env-Vˢ γ Δ (var f (∈-++ᶜˡ Δ x))
             ≐ᵛ V-rename (push-ren Δ p) (env-Vˢ γ [] (var f' x))

env-Vˢ-var-l ⌊ St ⌋ Δ eγ ¬et p x f f' =
  ≐ᵛ-sym (var-ren-tgt-≐ (push-ren Δ p) x f' (push-ren-tgt Δ p x) f)

env-Vˢ-var-l (∅ᵉ St) Δ eγ ¬et p x f f' = ⊥-elim (not-in-empty-ctx x)

env-Vˢ-var-l (reachᵉ γ q) Δ eγ ¬et p x f f' =
  ≐ᵛ-trans
    (V-rename-cong (cong-ren {Γ'' = Δ} (reach-renᵘ q))
                   (env-Vˢ-var-l γ Δ eγ ¬et p x f f'))
    (≐ᵛ-trans
      (≐ᵛ-sym (V-rename-∘ (cong-ren {Γ'' = Δ} (reach-renᵘ q)) (push-ren Δ p) _))
      (≐ᵛ-trans (V-rename-≐ (push-ren-nat (reach-renᵘ q) Δ p) _)
                (V-rename-∘ (push-ren Δ p) (reach-renᵘ q) _)))

env-Vˢ-var-l (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₁} γ q) Δ eγ ¬et p (Tl-⟨⟩ x) f f' =
  ≐ᵛ-trans
    (V-rename-cong (cong-ren {Γ'' = Δ} (unbox-ren q))
      (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) eγ ¬et p₁ x f₁ f''))
          (≐ᵛ-trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
            (≐ᵛ-trans (V-rename-≐ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
                      (V-rename-∘ (push-ren Δ p) (push-ren Δ₁ pₗ) _))))))
    (≐ᵛ-trans
      (≐ᵛ-sym (V-rename-∘ (cong-ren {Γ'' = Δ} (unbox-ren q)) (push-ren Δ p) _))
      (≐ᵛ-trans (V-rename-≐ (push-ren-nat (unbox-ren q) Δ p) _)
        (≐ᵛ-trans (V-rename-∘ (push-ren Δ p) (unbox-ren q) _)
          (V-rename-cong (push-ren Δ p)
            (V-rename-cong (unbox-ren q)
              (≐ᵛ-sym (env-Vˢ-var-l γ Δ₁ eγ ¬et pₗ x f' f'')))))))
  where
    Δ₁ = [] ⟨ ρ₁ ⟩
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

    pρ = ≾ᵣ-zero-productʳ (grade-++ᶜˡ-zeroˡ Δ (f ¬et))
    pₗ = ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ₁)) pρ
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁  = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)
    f'' = λ z → ≾ᵣ-zero-productˡ (grade-++ᶜˡ-zeroˡ Δ (f z))

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Tgt-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The cell zone: nothing is substituted, so both sides re-bracket and the
-- comparison is `push-ren-++ᶜ` alone.

env-Vˢ-var-l (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₁} V γ) Δ eγ ¬et p (Tl-∷ x) f f' =
  ≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
    (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) eγ ¬et p₁ x f₁ f'))
      (≐ᵛ-trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
        (≐ᵛ-trans (V-rename-≐ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
          (≐ᵛ-trans (V-rename-∘ (push-ren Δ p) (push-ren Δ₁ pₗ) _)
            (V-rename-cong (push-ren Δ p)
              (≐ᵛ-sym (env-Vˢ-var-l γ Δ₁ eγ ¬et pₗ x f' f')))))))
  where
    Δ₁ = [] ∷ [ ρ₁ ] A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

    pₗ = ≾ᵣ-refl
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁ = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Tgt-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The cell's own variable: a *suffix* variable of the inner action, carried
-- through unchanged since nothing is substituted.

env-Vˢ-var-l (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₁} V γ) Δ eγ ¬et p Hd f f' =
  ≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
    (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ (Δ₁ ++ᶜ Δ) hd f f))
      (≐ᵛ-trans outer
        (≐ᵛ-sym
          (≐ᵛ-trans
            (V-rename-cong (push-ren Δ p)
              (env-Vˢ-var-r γ Δ₁ (Hd {Γ = []}) f' f'))
            (var-ren-tgt-≐ (push-ren Δ p) (Hd {Γ = toCtx St}) f'
                           (push-ren-tgt Δ p Hd) f)))))
  where
    Δ₁ = [] ∷ [ ρ₁ ] A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    hd = ∈-++ᶜˡ {Γ = Δ₁} Δ (Hd {Γ = []})

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Γ} (Hd {Γ = []})))
              (∈-++ᶜʳ {Γ = Γ} hd) (∈-++ᶜˡ-++ᶜʳ Γ Δ₁ Δ (Hd {Γ = []})) f f

    outer = castᵛ-var-Tgt eo (∈-++ᶜʳ {Γ = toCtx St} hd)
              (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
              (Tgt-cast-flip (++ᶜ-assoc (toCtx St) Δ₁ Δ) _ _
                             (∈-++ᶜˡ-++ᶜʳ (toCtx St) Δ₁ Δ (Hd {Γ = []})))
              f f

env-Vˢ-var-l (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ eγ ¬et p (Tl-∷ x) f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {toCtx St} {A₀} Δ)
      (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl _)
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
          (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) eγ ¬et p₁ x f₁ f'))
            (≐ᵛ-trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
              (≐ᵛ-trans (V-rename-≐ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
                (≐ᵛ-trans
                  (V-rename-≐
                    (≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (push-ren-∷ pₗ))
                              (≐ʳ-sym (push-ren-nat wk-ren Δ p))) _)
                  (V-rename-∘ (cong-ren {Γ'' = Δ} wk-ren) (push-ren Δ p) _))))))))
    (≐ᵛ-trans (sub-wk-V Δ (V-rename (push-ren Δ p) Z) _)
      (V-rename-cong (push-ren Δ p)
        (≐ᵛ-sym
          (≐ᵛ-trans
            (castᵛ-≐ (castOf {toCtx St} {A₀} [])
              (sub-≐ᵛ (split→∈ t₀) (≐ᵛ-refl _)
                (≐ᵛ-trans (env-Vˢ-var-l γ Δ₁ eγ ¬et pₗ x f' f')
                          (V-rename-≐ (push-ren-∷ pₗ) _))))
            (sub-wk-V [] Z _)))))
  where
    Δ₁ = [] ∷ A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    t  = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    t₀ = split-≡-++ᶜ {toCtx St ∷ A₀} {[]}
    Z  = env-Vˢ γ [] (var f' x)

    pₗ = ≾ᵣ-refl
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁ = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Tgt-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The entry's own variable: a *suffix* variable of the inner action, which the
-- substitution then hits (`sub-var-hit′`), returning the entry's value pushed
-- under `Δ`. At the empty suffix that is `env-var-hd`.

env-Vˢ-var-l (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ eγ ¬et p Hd f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {toCtx St} {A₀} Δ)
      (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl _)
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
          (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ (Δ₁ ++ᶜ Δ) hd f f))
                    outer))))
    (≐ᵛ-trans
      (sub-var-hit′ Δ ¬et p (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
                    (sym (split→∈-∈-++ᶜˡ (toCtx St) A₀ Δ)) _ f)
      (≐ᵛ-trans (V-rename-cong (push-ren Δ p)
                  (≡→≐ᵛ (castᵛ-sym-cast (split→∈-split-l t) W)))
                (V-rename-cong (push-ren Δ p) (≐ᵛ-sym (env-var-hd γ W f')))))
  where
    Δ₁ = [] ∷ A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    t  = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    hd = ∈-++ᶜˡ {Γ = Δ₁} Δ (Hd {Γ = []})

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Γ} (Hd {Γ = []})))
              (∈-++ᶜʳ {Γ = Γ} hd) (∈-++ᶜˡ-++ᶜʳ Γ Δ₁ Δ (Hd {Γ = []})) f f

    outer = castᵛ-var-Tgt eo (∈-++ᶜʳ {Γ = toCtx St} hd)
              (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
              (Tgt-cast-flip (++ᶜ-assoc (toCtx St) Δ₁ Δ) _ _
                             (∈-++ᶜˡ-++ᶜʳ (toCtx St) Δ₁ Δ (Hd {Γ = []})))
              f f

-- An eternal prefix's variables are all eternal, so `¬ Eternal A` puts `x` in
-- the context it prefixes, where the prefix's substitutions leave it alone.

env-Vˢ-var-l (eternalˡ {Γ = Γ} Δ₀ lf η γ) Δ (eγ , et) ¬et p x f f'
  with ∈-++ᶜ-split Δ₀ Γ x in eq

... | inj₁ (ρ' , y) = ⊥-elim (¬et (et y))

... | inj₂ y
  rewrite ∈-++ᶜ-split-inj₂ Δ₀ Γ x y eq =
  ≐ᵛ-trans
    (env-Vˢ-≐ γ Δ
      (≐ᵛ-trans (env-eternal-V-≐ lf η inner)
                (env-eternal-V-var-r lf η (∈-++ᶜˡ {Γ = Γ} Δ y) f f)))
    (≐ᵛ-trans (env-Vˢ-var-l γ Δ eγ ¬et p y f f')
      (V-rename-cong (push-ren Δ p)
        (env-Vˢ-≐ γ []
          (≐ᵛ-sym (env-eternal-V-var-r lf η y f' f')))))
  where
    inner = castᵛ-var-Tgt (++ᶜ-assoc Δ₀ Γ Δ)
              (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Δ₀} y))
              (∈-++ᶜʳ {Γ = Δ₀} (∈-++ᶜˡ {Γ = Γ} Δ y))
              (∈-++ᶜˡ-++ᶜʳ Δ₀ Γ Δ y) f f

-- The two one-entry instances. `env-var-tl` substitutes `Hd` into a weakening,
-- which cancels (`sub-wk-V []`); `env-var-lock` composes the lock crossing with
-- the reach, which `unbox-ren-unit` recognises as the unit reach's renaming.

env-var-tl : ∀ {St Γ A A₀ ρ} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A₀)
           → Eternal-Env γ → ¬ Eternal A
           → (x : A ∈[ ρ ] Γ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → env-V (γ ∷ᵉ W) (var f (Tl-∷ x)) ≐ᵛ env-V γ (var f' x)

env-var-tl {St = St} {A₀ = A₀} γ W eγ ¬et x f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {toCtx St} {A₀} [])
      (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {toCtx St ∷ A₀} {[]})) (≐ᵛ-refl _)
        (≐ᵛ-trans (env-Vˢ-var-l γ ([] ∷ A₀) eγ ¬et ≾ᵣ-refl x f f')
                  (V-rename-≐ (push-ren-∷ ≾ᵣ-refl) _))))
    (sub-wk-V [] (env-Vˢ γ [] (var f' x)) _)

env-var-lock : ∀ {St St' Γ A ρ ρ'} → (γ : Env St Γ) → (q : St [ ρ ]⊑ₛ[ uᵣ ] St')
             → Eternal-Env γ → ¬ Eternal A
             → (p : ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ' ] Γ)
             → (f  : ¬ Eternal A → ρ' ·ᵣ ρ ≾ᵣ uᵣ)
             → (f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
             → env-V (γ ⟨ q ⟩ᵉ) (var f (Tl-⟨⟩ x))
             ≐ᵛ reach-val (reach-unit q p) (env-V γ (var f' x))

-- The cell zone's own instance: `Δ := [] ∷ [ ρ ] A₀`, where the push is the
-- weakening past the new cell and there is nothing to cancel — `liftᵉ` keeps the
-- binder rather than substituting for it.

env-var-lift : ∀ {St Γ A A₀ ρ ρ'} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A₀)
             → (γ : Env St Γ) → Eternal-Env γ → ¬ Eternal A
             → (x : A ∈[ ρ' ] Γ) → (f f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
             → env-V (liftᵉ V γ) (var f (Tl-∷ x))
             ≐ᵛ V-rename wk-ren (env-V γ (var f' x))

env-var-lift {A₀ = A₀} {ρ = ρ} V γ eγ ¬et x f f' =
  ≐ᵛ-trans (env-Vˢ-var-l γ ([] ∷ [ ρ ] A₀) eγ ¬et ≾ᵣ-refl x f f')
           (V-rename-≐ (push-ren-∷ ≾ᵣ-refl) _)

env-var-lock {ρ = ρ} γ q eγ ¬et p x f f' =
  ≐ᵛ-trans
    (V-rename-cong (unbox-ren q)
      (env-Vˢ-var-l γ ([] ⟨ ρ ⟩) eγ ¬et pₗ x f f'))
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ (unbox-ren q) (push-ren ([] ⟨ ρ ⟩) pₗ) _))
              (V-rename-≐ (≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (push-ren-⟨⟩ pₗ p))
                                    (unbox-ren-unit q p)) _))
  where
    pₗ = ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)) p

-- The eternal zone does not touch the variables of the context it prefixes.
-- `y` must be *the* variable `x` comes from: quantifying over the two
-- independently would identify any two same-typed variables of a state
-- context, since `env-V ⌊ St ⌋` is the identity.

env-var-eternalˡ : ∀ {St Γ A ρ} → (Δ : Ctx) → (lf : Lock-free Δ)
                 → (η : ClosedVals Δ) → (γ : Env St Γ)
                 → (x : A ∈[ ρ ] (Δ ++ᶜ Γ)) → (y : A ∈[ ρ ] Γ)
                 → ∈-++ᶜ-split Δ Γ x ≡ inj₂ y
                 → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
                 → env-V (eternalˡ Δ lf η γ) (var f x) ≐ᵛ env-V γ (var f y)
env-var-eternalˡ Δ lf η γ x y eq f =
  env-Vˢ-≐ γ []
    (subst (λ z → env-eternal-V lf η (var f z) ≐ᵛ var f y)
           (sym (∈-++ᶜ-split-inj₂ Δ _ x y eq))
           (env-eternal-V-var-r lf η y f f))

-- Every variable of a reducible environment's context becomes a reducible
-- value: the fundamental lemma's variable case. The eternal cases are the two
-- that need no law — `Val` holds of everything at an eternal type, which is
-- also why a locked variable of eternal type needs no reach.

env-var : ∀ {St Γ A ρ} → (γ : Env St Γ) → Rel-Env γ
        → (x : A ∈[ ρ ] Γ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        ------------------------------------------------
        → Val A St (env-V γ (var f x))

env-var ⌊ St ⌋       pγ x f = store-var pγ x f

env-var (∅ᵉ St)       pγ x f = ⊥-elim (not-in-empty-ctx x)

env-var (reachᵉ γ q) pγ x f = Val-reach q _ (env-var γ pγ x f)

env-var (γ ∷ᵉ W) (pγ , pW) Hd       f =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-hd γ W f)) pW
env-var {A = A} (γ ∷ᵉ W) (pγ , pW) (Tl-∷ x) f with eternal? A
... | yes et = Val-eternal et _
... | no ¬et =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-tl γ W (Rel-Env-eternal γ pγ) ¬et x f f))
           (env-var γ pγ x f)

env-var (liftᵉ V γ) (pγ , pV) Hd f =
  Val-≐ᵛ _ (≐ᵛ-sym (env-Vˢ-var-r γ ([] ∷ _) Hd f f)) (store-fresh V pV f)
env-var {A = A} (liftᵉ V γ) (pγ , pV) (Tl-∷ x) f with eternal? A
... | yes et = Val-eternal et _
... | no ¬et =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-lift V γ (Rel-Env-eternal γ pγ) ¬et x f f))
    (Val-≐ᵛ _ (V-rename-≐ (alloc-ren-≐ V) _)
      (Val-reach (alloc-reach V) _ (env-var γ pγ x f)))

env-var {A = A} (γ ⟨ q ⟩ᵉ) pγ (Tl-⟨⟩ x) f with eternal? A
... | yes et = Val-eternal et _
... | no ¬et =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-lock γ q (Rel-Env-eternal γ pγ) ¬et p x f f'))
           (Val-reach (reach-unit q p) _ (env-var γ pγ x f'))
  where
    p  = ≾ᵣ-zero-productʳ (f ¬et)
    f' = λ _ → ≾ᵣ-zero-productˡ (f ¬et)

env-var {A = A} (eternalˡ Δ lf η γ) (pγ , et) x f
  with ∈-++ᶜ-split Δ _ x in eq
... | inj₁ (ρ' , y) = Val-eternal (et y) _
... | inj₂ y        =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-eternalˡ Δ lf η γ x y eq f)) (env-var γ pγ y f)

