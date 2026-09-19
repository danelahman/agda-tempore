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
open import Syntax.Substitutions.At        Spec
open import Syntax.Substitutions.Clauses   Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec
open import OperationalSemantics.Adequacy.Environment.Core Spec
open import OperationalSemantics.Adequacy.Environment.Action Spec

------------------------------------------------------------------------
-- THE ACTION RESPECTS EQUALITY OF TERMS
--
-- The action is a function of the term, so this is `cong` — no recursion on
-- the environment needed.
------------------------------------------------------------------------

env-Vˢ-≡ : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx) → {V V' : (Γ ++ᶜ Δ) ⊢V⦂ A}
         → V ≡ V' → env-Vˢ γ Δ V ≡ env-Vˢ γ Δ V'
env-Vˢ-≡ γ Δ = cong (env-Vˢ γ Δ)


-- THE ACTION FIXES A SUFFIX VARIABLE
--
-- Recursion on the environment. Each zone either renames along a congruence
-- renaming (`ren-var-r`) or substitutes at a variable of the prefix
-- (`sub-var-r`); the two zones that re-bracket the suffix pass through
-- `∈-++ᶜʳ-assoc`.

env-Vˢ-var-r : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx) → (x : A ∈[ ρ ] Δ)
             → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → env-Vˢ γ Δ (var f (∈-++ᶜʳ {Γ = Γ} x))
             ≡ var f' (∈-++ᶜʳ {Γ = toCtx St} x)

env-Vˢ-var-r ⌊ St ⌋ Δ x f f' = var-≡
env-Vˢ-var-r (reachᵉ γ q) Δ x f f' =
  trans (V-rename-cong (cong-ren (reach-renᵘ q)) (env-Vˢ-var-r γ Δ x f f))
           (ren-var-r (reach-renᵘ q) x f f')

env-Vˢ-var-r (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ x f f' =
  trans (V-rename-cong (cong-ren (unbox-ren q)) step)
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
         ≡ var f (∈-++ᶜʳ {Γ = toCtx St ⟨ ρ ⟩} x)
    step =
      trans ((cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) inner))
        (trans (castᵛ-≡ eo (env-Vˢ-var-r γ Δ' y f f)) (outer))

env-Vˢ-var-r (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ x f f' =
  trans ((cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) inner))
    (trans (castᵛ-≡ eo (env-Vˢ-var-r γ Δ' y f f))
      (trans (outer) var-≡))
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
  trans ((cong (λ z → sub-atᵛ Δ (castᵛ eIn (env-Vˢ γ Δ'' z)) W) inner))
    (trans
      (sub-atᵛ-≡ Δ W
        (trans (castᵛ-≡ eIn (env-Vˢ-var-r γ Δ'' y f f)) (outer)))
      (sub-var-r Δ x W f f'))
  where
    Δ'' = [] ∷ A₀ ++ᶜ Δ
    eIn = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA  = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
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

------------------------------------------------------------------------
-- THE ACTION ON A VARIABLE
--
-- What each zone does to a variable of its own context. The bounds are left
-- free: `_≡_` does not see them, and each caller has its own.
------------------------------------------------------------------------

-- A telescope entry is substituted by its value: at the empty suffix the
-- action is `env-Vˢ γ ([] ∷ A)` followed by substituting `Hd`, and the entry's
-- own variable is a suffix variable.

env-var-hd : ∀ {St Γ A} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A)
           → (f : ¬ Eternal A → uᵣ ≾ᵣ uᵣ)
           → env-V (γ ∷ᵉ W) (var f Hd) ≡ W
env-var-hd γ W f =
  sub-≡ᵛ split-[] (refl) (env-Vˢ-var-r γ ([] ∷ _) Hd f f)

-- Any other variable is untouched by the entry, and is the action of the rest.
--
-- Both are the same lemma at a one-entry suffix: the action under a suffix `Δ`
-- of a variable of the *prefix* is the action at the empty suffix, pushed under
-- `Δ` by `push-ren`. The suffix must be arbitrary, because `env-Vˢ` grows it at
-- `_⟨_⟩ᵉ` and `_∷ᵉ_`; `push-ren` is pinned up to `_≐ʳ_` by `push-ren-img`, which
-- is why no renaming needs to be quantified over.
--
-- The two zones that grow the suffix use the induction hypothesis **twice** —
-- at `[] ∷ A ++ᶜ Δ` (resp. `[] ⟨ ρ ⟩ ++ᶜ Δ`) for the goal's left side and at
-- `[] ∷ A` (resp. `[] ⟨ ρ ⟩`) for its right, whose own action is at suffix `[]`.
-- Both land on the same `env-Vˢ γ [] (var _ x)`, leaving an equation between two
-- composite renamings, which `push-ren-++ᶜ` and `push-ren-nat` settle.
--
-- `¬ Eternal A` is what makes the lock case go through: it supplies the lock's
-- own bound by `≾ᵣ-zero-product*`, where at an eternal type `f` is vacuous.

env-Vˢ-var-l : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → ¬ Eternal A
             → (p : ctx-grade Δ ≾ᵣ uᵣ)
             → (x : A ∈[ ρ ] Γ)
             → (f  : ¬ Eternal A → grade-++ᶜˡ ρ Δ ≾ᵣ uᵣ)
             → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → env-Vˢ γ Δ (var f (∈-++ᶜˡ Δ x))
             ≡ V-rename (push-ren Δ p) (env-Vˢ γ [] (var f' x))

env-Vˢ-var-l ⌊ St ⌋ Δ ¬et p x f f' =
  sym (var-ren-img-≡ (push-ren Δ p) x f' (push-ren-img Δ p x) f)

env-Vˢ-var-l (reachᵉ γ q) Δ ¬et p x f f' =
  trans
    (V-rename-cong (cong-ren {Γ'' = Δ} (reach-renᵘ q))
                   (env-Vˢ-var-l γ Δ ¬et p x f f'))
    (trans
      (sym (V-rename-∘ (push-ren Δ p) (cong-ren {Γ'' = Δ} (reach-renᵘ q)) _))
      (trans (V-rename-≡ (push-ren-nat (reach-renᵘ q) Δ p) _)
                (V-rename-∘ (reach-renᵘ q) (push-ren Δ p) _)))

env-Vˢ-var-l (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₁} γ q) Δ ¬et p (Tl-⟨⟩ x) f f' =
  trans
    (V-rename-cong (cong-ren {Γ'' = Δ} (unbox-ren q))
      (trans (castᵛ-≡ eo (env-Vˢ-≡ γ (Δ₁ ++ᶜ Δ) inner))
        (trans (castᵛ-≡ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) ¬et p₁ x f₁ f''))
          (trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
            (trans (V-rename-≡ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
                      (V-rename-∘ (push-ren Δ₁ pₗ) (push-ren Δ p) _))))))
    (trans
      (sym (V-rename-∘ (push-ren Δ p) (cong-ren {Γ'' = Δ} (unbox-ren q)) _))
      (trans (V-rename-≡ (push-ren-nat (unbox-ren q) Δ p) _)
        (trans (V-rename-∘ (unbox-ren q) (push-ren Δ p) _)
          (V-rename-cong (push-ren Δ p)
            (V-rename-cong (unbox-ren q)
              (sym (env-Vˢ-var-l γ Δ₁ ¬et pₗ x f' f'')))))))
  where
    Δ₁ = [] ⟨ ρ₁ ⟩
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

    pρ = ≾ᵣ-zero-productʳ (grade-++ᶜˡ-zeroˡ Δ (f ¬et))
    pₗ = ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ₁)) pρ
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁  = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)
    f'' = λ z → ≾ᵣ-zero-productˡ (grade-++ᶜˡ-zeroˡ Δ (f z))

    inner = castᵛ-var-Var ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Var-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The cell zone: nothing is substituted, so both sides re-bracket and the
-- comparison is `push-ren-++ᶜ` alone.

env-Vˢ-var-l (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₁} V γ) Δ ¬et p (Tl-∷ x) f f' =
  trans (castᵛ-≡ eo (env-Vˢ-≡ γ (Δ₁ ++ᶜ Δ) inner))
    (trans (castᵛ-≡ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) ¬et p₁ x f₁ f'))
      (trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
        (trans (V-rename-≡ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
          (trans (V-rename-∘ (push-ren Δ₁ pₗ) (push-ren Δ p) _)
            (V-rename-cong (push-ren Δ p)
              (sym (env-Vˢ-var-l γ Δ₁ ¬et pₗ x f' f')))))))
  where
    Δ₁ = [] ∷ [ ρ₁ ] A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

    pₗ = ≾ᵣ-refl
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁ = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)

    inner = castᵛ-var-Var ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Var-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The cell's own variable: a *suffix* variable of the inner action, carried
-- through unchanged since nothing is substituted.

env-Vˢ-var-l (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₁} V γ) Δ ¬et p Hd f f' =
  trans (castᵛ-≡ eo (env-Vˢ-≡ γ (Δ₁ ++ᶜ Δ) inner))
    (trans (castᵛ-≡ eo (env-Vˢ-var-r γ (Δ₁ ++ᶜ Δ) hd f f))
      (trans outer
        (sym
          (trans
            (V-rename-cong (push-ren Δ p)
              (env-Vˢ-var-r γ Δ₁ (Hd {Γ = []}) f' f'))
            (var-ren-img-≡ (push-ren Δ p) (Hd {Γ = toCtx St}) f'
                           (push-ren-img Δ p Hd) f)))))
  where
    Δ₁ = [] ∷ [ ρ₁ ] A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    hd = ∈-++ᶜˡ {Γ = Δ₁} Δ (Hd {Γ = []})

    inner = castᵛ-var-Var ei (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Γ} (Hd {Γ = []})))
              (∈-++ᶜʳ {Γ = Γ} hd) (∈-++ᶜˡ-++ᶜʳ Γ Δ₁ Δ (Hd {Γ = []})) f f

    outer = castᵛ-var-Var eo (∈-++ᶜʳ {Γ = toCtx St} hd)
              (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
              (Var-cast-flip (++ᶜ-assoc (toCtx St) Δ₁ Δ) _ _
                             (∈-++ᶜˡ-++ᶜʳ (toCtx St) Δ₁ Δ (Hd {Γ = []})))
              f f

env-Vˢ-var-l (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ ¬et p (Tl-∷ x) f f' =
  trans
    (sub-atᵛ-≡ Δ W
      (trans (castᵛ-≡ eo (env-Vˢ-≡ γ (Δ₁ ++ᶜ Δ) inner))
        (trans (castᵛ-≡ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) ¬et p₁ x f₁ f'))
          (trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
            (trans (V-rename-≡ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
              (trans
                (V-rename-≡
                  (≐ʳ-trans (∘ʳ-≐ʳ (push-ren-∷ pₗ) ≐ʳ-refl)
                            (≐ʳ-sym (push-ren-nat wk-ren Δ p))) _)
                (V-rename-∘ (push-ren Δ p) (cong-ren {Γ'' = Δ} wk-ren) _)))))))
    (trans (sub-wk-V Δ (V-rename (push-ren Δ p) Z) W)
      (V-rename-cong (push-ren Δ p)
        (sym
          (trans
            (sub-atᵛ-≡ [] W
              (trans (env-Vˢ-var-l γ Δ₁ ¬et pₗ x f' f')
                        (V-rename-≡ (push-ren-∷ pₗ) _)))
            (sub-wk-V [] Z W)))))
  where
    Δ₁ = [] ∷ A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    Z  = env-Vˢ γ [] (var f' x)

    pₗ = ≾ᵣ-refl
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁ = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)

    inner = castᵛ-var-Var ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Var-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The entry's own variable: a *suffix* variable of the inner action, which the
-- substitution then hits (`sub-var-hit′`), returning the entry's value pushed
-- under `Δ`. At the empty suffix that is `env-var-hd`.

env-Vˢ-var-l (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ ¬et p Hd f f' =
  trans
    (sub-atᵛ-≡ Δ W
      (trans (castᵛ-≡ eo (env-Vˢ-≡ γ (Δ₁ ++ᶜ Δ) inner))
        (trans (castᵛ-≡ eo (env-Vˢ-var-r γ (Δ₁ ++ᶜ Δ) hd f f))
                  outer)))
    (trans
      (sub-var-hit′ Δ ¬et p (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
                    (sym (split→∈-∈-++ᶜˡ (toCtx St) A₀ Δ)) W f)
      (V-rename-cong (push-ren Δ p) (sym (env-var-hd γ W f'))))
  where
    Δ₁ = [] ∷ A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    hd = ∈-++ᶜˡ {Γ = Δ₁} Δ (Hd {Γ = []})

    inner = castᵛ-var-Var ei (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Γ} (Hd {Γ = []})))
              (∈-++ᶜʳ {Γ = Γ} hd) (∈-++ᶜˡ-++ᶜʳ Γ Δ₁ Δ (Hd {Γ = []})) f f

    outer = castᵛ-var-Var eo (∈-++ᶜʳ {Γ = toCtx St} hd)
              (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
              (Var-cast-flip (++ᶜ-assoc (toCtx St) Δ₁ Δ) _ _
                             (∈-++ᶜˡ-++ᶜʳ (toCtx St) Δ₁ Δ (Hd {Γ = []})))
              f f

-- The two one-entry instances. `env-var-tl` substitutes `Hd` into a weakening,
-- which cancels (`sub-wk-V []`); `env-var-lock` composes the lock crossing with
-- the reach, which `unbox-ren-unit` recognises as the unit reach's renaming.

env-var-tl : ∀ {St Γ A A₀ ρ} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A₀)
           → ¬ Eternal A
           → (x : A ∈[ ρ ] Γ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → env-V (γ ∷ᵉ W) (var f (Tl-∷ x)) ≡ env-V γ (var f' x)

env-var-tl γ W ¬et x f f' =
  trans
    (sub-atᵛ-≡ [] W
      (trans (env-Vˢ-var-l γ ([] ∷ _) ¬et ≾ᵣ-refl x f f')
                (V-rename-≡ (push-ren-∷ ≾ᵣ-refl) _)))
    (sub-wk-V [] (env-Vˢ γ [] (var f' x)) W)

env-var-lock : ∀ {St St' Γ A ρ ρ'} → (γ : Env St Γ) → (q : St ⊑ₛ[ ρ ] St')
             → ¬ Eternal A
             → (p : ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ' ] Γ)
             → (f  : ¬ Eternal A → ρ' ·ᵣ ρ ≾ᵣ uᵣ)
             → (f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
             → env-V (γ ⟨ q ⟩ᵉ) (var f (Tl-⟨⟩ x))
             ≡ reach-val (reach-≤ q p) (env-V γ (var f' x))

-- The cell zone's own instance: `Δ := [] ∷ [ ρ ] A₀`, where the push is the
-- weakening past the new cell and there is nothing to cancel — `liftᵉ` keeps the
-- binder rather than substituting for it.

env-var-lift : ∀ {St Γ A A₀ ρ ρ'} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A₀)
             → (γ : Env St Γ) → ¬ Eternal A
             → (x : A ∈[ ρ' ] Γ) → (f f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
             → env-V (liftᵉ V γ) (var f (Tl-∷ x))
             ≡ V-rename wk-ren (env-V γ (var f' x))

env-var-lift {A₀ = A₀} {ρ = ρ} V γ ¬et x f f' =
  trans (env-Vˢ-var-l γ ([] ∷ [ ρ ] A₀) ¬et ≾ᵣ-refl x f f')
           (V-rename-≡ (push-ren-∷ ≾ᵣ-refl) _)

env-var-lock {ρ = ρ} γ q ¬et p x f f' =
  trans
    (V-rename-cong (unbox-ren q)
      (env-Vˢ-var-l γ ([] ⟨ ρ ⟩) ¬et pₗ x f f'))
    (trans (sym (V-rename-∘ (push-ren ([] ⟨ ρ ⟩) pₗ) (unbox-ren q) _))
              (V-rename-≡ (≐ʳ-trans (∘ʳ-≐ʳ (push-ren-⟨⟩ pₗ p) ≐ʳ-refl)
                                    (unbox-ren-unit q p)) _))
  where
    pₗ = ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)) p

-- Every variable of a reducible environment's context becomes a reducible
-- value: the fundamental lemma's variable case. The eternal cases are the two
-- that need no law — `VRed` holds of everything at an eternal type, which is
-- also why a locked variable of eternal type needs no reach.

env-var : ∀ {St Γ A ρ} → (γ : Env St Γ) → Rel-Env γ
        → (x : A ∈[ ρ ] Γ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        ------------------------------------------------
        → VRed A St (env-V γ (var f x))

env-var ⌊ St ⌋       pγ x f = SRed-var pγ x f

env-var (reachᵉ γ q) pγ x f = VRed-reach q _ (env-var γ pγ x f)

env-var (γ ∷ᵉ W) (pγ , pW) Hd       f =
  VRed-≡ᵛ _ (sym (env-var-hd γ W f)) pW
env-var {A = A} (γ ∷ᵉ W) (pγ , pW) (Tl-∷ x) f with eternal? A
... | yes et = VRed-eternal et _
... | no ¬et =
  VRed-≡ᵛ _ (sym (env-var-tl γ W ¬et x f f))
            (env-var γ pγ x f)

env-var (liftᵉ V γ) (pγ , pV) Hd f =
  VRed-≡ᵛ _ (sym (env-Vˢ-var-r γ ([] ∷ _) Hd f f)) (SRed-fresh V pV f)
env-var {A = A} (liftᵉ V γ) (pγ , pV) (Tl-∷ x) f with eternal? A
... | yes et = VRed-eternal et _
... | no ¬et =
  VRed-≡ᵛ _ (sym (env-var-lift V γ ¬et x f f))
    (VRed-≡ᵛ _ (V-rename-≡ (alloc-ren-≐ʳ V) _)
      (VRed-reach (alloc-reach V) _ (env-var γ pγ x f)))

env-var {A = A} (γ ⟨ q ⟩ᵉ) pγ (Tl-⟨⟩ x) f with eternal? A
... | yes et = VRed-eternal et _
... | no ¬et =
  VRed-≡ᵛ _ (sym (env-var-lock γ q ¬et p x f f'))
            (VRed-reach (reach-≤ q p) _ (env-var γ pγ x f'))
  where
    p  = ≾ᵣ-zero-productʳ (f ¬et)
    f' = λ _ → ≾ᵣ-zero-productˡ (f ¬et)

