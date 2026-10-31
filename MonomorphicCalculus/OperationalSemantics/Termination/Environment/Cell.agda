------------------------------------------------------------------------
-- The action on the cell an `unbox` names.
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

module MonomorphicCalculus.OperationalSemantics.Termination.Environment.Cell (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.OperationalSemantics.Termination.Reducibility Spec
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Base       Spec
open import MonomorphicCalculus.Syntax.Substitution.Lookup     Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.Syntax.Substitution.At         Spec
open import MonomorphicCalculus.Syntax.Substitution.Clauses    Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Core Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Action Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Environment.Variables Spec

-- A cell past a context equality.

RVar-cast : ∀ {Γ Γ'} → Γ ≡ Γ' → RVar Γ → RVar Γ'
RVar-cast e (ρ , A , t) = ρ , A , Var-cast e t

-- What the action does to an `unbox`: the cell `env-cell` computes, at the
-- declared box type the named one only bounds. The grade bound and the
-- payload subsumption travel separately, as `env-cell-rel` and `env-cell-typ`.

env-cell : ∀ {𝕊 Γ A ρ} → (γ : Env 𝕊 Γ) → (Δ : Ctx)
         → Var (Γ ++ᶜ Δ) ([ ρ ] A) → RVar (toCtx 𝕊 ++ᶜ Δ)

env-cell {A = A} {ρ = ρ} ⌊ 𝕊 ⌋ Δ t = ρ , A , t
env-cell (reachᵉ γ q) Δ t =
  rvar-img′ (cong-ren (reach-renᵘ q)) (env-cell γ Δ t)

env-cell (_⟨_⟩ᵉ {𝕊 = 𝕊} {Γ = Γ} {ρ = ρ₀} γ q) Δ t =
  rvar-img′ (cong-ren (unbox-ren q))
    (RVar-cast (sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ρ₀ ⟩) Δ))
      (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
        (Var-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell (liftᵉ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t =
  RVar-cast (sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ [ ρ₀ ] A₀) Δ))
    (env-cell γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
      (Var-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t))

env-cell (_∷ᵉ_ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} γ W) Δ t = atᴿ Δ z W
  where
    z = rvar-pos (RVar-cast (sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₀) Δ))
                   (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                     (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

-- The readability bound travels with the cell: renaming only lowers a
-- variable's grade, and `⟨_⟩[_↦_]rvar` carries its bound along, composing the
-- contravariance of box subtyping into it, so a cell readable at `ρ` stays
-- readable at the grade it is declared at wherever the action puts it.

var-img-≾ : ∀ {Γ Γ' A ρ σ} → (r : Ren [] Γ' Γ)
          → (x : [ ρ ] A ∈[ σ ] Γ) → proj₁ (var-img r x) ≾ᵣ σ
var-img-≾ r x = proj₁ (proj₂ (var-rename r x)) (λ ())

env-cell-rel : ∀ {𝕊 Γ A ρ} → (γ : Env 𝕊 Γ) → (Δ : Ctx)
             → (t : Var (Γ ++ᶜ Δ) ([ ρ ] A))
             → proj₁ t ≾ᵣ ρ
             → rvar-elapsed (env-cell γ Δ t) ≾ᵣ rvar-grade (env-cell γ Δ t)

env-cell-rel ⌊ 𝕊 ⌋        Δ t rel = rel
env-cell-rel (reachᵉ γ q) Δ t rel =
  ≾ᵣ-trans (var-img-≾ (cong-ren (reach-renᵘ q)) (rvar-pos (env-cell γ Δ t)))
           (env-cell-rel γ Δ t rel)

env-cell-rel (_⟨_⟩ᵉ {𝕊 = 𝕊} {Γ = Γ} {ρ = ρ₀} γ q) Δ t rel =
  ≾ᵣ-trans (var-img-≾ (cong-ren (unbox-ren q)) z)
           (env-cell-rel γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                         (Var-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t) rel)
  where
    z = rvar-pos (RVar-cast (sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ρ₀ ⟩) Δ))
                   (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                     (Var-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell-rel (liftᵉ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t rel =
  env-cell-rel γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
               (Var-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t) rel

env-cell-rel (_∷ᵉ_ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} γ W) Δ t rel =
  ≾ᵣ-trans
    (≾ᵣ-trans
      (tgt-≾₀ (sub-atˢ₀ Δ W) z)
      (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ)
                    (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t) rel))
    (tgt-grade-≾₀ (sub-atˢ₀ Δ W) z)
  where
    z = rvar-pos (RVar-cast (sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₀) Δ))
                   (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                     (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

-- The payload subsumption, composed the same way.

env-cell-typ : ∀ {𝕊 Γ A ρ} → (γ : Env 𝕊 Γ) → (Δ : Ctx)
             → (t : Var (Γ ++ᶜ Δ) ([ ρ ] A))
             → rvar-type (env-cell γ Δ t) <:ᵛ A

env-cell-typ {A = A} ⌊ 𝕊 ⌋ Δ t = <:ᵛ-refl A
env-cell-typ (reachᵉ γ q) Δ t = env-cell-typ γ Δ t

env-cell-typ (_⟨_⟩ᵉ {Γ = Γ} {ρ = ρ₀} γ q) Δ t =
  env-cell-typ γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ) (Var-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)

env-cell-typ (liftᵉ {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t =
  env-cell-typ γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
               (Var-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t)

env-cell-typ (_∷ᵉ_ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} γ W) Δ t =
  <:ᵛ-trans
    (tgt-type-<:₀ (sub-atˢ₀ Δ W) z)
    (env-cell-typ γ ([] ∷ A₀ ++ᶜ Δ) (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t))
  where
    z = rvar-pos (RVar-cast (sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₀) Δ))
                   (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                     (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

-- and the same on computations

env-Cˢ-≡ : ∀ {𝕊 Γ C} → (γ : Env 𝕊 Γ) → (Δ : Ctx) → {M M' : (Γ ++ᶜ Δ) ⊢ᶜ⦂ C}
         → M ≡ M' → env-Cˢ γ Δ M ≡ env-Cˢ γ Δ M'
env-Cˢ-≡ γ Δ = cong (env-Cˢ γ Δ)

-- The action sends an `unbox` to an `unbox` at the cell `env-cell` computes;
-- the grade bound and the payload subsumption are irrelevant, so the statement
-- takes the target's pair as parameters.

env-Cˢ-unbox : ∀ {𝕊 Γ A A₀ C ρ₀ σ} → (γ : Env 𝕊 Γ) → (Δ : Ctx)
             → (x : [ ρ₀ ] A₀ ∈[ σ ] (Γ ++ᶜ Δ)) → (rel : σ ≾ᵣ ρ₀)
             → (p : A₀ <:ᵛ A)
             → (M : ((Γ ++ᶜ Δ) ∷ A) ⊢ᶜ⦂ C)
             → (rel' : rvar-elapsed (env-cell γ Δ (σ , x))
                         ≾ᵣ rvar-grade (env-cell γ Δ (σ , x)))
             → (p' : rvar-type (env-cell γ Δ (σ , x)) <:ᵛ A)
             → env-Cˢ γ Δ (unbox x rel p M)
             ≡ unbox (rvar-pos (env-cell γ Δ (σ , x))) rel' p'
                     (env-Cˢ γ (Δ ∷ A) M)

env-Cˢ-unbox ⌊ 𝕊 ⌋   Δ x rel p M rel' p' = unbox-≡ refl (refl)

env-Cˢ-unbox (reachᵉ γ q) Δ x rel p M rel' p' =
  trans
    (C-rename-cong (cong-ren (reach-renᵘ q))
      (env-Cˢ-unbox γ Δ x rel p M (env-cell-rel γ Δ _ rel)
                    (<:ᵛ-trans (env-cell-typ γ Δ _) p)))
    (unbox-≡ refl (refl))

env-Cˢ-unbox {A = A} (_⟨_⟩ᵉ {𝕊 = 𝕊} {Γ = Γ} {ρ = ρ₀} γ q) Δ x rel p M rel' p' =
  trans
    (C-rename-cong (cong-ren (unbox-ren q))
      (castᶜ-≡ eOut
        (trans
          (env-Cˢ-≡ γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
            ((cast-unbox (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ))))
          (env-Cˢ-unbox γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ) _ _ _ _
            (env-cell-rel γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ) _ rel)
            (<:ᵛ-trans (env-cell-typ γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ) _) p)))))
    (trans
      ((cong (C-rename (cong-ren (unbox-ren q))) (cast-unbox eOut)))
      (unbox-≡ refl
        (C-rename-cong (cong-ren (unbox-ren q))
          ((castᶜ-irr (cong (_∷ A) eOut)
                   (sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ρ₀ ⟩) (Δ ∷ A))) _)))))
  where
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ρ₀ ⟩) Δ)

env-Cˢ-unbox {A = A} (liftᵉ {𝕊 = 𝕊} {Γ = Γ} {A = A₁} {ρ = ρ₁} V₀ γ)
             Δ x rel p M rel' p' =
  trans
    (castᶜ-≡ eOut
      (trans
        (env-Cˢ-≡ γ ([] ∷ [ ρ₁ ] A₁ ++ᶜ Δ)
          ((cast-unbox (++ᶜ-assoc Γ ([] ∷ [ ρ₁ ] A₁) Δ))))
        (env-Cˢ-unbox γ ([] ∷ [ ρ₁ ] A₁ ++ᶜ Δ) _ _ _ _
          (env-cell-rel γ ([] ∷ [ ρ₁ ] A₁ ++ᶜ Δ) _ rel)
          (<:ᵛ-trans (env-cell-typ γ ([] ∷ [ ρ₁ ] A₁ ++ᶜ Δ) _) p))))
    (trans ((cast-unbox eOut))
      (unbox-≡ refl
        ((castᶜ-irr (cong (_∷ A) eOut)
                 (sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ [ ρ₁ ] A₁) (Δ ∷ A))) _))))
  where
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ [ ρ₁ ] A₁) Δ)

env-Cˢ-unbox {A = A} (_∷ᵉ_ {𝕊 = 𝕊} {Γ = Γ} {A = A₁} γ W) Δ x rel p M rel' p' =
  trans
    (sub-atᶜ-≡ Δ W
      (trans
        (castᶜ-≡ eOut
          (trans
            (env-Cˢ-≡ γ ([] ∷ A₁ ++ᶜ Δ)
              ((cast-unbox (++ᶜ-assoc Γ ([] ∷ A₁) Δ))))
            (env-Cˢ-unbox γ ([] ∷ A₁ ++ᶜ Δ) _ _ _ _
              (env-cell-rel γ ([] ∷ A₁ ++ᶜ Δ) _ rel)
              (<:ᵛ-trans (env-cell-typ γ ([] ∷ A₁ ++ᶜ Δ) _) p))))
        ((cast-unbox eOut))))
    (unbox-≡ refl
      (sub-atᶜ-≡ (Δ ∷ A) W
        ((castᶜ-irr (cong (_∷ A) eOut)
                 (sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₁) (Δ ∷ A)))
                 _))))
  where
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₁) Δ)

-- The same action as `env-cell`, read directly off the environment's zones,
-- with the recursion staying at the boundary: every case is a cell of
-- `toCtx 𝕊`.

env-cell₀ : ∀ {𝕊 Γ A ρ} → (γ : Env 𝕊 Γ)
          → Var Γ ([ ρ ] A) → RVar (toCtx 𝕊)

env-cell₀ {A = A} {ρ = ρ} ⌊ 𝕊 ⌋ t = ρ , A , t
env-cell₀ (reachᵉ γ q) t        = rvar-img′ (reach-renᵘ q) (env-cell₀ γ t)

env-cell₀ (_⟨_⟩ᵉ {ρ = ρ₀} γ q) (σ , Tl-⟨⟩ y) =
  rvar-img′ (unbox-ren q) (RVar-⟨⟩ ρ₀ (env-cell₀ γ (_ , y)))

env-cell₀ (γ ∷ᵉ W) (σ , Hd)     = val-cell W
env-cell₀ (γ ∷ᵉ W) (σ , Tl-∷ y) = env-cell₀ γ (σ , y)

env-cell₀ {A = A} {ρ = ρ} (liftᵉ V γ) (σ , Hd) = ρ , A , 𝟏ᵣ , Hd
env-cell₀ (liftᵉ V γ) (σ , Tl-∷ y)             = RVar-∷ (env-cell₀ γ (σ , y))

-- Reading a cell a zone has moved: the same read, at the cell the inner
-- environment names, and the same value: the two positions agree once the
-- extension is embedded.

push-read : ∀ {A ρ σ σ'} {𝕊 𝕊' 𝕊₂ : State []}
          → {x : [ ρ ] A ∈[ σ ] toCtx 𝕊} → {x' : [ ρ ] A ∈[ σ' ] toCtx 𝕊'}
          → (E : 𝕊 ≤ₛ 𝕊')
          → (r : 𝕊' [ x' ]⊑ᶜ 𝕊₂)
          → ≤ₛ-embed (≤ₛ-trans E (extᶜ r)) x ≡ ≤ₛ-embed (extᶜ r) x'
          -----------------------------------------------------------
          → Σ[ r₀ ∈ 𝕊 [ x ]⊑ᶜ 𝕊₂ ] (lookupᶜ r₀ ≡ lookupᶜ r)

push-read E (read e rel) eq =
    read (≤ₛ-trans E e) (subst (_≾ᵣ _) (sym (cong proj₁ eq)) rel)
  , lookup-body-≡ _ eq _ rel

reach-read : ∀ {𝕊 𝕊' 𝕊₂ : State []} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
           → (c : RVar (toCtx 𝕊))
           → (r : 𝕊' [ rvar-pos (rvar-img′ (reach-renᵘ q) c) ]⊑ᶜ 𝕊₂)
           → Σ[ r₀ ∈ 𝕊 [ rvar-pos c ]⊑ᶜ 𝕊₂ ] (lookupᶜ r₀ ≡ lookupᶜ r)

reach-read q c r =
  push-read (ext q) r
    (trans (≤ₛ-embed-∘ (ext q) (extᶜ r) (rvar-pos c))
           (sym (cong (λ z → ≤ₛ-embed (extᶜ r) (proj₂ z))
                      (reach-renᵘ-img q (rvar-pos c)))))

unbox-read : ∀ {𝕊 𝕊' 𝕊₂ : State []} {ρ} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
           → (c : RVar (toCtx 𝕊))
           → (r : 𝕊' [ rvar-pos (rvar-img′ (unbox-ren q) (RVar-⟨⟩ ρ c)) ]⊑ᶜ 𝕊₂)
           → Σ[ r₀ ∈ 𝕊 [ rvar-pos c ]⊑ᶜ 𝕊₂ ] (lookupᶜ r₀ ≡ lookupᶜ r)

unbox-read q c r =
  push-read (ext q) r
    (trans (≤ₛ-embed-∘ (ext q) (extᶜ r) (rvar-pos c))
           (sym (cong (λ z → ≤ₛ-embed (extᶜ r) (proj₂ z))
                      (unbox-ren-img q (rvar-pos c)))))

alloc-read : ∀ {A ρ} {𝕊 𝕊₂ : State []}
           → (V : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢ᵛ⦂ A) → (c : RVar (toCtx 𝕊))
           → (r : (𝕊 ∷ₛ V) [ rvar-pos (RVar-∷ c) ]⊑ᶜ 𝕊₂)
           → Σ[ r₀ ∈ 𝕊 [ rvar-pos c ]⊑ᶜ 𝕊₂ ] (lookupᶜ r₀ ≡ lookupᶜ r)

alloc-read V c r =
  push-read (≤ₛ-res ≤ₛ-refl) r
    (≤ₛ-embed-∘ (≤ₛ-res ≤ₛ-refl) (extᶜ r) (rvar-pos c))

-- The raw store read is reducible at the cell's declared payload type. At
-- `_∷ᵉ_`'s own entry that is `Rel-Env`'s component unfolded, the entry being a
-- value of box type and `VRed` speaking of its cell.

env-cell₀-val : ∀ {𝕊 Γ A ρ} → (γ : Env 𝕊 Γ) → Rel-Env γ
              → (t : Var Γ ([ ρ ] A))
              → ∀ {𝕊'} → (r : 𝕊 [ rvar-pos (env-cell₀ γ t) ]⊑ᶜ 𝕊')
              --------------------------------------------------------
              → VRed (rvar-type (env-cell₀ γ t)) 𝕊' (lookupᶜ r)

env-cell₀-val ⌊ 𝕊 ⌋    pγ t r = pγ (proj₂ t) r

env-cell₀-val (reachᵉ γ q) pγ t r =
  VRed-≡ᵛ _ (proj₂ rd) (env-cell₀-val γ pγ t (proj₁ rd))
  where rd = reach-read q (env-cell₀ γ t) r

env-cell₀-val (γ ⟨ q ⟩ᵉ) pγ (σ , Tl-⟨⟩ y) r =
  VRed-≡ᵛ _ (proj₂ rd) (env-cell₀-val γ pγ (_ , y) (proj₁ rd))
  where rd = unbox-read q (env-cell₀ γ (_ , y)) r

env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Hd)     r = VRedˢ-≡ˢ (pW r)
env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Tl-∷ y) r =
  env-cell₀-val γ pγ (σ , y) r

env-cell₀-val (liftᵉ V γ) (pγ , pV) (σ , Hd) r =
  VRedˢ-≡ˢ (SRed-fresh V pV (λ _ → ≾ᵣ-refl) r)

env-cell₀-val (liftᵉ V γ) (pγ , pV) (σ , Tl-∷ y) r =
  VRed-≡ᵛ _ (proj₂ rd) (env-cell₀-val γ pγ (σ , y) (proj₁ rd))
  where rd = alloc-read V (env-cell₀ γ (σ , y)) r

-- `env-cell` and `env-cell₀` agree on the cells pushed in from the
-- environment's own context, all that `fund-unbox` reads.

Var-++ᶜˡ : ∀ {Γ A} → (Δ : Ctx) → Var Γ A → Var (Γ ++ᶜ Δ) A
Var-++ᶜˡ Δ (σ , x) = grade-++ᶜˡ σ Δ , ∈-++ᶜˡ Δ x

RVar-++ᶜˡ : ∀ {Γ} → (Δ : Ctx) → RVar Γ → RVar (Γ ++ᶜ Δ)
RVar-++ᶜˡ Δ (ρ , A , t) = ρ , A , Var-++ᶜˡ Δ t

Var-cast-loop : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Var Γ' A)
              → Var-cast e (Var-cast (sym e) t) ≡ t
Var-cast-loop refl t = refl

-- A cell that comes from the suffix is left where it is: `cong-ren` is the
-- identity on the suffix, and a substituting zone's boundary variable is not a
-- suffix variable, so `⟨_⟩[_↦_]rvar` leaves it alone (`sub-rvar-r`). This is
-- what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` below need, the boundary entry being
-- a suffix cell at the suffix the zone recurses at.

-- Substituting at a resource variable, rather than past it: the counterpart
-- of `sub-rvar-r`, and what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` need. The value
-- put in the variable's place is of box type, hence a variable itself up to
-- subsumption, and the result is that variable pushed back under the suffix.

-- `grad-typ⇒var<:` and `val-cell` locate the same occurrence, by two
-- recursions on the value that agree clause for clause.

val-cell-≡ : ∀ {Γ A ρ} → (W : Γ ⊢ᵛ⦂ [ ρ ] A)
           → tgt-img₀ (val-sub W) Hd ≡ val-cell W

val-cell-≡ (var f x)           = refl
val-cell-≡ (subV V ([ _ ]ₛ _)) = val-cell-≡ V

rvar-hit : ∀ {Γ A ρ} → (Θ : Ctx) → (W : Γ ⊢ᵛ⦂ [ ρ ] A)
         → atᴿ {Γ} Θ (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ})) W
         ≡ RVar-++ᶜˡ Θ (val-cell W)

rvar-hit []        W = val-cell-≡ W
rvar-hit (Θ ∷ C)   W = cong RVar-∷ (rvar-hit Θ W)
rvar-hit (Θ ⟨ ρ' ⟩) W = cong (RVar-⟨⟩ ρ') (rvar-hit Θ W)

∈-++ᶜʳ-assoc⁻ : ∀ {A ρ} → (Γ Γ' : Ctx) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
              → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ))
                      (∈-++ᶜʳ {Γ = Γ} (∈-++ᶜʳ {Γ = Γ'} x))
              ≡ ∈-++ᶜʳ {Γ = Γ ++ᶜ Γ'} x
∈-++ᶜʳ-assoc⁻ Γ Γ' {Δ} x =
  trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ)))
              (sym (∈-++ᶜʳ-assoc Γ Γ' x)))
        (subst-sym-subst′ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))

env-cell-suffix : ∀ {𝕊 Γ A ρ σ} → (γ : Env 𝕊 Γ) → (Δ : Ctx)
                → (z : [ ρ ] A ∈[ σ ] Δ)
                → env-cell γ Δ (σ , ∈-++ᶜʳ {Γ = Γ} z)
                ≡ (ρ , A , σ , ∈-++ᶜʳ {Γ = toCtx 𝕊} z)

env-cell-suffix ⌊ 𝕊 ⌋   Δ z = refl
env-cell-suffix (reachᵉ γ q) Δ z =
  trans (cong (rvar-img′ (cong-ren (reach-renᵘ q))) (env-cell-suffix γ Δ z))
        (rvar-≡ (cong-ren-img-r (reach-renᵘ q) z))

env-cell-suffix {A = A} {ρ = ρ} {σ = σ}
                (_⟨_⟩ᵉ {𝕊 = 𝕊} {Γ = Γ} {ρ = ρ₀} γ q) Δ z =
  trans (cong (λ v → rvar-img′ (cong-ren (unbox-ren q))
                       (RVar-cast eOut (env-cell γ Δ' (_ , v))))
              (∈-++ᶜʳ-assoc Γ ([] ⟨ ρ₀ ⟩) z))
    (trans (cong (λ v → rvar-img′ (cong-ren (unbox-ren q)) (RVar-cast eOut v))
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ⟨ ρ₀ ⟩} z)))
      (trans (cong (λ v → rvar-img′ (cong-ren (unbox-ren q)) (ρ , A , σ , v))
                   (∈-++ᶜʳ-assoc⁻ (toCtx 𝕊) ([] ⟨ ρ₀ ⟩) z))
             (rvar-≡ (cong-ren-img-r (unbox-ren q) z))))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ρ₀ ⟩) Δ)

env-cell-suffix {A = A} {ρ = ρ} {σ = σ}
                (liftᵉ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ z =
  trans (cong (λ v → RVar-cast eOut (env-cell γ Δ' (_ , v)))
              (∈-++ᶜʳ-assoc Γ ([] ∷ [ ρ₀ ] A₀) z))
    (trans (cong (RVar-cast eOut)
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ [ ρ₀ ] A₀} z)))
           (cong (λ v → ρ , A , σ , v)
                 (∈-++ᶜʳ-assoc⁻ (toCtx 𝕊) ([] ∷ [ ρ₀ ] A₀) z)))
  where
    Δ'   = [] ∷ [ ρ₀ ] A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ [ ρ₀ ] A₀) Δ)

env-cell-suffix {A = A} {ρ = ρ} {σ = σ}
                (_∷ᵉ_ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} γ W) Δ z =
  trans (cong (λ v → atᴿ Δ (rvar-pos (RVar-cast eOut (env-cell γ Δ' (_ , v)))) W)
              (∈-++ᶜʳ-assoc Γ ([] ∷ A₀) z))
    (trans (cong (λ v → atᴿ Δ (rvar-pos (RVar-cast eOut v)) W)
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ A₀} z)))
      (trans (cong (λ v → atᴿ Δ v W)
                   (∈-++ᶜʳ-assoc⁻ (toCtx 𝕊) ([] ∷ A₀) z))
             (sub-rvar-r Δ z W)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₀) Δ)

env-cell-push : ∀ {𝕊 Γ A ρ} → (γ : Env 𝕊 Γ) → (Δ : Ctx)
              → (t : Var Γ ([ ρ ] A))
              → env-cell γ Δ (Var-++ᶜˡ Δ t) ≡ RVar-++ᶜˡ Δ (env-cell₀ γ t)

env-cell-push ⌊ 𝕊 ⌋   Δ t       = refl

env-cell-push (reachᵉ γ q) Δ t =
  trans (cong (rvar-img′ (cong-ren (reach-renᵘ q))) (env-cell-push γ Δ t))
        (rvar-≡ (cong-ren-img-l (reach-renᵘ q) Δ (rvar-pos (env-cell₀ γ t))))

-- The two zones that grow the suffix by a binder split on the variable: a
-- `Tl-∷` is the `⟨⟩ᵉ` pattern with `[] ∷ A₀` for `[] ⟨ ρ₀ ⟩`, and a `Hd` is the
-- zone's own boundary variable, which `env-cell-suffix` carries across. The
-- eternal zone has no cell of its own.

env-cell-push (_⟨_⟩ᵉ {𝕊 = 𝕊} {Γ = Γ} {ρ = ρ₀} γ q) Δ (σ , Tl-⟨⟩ y) =
  trans (cong (λ z → rvar-img′ (cong-ren (unbox-ren q))
                       (RVar-cast eOut (env-cell γ Δ' z)))
              step-in)
    (trans (cong (λ z → rvar-img′ (cong-ren (unbox-ren q)) (RVar-cast eOut z))
                 (env-cell-push γ Δ' (_ , y)))
      (trans (cong (rvar-img′ (cong-ren (unbox-ren q)))
                   (rvar-≡ (∈-++ᶜˡ-assoc {Γ = toCtx 𝕊} ([] ⟨ ρ₀ ⟩) Δ
                                         (rvar-pos (env-cell₀ γ (_ , y))))))
             (rvar-≡
               (cong-ren-img-l (unbox-ren q) Δ
                 (rvar-pos (RVar-⟨⟩ ρ₀ (env-cell₀ γ (_ , y))))))))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ⟨ ρ₀ ⟩) Δ)

    -- `Tl-⟨⟩ y` is the push of `y` under `[] ⟨ ρ₀ ⟩`, so the zone's
    -- associativity cast re-brackets the two pushes
    step-in : Var-cast eIn (Var-++ᶜˡ Δ (σ , Tl-⟨⟩ y))
            ≡ Var-++ᶜˡ Δ' (_ , y)
    step-in =
      trans (cong (Var-cast eIn)
                  (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ⟨ ρ₀ ⟩) Δ y)))
            (Var-cast-loop eIn (Var-++ᶜˡ Δ' (_ , y)))

env-cell-push (_∷ᵉ_ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} γ W) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → atᴿ Δ (rvar-pos (RVar-cast eOut (env-cell γ Δ' z))) W)
              step-in)
    (trans (cong (λ z → atᴿ Δ (rvar-pos (RVar-cast eOut z)) W)
                 (env-cell-push γ Δ' (σ , y)))
      (trans (cong (λ z → atᴿ Δ (proj₂ z) W)
                   (∈-++ᶜˡ-assoc {Γ = toCtx 𝕊} ([] ∷ A₀) Δ c))
             (sub-rvar-l Δ c W)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₀) Δ)

    c = rvar-pos (env-cell₀ γ (σ , y))

    step-in : Var-cast eIn (Var-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Var-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Var-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ∷ A₀) Δ y)))
            (Var-cast-loop eIn (Var-++ᶜˡ Δ' (σ , y)))

env-cell-push (_∷ᵉ_ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} γ W) Δ (σ , Hd) =
  trans (cong (λ z → atᴿ Δ (rvar-pos (RVar-cast eOut (env-cell γ Δ' z))) W)
              (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ A₀) Δ Hd))
    (trans (cong (λ z → atᴿ Δ (rvar-pos (RVar-cast eOut z)) W)
                 (env-cell-suffix γ Δ' bnd))
      (trans (cong (λ z → atᴿ Δ (proj₂ z) W)
                   (trans step-out (sym (split→∈-∈-++ᶜˡ (toCtx 𝕊) A₀ Δ))))
             (rvar-hit Δ W)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₀) Δ)

    bnd = ∈-++ᶜˡ {Γ = [] ∷ A₀} Δ Hd

    -- the boundary variable, come across, is `Hd` pushed under the suffix
    step-out : Var-cast eOut (grade-++ᶜˡ 𝟏ᵣ Δ , ∈-++ᶜʳ {Γ = toCtx 𝕊} bnd)
             ≡ Var-++ᶜˡ Δ (𝟏ᵣ , Hd {Γ = toCtx 𝕊})
    step-out =
      Var-cast-flip (++ᶜ-assoc (toCtx 𝕊) ([] ∷ A₀) Δ) _ _
                    (∈-++ᶜˡ-++ᶜʳ (toCtx 𝕊) ([] ∷ A₀) Δ Hd)

env-cell-push (liftᵉ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → RVar-cast eOut (env-cell γ Δ' z)) step-in)
    (trans (cong (RVar-cast eOut) (env-cell-push γ Δ' (σ , y)))
           (rvar-≡ (∈-++ᶜˡ-assoc {Γ = toCtx 𝕊} B₀ Δ
                                 (rvar-pos (env-cell₀ γ (σ , y))))))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ B₀ Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) B₀ Δ)

    step-in : Var-cast eIn (Var-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Var-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Var-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} B₀ Δ y)))
            (Var-cast-loop eIn (Var-++ᶜˡ Δ' (σ , y)))

env-cell-push (liftᵉ {𝕊 = 𝕊} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Hd) =
  trans (cong (λ z → RVar-cast eOut (env-cell γ Δ' z))
              (∈-++ᶜˡ-++ᶜʳ Γ B₀ Δ Hd))
    (trans (cong (RVar-cast eOut) (env-cell-suffix γ Δ' bnd))
           (rvar-≡
             (Var-cast-flip (++ᶜ-assoc (toCtx 𝕊) B₀ Δ) _ _
                            (∈-++ᶜˡ-++ᶜʳ (toCtx 𝕊) B₀ Δ Hd))))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx 𝕊) B₀ Δ)

    bnd = ∈-++ᶜˡ {Γ = B₀} Δ Hd

-- What `fund-unbox` reads: at the unextended state the readability proof is
-- `≤ₛ-refl`, whose embedding is the identity, so the store read is
-- `unbox-lookup`. The cell is taken as a parameter, to be met by
-- `env-cell-push`.

env-cell-val : ∀ {𝕊 Γ A ρ} → (γ : Env 𝕊 Γ) → Rel-Env γ
             → (t : Var Γ ([ ρ ] A))
             → (c : RVar (toCtx 𝕊)) → c ≡ env-cell₀ γ t
             → (rel : rvar-elapsed c ≾ᵣ rvar-grade c)
             ------------------------------------------------------------
             → VRed (rvar-type c) 𝕊 (unbox-lookup 𝕊 (rvar-pos c) rel)

env-cell-val γ pγ t _ refl rel = env-cell₀-val γ pγ t (read ≤ₛ-refl rel)
