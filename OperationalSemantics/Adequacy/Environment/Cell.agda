------------------------------------------------------------------------
-- The action on the cell an `unbox` names.
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

module OperationalSemantics.Adequacy.Environment.Cell (Spec : LanguageSpec) where

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
open import OperationalSemantics.Adequacy.Environment.Variables Spec

-- What the action does to an `unbox`: the cell `env-cell` computes. Only the
-- cell is tracked, not its grade bound, which every consumer recovers from
-- the term.

env-cell : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
         → Var (Γ ++ᶜ Δ) ([ ρ ] A) → Var (toCtx St ++ᶜ Δ) ([ ρ ] A)

env-cell ⌊ St ⌋      Δ t = t
env-cell (reachᵉ γ q) Δ t =
  var-img′ (cong-ren (reach-renᵘ q)) (env-cell γ Δ t)

env-cell (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ t =
  var-img′ (cong-ren (unbox-ren q))
    (Var-cast (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ))
      (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
        (Var-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t =
  Var-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ))
    (env-cell γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
      (Var-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t))

env-cell (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ t =
  proj₁ (sub-atᴿ Δ z W) , proj₁ (proj₂ (sub-atᴿ Δ z W))
  where
    z = proj₂ (Var-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ))
                 (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                   (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

-- The readability bound travels with the cell: renaming only lowers a
-- variable's grade, and `⟨_⟩[_↦_]rvar` carries its bound along, so a cell
-- readable at `ρ` stays readable at `ρ` wherever the action puts it.

var-img-≾ : ∀ {Γ Γ' A ρ σ} → (r : Ren [] Γ' Γ)
          → (x : [ ρ ] A ∈[ σ ] Γ) → proj₁ (var-img r x) ≾ᵣ σ
var-img-≾ r x = proj₁ (proj₂ (var-rename r x)) (λ ())

env-cell-rel : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → (t : Var (Γ ++ᶜ Δ) ([ ρ ] A))
             → proj₁ t ≾ᵣ ρ
             → proj₁ (env-cell γ Δ t) ≾ᵣ ρ

env-cell-rel ⌊ St ⌋       Δ t rel = rel
env-cell-rel (reachᵉ γ q) Δ t rel =
  ≾ᵣ-trans (var-img-≾ (cong-ren (reach-renᵘ q)) (proj₂ (env-cell γ Δ t)))
           (env-cell-rel γ Δ t rel)

env-cell-rel (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ t rel =
  ≾ᵣ-trans (var-img-≾ (cong-ren (unbox-ren q)) z)
           (env-cell-rel γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                         (Var-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t) rel)
  where
    z = proj₂ (Var-cast (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ))
                 (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                   (Var-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell-rel (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t rel =
  env-cell-rel γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
               (Var-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t) rel

env-cell-rel (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ t rel =
  ≾ᵣ-trans
    (proj₂ (proj₂ (sub-atᴿ Δ z W)))
    (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ) (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t) rel)
  where
    z = proj₂ (Var-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ))
                 (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                   (Var-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

-- and the same on computations

env-Cˢ-≡ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx) → {M M' : (Γ ++ᶜ Δ) ⊢C⦂ C}
         → M ≡ M' → env-Cˢ γ Δ M ≡ env-Cˢ γ Δ M'
env-Cˢ-≡ γ Δ = cong (env-Cˢ γ Δ)

-- The action sends an `unbox` to an `unbox` at the cell `env-cell` computes;
-- the grade bound is irrelevant, so the statement takes the target bound as a
-- parameter.

env-Cˢ-unbox : ∀ {St Γ A C ρ σ} → (γ : Env St Γ) → (Δ : Ctx)
             → (x : [ ρ ] A ∈[ σ ] (Γ ++ᶜ Δ)) → (rel : σ ≾ᵣ ρ)
             → (M : ((Γ ++ᶜ Δ) ∷ A) ⊢C⦂ C)
             → (rel' : proj₁ (env-cell γ Δ (σ , x)) ≾ᵣ ρ)
             → env-Cˢ γ Δ (unbox x rel M)
             ≡ unbox (proj₂ (env-cell γ Δ (σ , x))) rel' (env-Cˢ γ (Δ ∷ A) M)

env-Cˢ-unbox ⌊ St ⌋  Δ x rel M rel' = unbox-≡ refl (refl)

env-Cˢ-unbox (reachᵉ γ q) Δ x rel M rel' =
  trans
    (C-rename-cong (cong-ren (reach-renᵘ q))
      (env-Cˢ-unbox γ Δ x rel M (env-cell-rel γ Δ _ rel)))
    (unbox-≡ refl (refl))

env-Cˢ-unbox {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ x rel M rel' =
  trans
    (C-rename-cong (cong-ren (unbox-ren q))
      (castᶜ-≡ eOut
        (trans
          (env-Cˢ-≡ γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
            ((cast-unbox (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ))))
          (env-Cˢ-unbox γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ) _ _ _
            (env-cell-rel γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ) _ rel)))))
    (trans
      ((cong (C-rename (cong-ren (unbox-ren q))) (cast-unbox eOut)))
      (unbox-≡ refl
        (C-rename-cong (cong-ren (unbox-ren q))
          ((castᶜ-irr (cong (_∷ A) eOut)
                   (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) (Δ ∷ A))) _)))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

env-Cˢ-unbox {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V₀ γ) Δ x rel M rel' =
  trans
    (castᶜ-≡ eOut
      (trans
        (env-Cˢ-≡ γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
          ((cast-unbox (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ))))
        (env-Cˢ-unbox γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ) _ _ _
          (env-cell-rel γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ) _ rel))))
    (trans ((cast-unbox eOut))
      (unbox-≡ refl
        ((castᶜ-irr (cong (_∷ A) eOut)
                 (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) (Δ ∷ A))) _))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ)

env-Cˢ-unbox {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ x rel M rel' =
  trans
    (sub-atᶜ-≡ Δ W
      (trans
        (castᶜ-≡ eOut
          (trans
            (env-Cˢ-≡ γ ([] ∷ A₀ ++ᶜ Δ)
              ((cast-unbox (++ᶜ-assoc Γ ([] ∷ A₀) Δ))))
            (env-Cˢ-unbox γ ([] ∷ A₀ ++ᶜ Δ) _ _ _
              (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ) _ rel))))
        ((cast-unbox eOut))))
    (unbox-≡ refl
      (sub-atᶜ-≡ (Δ ∷ A) W
        ((castᶜ-irr (cong (_∷ A) eOut)
                 (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A)))
                 _))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

-- The same action as `env-cell`, read directly off the environment's zones,
-- with the recursion staying at the boundary: every case is a variable of
-- `toCtx St`.

env-cell₀ : ∀ {St Γ A ρ} → (γ : Env St Γ)
          → Var Γ ([ ρ ] A) → Var (toCtx St) ([ ρ ] A)

env-cell₀ ⌊ St ⌋      t         = t
env-cell₀ (reachᵉ γ q) t        = var-img′ (reach-renᵘ q) (env-cell₀ γ t)

env-cell₀ (_⟨_⟩ᵉ {ρ = ρ₀} γ q) (σ , Tl-⟨⟩ y) =
  var-img′ (unbox-ren q) (Var-⟨⟩ ρ₀ (env-cell₀ γ (_ , y)))

env-cell₀ (γ ∷ᵉ W) (σ , Hd)     =
  proj₁ (grad-typ⇒var W) , proj₁ (proj₂ (grad-typ⇒var W))
env-cell₀ (γ ∷ᵉ W) (σ , Tl-∷ y) = env-cell₀ γ (σ , y)

env-cell₀ (liftᵉ V γ) (σ , Hd)     = uᵣ , Hd
env-cell₀ (liftᵉ V γ) (σ , Tl-∷ y) = Var-∷ (env-cell₀ γ (σ , y))

-- `VRed` at the box type, for `env-cell₀ γ t`.

env-cell₀-val : ∀ {St Γ A ρ} → (γ : Env St Γ) → Rel-Env γ
              → (t : Var Γ ([ ρ ] A))
              → ∀ {St'} → (e : St ≤ₛ St')
              → (rel : proj₁ (≤ₛ-embed e (proj₂ (env-cell₀ γ t))) ≾ᵣ ρ)
              --------------------------------------------------------------
              → VRed A St' (lookup-body St' (≤ₛ-embed e (proj₂ (env-cell₀ γ t)))
                                        rel)

env-cell₀-val ⌊ St ⌋   pγ t       e rel = pγ (proj₂ t) (read e rel)

env-cell₀-val {A = A} {ρ = ρ} (reachᵉ γ q) pγ t {St'} e rel =
  VRed-≡ᵛ A ((lookup-body-≡ St' cellEq rel₁ rel))
            (env-cell₀-val γ pγ t (≤ₛ-trans (ext q) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ t)

    cellEq = trans (≤ₛ-embed-∘ (ext q) e c)
                   (sym (cong (λ z → ≤ₛ-embed e (proj₂ z))
                              (reach-renᵘ-img q c)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val {A = A} {ρ = ρ} (_⟨_⟩ᵉ {ρ = ρ₀} γ q) pγ (σ , Tl-⟨⟩ y) {St'} e rel =
  VRed-≡ᵛ A ((lookup-body-≡ St' cellEq rel₁ rel))
            (env-cell₀-val γ pγ (_ , y) (≤ₛ-trans (ext q) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ (_ , y))

    cellEq = trans (≤ₛ-embed-∘ (ext q) e c)
                   (sym (cong (λ z → ≤ₛ-embed e (proj₂ z))
                              (unbox-ren-img q c)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Hd)     e rel = pW (read e rel)
env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Tl-∷ y) e rel =
  env-cell₀-val γ pγ (σ , y) e rel

env-cell₀-val (liftᵉ V γ) (pγ , pV) (σ , Hd) e rel =
  SRed-fresh V pV (λ _ → ≾ᵣ-refl) (read e rel)

env-cell₀-val {A = A} {ρ = ρ} (liftᵉ V γ) (pγ , pV) (σ , Tl-∷ y) {St'} e rel =
  VRed-≡ᵛ A ((lookup-body-≡ St' cellEq rel₁ rel))
            (env-cell₀-val γ pγ (σ , y) (≤ₛ-trans (∷-suc V id-suc) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ (σ , y))

    cellEq = ≤ₛ-embed-∘ (∷-suc V id-suc) e c
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

-- `env-cell` and `env-cell₀` agree on the cells pushed in from the
-- environment's own context — all that `FL-unbox` reads.

Var-++ᶜˡ : ∀ {Γ A} → (Δ : Ctx) → Var Γ A → Var (Γ ++ᶜ Δ) A
Var-++ᶜˡ Δ (σ , x) = grade-++ᶜˡ σ Δ , ∈-++ᶜˡ Δ x

Var-cast-loop : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Var Γ' A)
              → Var-cast e (Var-cast (sym e) t) ≡ t
Var-cast-loop refl t = refl

-- A cell that comes from the *suffix* is left where it is: `cong-ren` is the
-- identity on the suffix, and a substituting zone's boundary variable is not a
-- suffix variable, so `⟨_⟩[_↦_]rvar` leaves it alone (`sub-rvar-r`). This is
-- what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` below need, the boundary entry being
-- a suffix cell at the suffix the zone recurses at.

-- Substituting *at* a resource variable, rather than past it: the counterpart
-- of `sub-rvar-r`, and what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` need. The value
-- put in the variable's place is of box type, hence a variable itself, and the
-- result is that variable pushed back under the suffix.

rvar-hit : ∀ {Γ A ρ} → (Θ : Ctx) → (W : Γ ⊢V⦂ [ ρ ] A)
         → atᴿ {Γ} Θ (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ})) W
         ≡ Var-++ᶜˡ Θ (val-cell W)

rvar-hit []        W = refl
rvar-hit (Θ ∷ C)   W = cong Var-∷ (rvar-hit Θ W)
rvar-hit (Θ ⟨ ρ' ⟩) W = cong (Var-⟨⟩ ρ') (rvar-hit Θ W)

∈-++ᶜʳ-assoc⁻ : ∀ {A ρ} → (Γ Γ' : Ctx) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
              → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ))
                      (∈-++ᶜʳ {Γ = Γ} (∈-++ᶜʳ {Γ = Γ'} x))
              ≡ ∈-++ᶜʳ {Γ = Γ ++ᶜ Γ'} x
∈-++ᶜʳ-assoc⁻ Γ Γ' {Δ} x =
  trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ)))
              (sym (∈-++ᶜʳ-assoc Γ Γ' x)))
        (subst-sym-subst′ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))

env-cell-suffix : ∀ {St Γ A ρ σ} → (γ : Env St Γ) → (Δ : Ctx)
                → (z : [ ρ ] A ∈[ σ ] Δ)
                → env-cell γ Δ (σ , ∈-++ᶜʳ {Γ = Γ} z)
                ≡ (σ , ∈-++ᶜʳ {Γ = toCtx St} z)

env-cell-suffix ⌊ St ⌋  Δ z = refl
env-cell-suffix (reachᵉ γ q) Δ z =
  trans (cong (var-img′ (cong-ren (reach-renᵘ q))) (env-cell-suffix γ Δ z))
        (cong-ren-img-r (reach-renᵘ q) z)

env-cell-suffix (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ z =
  trans (cong (λ v → var-img′ (cong-ren (unbox-ren q))
                       (Var-cast eOut (env-cell γ Δ' (_ , v))))
              (∈-++ᶜʳ-assoc Γ ([] ⟨ ρ₀ ⟩) z))
    (trans (cong (λ v → var-img′ (cong-ren (unbox-ren q)) (Var-cast eOut v))
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ⟨ ρ₀ ⟩} z)))
      (trans (cong (λ v → var-img′ (cong-ren (unbox-ren q)) (_ , v))
                   (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ⟨ ρ₀ ⟩) z))
             (cong-ren-img-r (unbox-ren q) z)))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

env-cell-suffix (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ z =
  trans (cong (λ v → Var-cast eOut (env-cell γ Δ' (_ , v)))
              (∈-++ᶜʳ-assoc Γ ([] ∷ [ ρ₀ ] A₀) z))
    (trans (cong (Var-cast eOut)
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ [ ρ₀ ] A₀} z)))
           (cong (λ v → _ , v) (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ∷ [ ρ₀ ] A₀) z)))
  where
    Δ'   = [] ∷ [ ρ₀ ] A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ)

env-cell-suffix (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ z =
  trans (cong (λ v → atᴿ Δ (proj₂ (Var-cast eOut (env-cell γ Δ' (_ , v)))) W)
              (∈-++ᶜʳ-assoc Γ ([] ∷ A₀) z))
    (trans (cong (λ v → atᴿ Δ (proj₂ (Var-cast eOut v)) W)
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ A₀} z)))
      (trans (cong (λ v → atᴿ Δ v W)
                   (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ∷ A₀) z))
             (sub-rvar-r Δ z W)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

env-cell-push : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
              → (t : Var Γ ([ ρ ] A))
              → env-cell γ Δ (Var-++ᶜˡ Δ t) ≡ Var-++ᶜˡ Δ (env-cell₀ γ t)

env-cell-push ⌊ St ⌋  Δ t       = refl

env-cell-push (reachᵉ γ q) Δ t =
  trans (cong (var-img′ (cong-ren (reach-renᵘ q))) (env-cell-push γ Δ t))
        (cong-ren-img-l (reach-renᵘ q) Δ (proj₂ (env-cell₀ γ t)))

-- The two zones that grow the suffix by a binder split on the variable. A
-- `Tl-∷` is the `⟨⟩ᵉ` pattern with `[] ∷ A₀` for `[] ⟨ ρ₀ ⟩`; a `Hd` is the
-- zone's own boundary variable, which `∈-++ᶜˡ-++ᶜʳ` recognises as a *suffix*
-- variable of the grown suffix, so `env-cell-suffix` carries it across. At
-- `_∷ᵉ_` the substitution then hits it (`split→∈-∈-++ᶜˡ` identifies the pushed
-- boundary variable with the one the splitting names, and `rvar-hit` reads off
-- the substituted value's own cell); at `liftᵉ` nothing substitutes and it
-- stays the fresh cell. The eternal zone has no cell of its own at all.

env-cell-push (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ (σ , Tl-⟨⟩ y) =
  trans (cong (λ z → var-img′ (cong-ren (unbox-ren q))
                       (Var-cast eOut (env-cell γ Δ' z)))
              step-in)
    (trans (cong (λ z → var-img′ (cong-ren (unbox-ren q)) (Var-cast eOut z))
                 (env-cell-push γ Δ' (_ , y)))
      (trans (cong (var-img′ (cong-ren (unbox-ren q)))
                   (∈-++ᶜˡ-assoc {Γ = toCtx St} ([] ⟨ ρ₀ ⟩) Δ
                                 (proj₂ (env-cell₀ γ (_ , y)))))
             (cong-ren-img-l (unbox-ren q) Δ
                             (proj₂ (Var-⟨⟩ ρ₀ (env-cell₀ γ (_ , y)))))))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

    -- `Tl-⟨⟩ y` *is* the push of `y` under `[] ⟨ ρ₀ ⟩`, so the zone's
    -- associativity cast just re-brackets the two pushes
    step-in : Var-cast eIn (Var-++ᶜˡ Δ (σ , Tl-⟨⟩ y))
            ≡ Var-++ᶜˡ Δ' (_ , y)
    step-in =
      trans (cong (Var-cast eIn)
                  (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ⟨ ρ₀ ⟩) Δ y)))
            (Var-cast-loop eIn (Var-++ᶜˡ Δ' (_ , y)))
env-cell-push (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → atᴿ Δ (proj₂ (Var-cast eOut (env-cell γ Δ' z))) W)
              step-in)
    (trans (cong (λ z → atᴿ Δ (proj₂ (Var-cast eOut z)) W)
                 (env-cell-push γ Δ' (σ , y)))
      (trans (cong (λ z → atᴿ Δ (proj₂ z) W)
                   (∈-++ᶜˡ-assoc {Γ = toCtx St} ([] ∷ A₀) Δ c))
             (sub-rvar-l Δ c W)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

    c = proj₂ (env-cell₀ γ (σ , y))

    step-in : Var-cast eIn (Var-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Var-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Var-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ∷ A₀) Δ y)))
            (Var-cast-loop eIn (Var-++ᶜˡ Δ' (σ , y)))

env-cell-push (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ (σ , Hd) =
  trans (cong (λ z → atᴿ Δ (proj₂ (Var-cast eOut (env-cell γ Δ' z))) W)
              (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ A₀) Δ Hd))
    (trans (cong (λ z → atᴿ Δ (proj₂ (Var-cast eOut z)) W)
                 (env-cell-suffix γ Δ' bnd))
      (trans (cong (λ z → atᴿ Δ (proj₂ z) W)
                   (trans step-out (sym (split→∈-∈-++ᶜˡ (toCtx St) A₀ Δ))))
             (rvar-hit Δ W)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

    bnd = ∈-++ᶜˡ {Γ = [] ∷ A₀} Δ Hd

    -- the boundary variable, come across, is `Hd` pushed under the suffix
    step-out : Var-cast eOut (grade-++ᶜˡ uᵣ Δ , ∈-++ᶜʳ {Γ = toCtx St} bnd)
             ≡ Var-++ᶜˡ Δ (uᵣ , Hd {Γ = toCtx St})
    step-out =
      Var-cast-flip (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ) _ _
                    (∈-++ᶜˡ-++ᶜʳ (toCtx St) ([] ∷ A₀) Δ Hd)

env-cell-push (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → Var-cast eOut (env-cell γ Δ' z)) step-in)
    (trans (cong (Var-cast eOut) (env-cell-push γ Δ' (σ , y)))
           (∈-++ᶜˡ-assoc {Γ = toCtx St} B₀ Δ (proj₂ (env-cell₀ γ (σ , y)))))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ B₀ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) B₀ Δ)

    step-in : Var-cast eIn (Var-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Var-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Var-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} B₀ Δ y)))
            (Var-cast-loop eIn (Var-++ᶜˡ Δ' (σ , y)))

env-cell-push (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Hd) =
  trans (cong (λ z → Var-cast eOut (env-cell γ Δ' z))
              (∈-++ᶜˡ-++ᶜʳ Γ B₀ Δ Hd))
    (trans (cong (Var-cast eOut) (env-cell-suffix γ Δ' bnd))
           (Var-cast-flip (++ᶜ-assoc (toCtx St) B₀ Δ) _ _
                          (∈-++ᶜˡ-++ᶜʳ (toCtx St) B₀ Δ Hd)))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) B₀ Δ)

    bnd = ∈-++ᶜˡ {Γ = B₀} Δ Hd
