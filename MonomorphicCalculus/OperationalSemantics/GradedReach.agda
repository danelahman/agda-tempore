------------------------------------------------------------------------
-- Graded reachability: the frame the logical relation is indexed by. --
--                                                                    --
-- Kripke over an accessibility that carries a grade budget: an       --
-- extension together with the bound licensing the lock it crossed,   --
-- rather than over `≤ₛ` alone, since reindexing along `≤ₛ` is not    --
-- free weakening.                                                    --
------------------------------------------------------------------------

open import Data.Product

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.GradedReach (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables Spec

open import MonomorphicCalculus.Syntax.Contexts   Spec
open import MonomorphicCalculus.Syntax.Terms   Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming      Spec
open import MonomorphicCalculus.Syntax.Substitution  Spec
open import MonomorphicCalculus.Syntax.Types Spec

open import MonomorphicCalculus.Syntax.Substitution.Base         Spec
open import MonomorphicCalculus.Syntax.Substitution.Action       Spec
open import MonomorphicCalculus.Syntax.Substitution.Laws         Spec
open import MonomorphicCalculus.Syntax.Substitution.Subsumption  Spec

-- `𝕊 ⊑ₛ[ ρ ] 𝕊'`: `𝕊'` is reachable from `𝕊` on the budget `ρ`, the grade
-- the extension accumulated staying below `ρ`. The `ₛ` marks it as refining the
-- state extension `≤ₛ`.

infix 4 _⊑ₛ[_]_

record _⊑ₛ[_]_ (𝕊 : State []) (ρ : R) (𝕊' : State []) : Set where
  constructor reach
  field
    ext   : 𝕊 ≤ₛ 𝕊'
    bound : κₛ ext ≾ᵣ ρ

open _⊑ₛ[_]_ public

-- The bound in the form `suc-comp-ren` consumes, with the residual spent.

reach-bound : ∀ {𝕊 𝕊' ρ} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
            → κₛ (ext q) ·ᵣ 𝟏ᵣ ≾ᵣ ρ
reach-bound q = ≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ _)) (bound q)

-- The witness an `unbox` needs: enough time has passed for a `ρ`-boxed value
-- to be ready at `𝕊'`. This is the shape of `UNBOX`'s premise, hence what
-- `unbox-lookup` consumes.

unbox-ren : ∀ {𝕊 ρ 𝕊'} → 𝕊 ⊑ₛ[ ρ ] 𝕊' → Ren [] (toCtx 𝕊') (toCtx 𝕊 ⟨ ρ ⟩)
unbox-ren q = suc-comp-ren (ext q) (reach-bound q) ∘ʳ ⟨⟩-η-ren

-- At the unit budget it is a plain renaming `toCtx 𝕊 → toCtx 𝕊'`: `unbox-ren`
-- with the source lock unwound. So each of its laws is the corresponding
-- `unbox-ren` law conjugated by `⟨⟩-η⁻¹-ren`.

reach-renᵘ : ∀ {𝕊 𝕊'} → 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊' → Ren [] (toCtx 𝕊') (toCtx 𝕊)
reach-renᵘ q = ⟨⟩-η⁻¹-ren ∘ʳ suc-comp-ren (ext q) (reach-bound q) ∘ʳ ⟨⟩-η-ren

reach-renᵘ-unbox : ∀ {𝕊 𝕊' : State []} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
                 → reach-renᵘ q ≐ʳ (⟨⟩-η⁻¹-ren ∘ʳ unbox-ren q)
reach-renᵘ-unbox q = ≐ʳ-refl

reach-val : ∀ {𝕊 𝕊' A} → 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊' → toCtx 𝕊 ⊢ᵛ⦂ A → toCtx 𝕊' ⊢ᵛ⦂ A
reach-val q = V-rename (reach-renᵘ q)

-- Transporting a term with one more variable on top (a `fun` body).

reach-under : ∀ {𝕊 𝕊' A C} → 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊'
            → toCtx 𝕊 ∷ A ⊢ᶜ⦂ C → toCtx 𝕊' ∷ A ⊢ᶜ⦂ C
reach-under q = C-rename (cong-∷-ren (reach-renᵘ q))

-- Resuming a continuation guarded by `ρ` at a state where `ρ` has elapsed:
-- cross the lock along the reach, then feed it the arity value. The reach is the
-- one `unbox` consumes, because that is how a resumption is reached: `HANDLE-OP`
-- boxes it at `ρ` and the clause unboxes it once `ρ` has passed.

resume : ∀ {𝕊 𝕊' ρ A ε B}
       → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
       → toCtx 𝕊 ⟨ ρ ⟩ ∷ B ⊢ᶜ⦂ A ! ε
       → toCtx 𝕊' ⊢ᵛ⦂ B
       → toCtx 𝕊' ⊢ᶜ⦂ A ! ε
resume q M W = (C-rename (cong-∷-ren (unbox-ren q)) M) [ split-[] ↦ W ]c

-- Two general facts about `_≤ₛ_` that `MonomorphicCalculus.OperationalSemantics.State` does not
-- carry: extensions compose, and their accumulated grades multiply.

≤ₛ-trans : ∀ {Γ Γ' Γ''} → {𝕊 : State Γ} → {𝕊' : State Γ'} → {𝕊'' : State Γ''}
         → 𝕊 ≤ₛ 𝕊' → 𝕊' ≤ₛ 𝕊''
         -------------------------
         → 𝕊 ≤ₛ 𝕊''

≤ₛ-trans q ≤ₛ-refl      = q
≤ₛ-trans q (≤ₛ-lock q') = ≤ₛ-lock (≤ₛ-trans q q')
≤ₛ-trans q (≤ₛ-res q')  = ≤ₛ-res (≤ₛ-trans q q')

κₛ-trans : ∀ {Γ Γ' Γ''} → {𝕊 : State Γ} → {𝕊' : State Γ'} → {𝕊'' : State Γ''}
         → (q : 𝕊 ≤ₛ 𝕊') → (q' : 𝕊' ≤ₛ 𝕊'')
         ---------------------------------------------------------
         → κₛ (≤ₛ-trans q q') ≃ᵣ κₛ q ·ᵣ κₛ q'

κₛ-trans q ≤ₛ-refl              =
  ≃ᵣ-sym (·ᵣ-identityʳ (κₛ q))
κₛ-trans q (≤ₛ-lock {ρ = ρ} q') =
  ≃ᵣ-trans (·ᵣ-cong (κₛ-trans q q') ≃ᵣ-refl) (·ᵣ-assoc _ _ ρ)
κₛ-trans q (≤ₛ-res q')          =
  κₛ-trans q q'

reach-≤ : ∀ {𝕊 𝕊' ρ ρ₀} → 𝕊 ⊑ₛ[ ρ ] 𝕊' → ρ ≾ᵣ ρ₀ → 𝕊 ⊑ₛ[ ρ₀ ] 𝕊'
reach-≤ (reach e b) p = reach e (≾ᵣ-trans b p)

reach-id : ∀ {𝕊} → 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊
reach-id = reach ≤ₛ-refl ≾ᵣ-refl

reach-∘ᵍ : ∀ {𝕊 𝕊' 𝕊'' ρ ρ'}
         → 𝕊' ⊑ₛ[ ρ' ] 𝕊'' → 𝕊 ⊑ₛ[ ρ ] 𝕊'
         --------------------------------------
         → 𝕊 ⊑ₛ[ ρ ·ᵣ ρ' ] 𝕊''

reach-∘ᵍ (reach e' b') (reach e b) =
  reach (≤ₛ-trans e e')
    (≾ᵣ-trans (≃ᵣ⇒≾ᵣ (κₛ-trans e e'))
              (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ b) (·ᵣ-monoʳ-≾ᵣ b')))

-- The two shapes the development uses: a unit reach appended to a guarded one,
-- and a guarded reach appended to a unit one. Both are the graded law at a
-- product a unit law collapses.

reach-∘ : ∀ {𝕊 𝕊' 𝕊'' ρ} → 𝕊' ⊑ₛ[ 𝟏ᵣ ] 𝕊'' → 𝕊 ⊑ₛ[ ρ ] 𝕊'
        → 𝕊 ⊑ₛ[ ρ ] 𝕊''
reach-∘ {ρ = ρ} q' q = reach-≤ (reach-∘ᵍ q' q) (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ))

-- Allocating a cell accumulates nothing (`BOX`); letting time pass costs
-- exactly the lock it passes (`DELAY`).

alloc-reach : ∀ {A ρ} {𝕊 : State []} → (V : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢ᵛ⦂ A)
            ------------------------------------------------------------
            → 𝕊 ⊑ₛ[ 𝟏ᵣ ] (𝕊 ∷ₛ V)

alloc-reach V = reach (≤ₛ-res ≤ₛ-refl) ≾ᵣ-refl

delay-reach : ∀ {ρ} {𝕊 : State []}
            ----------------------------
            → 𝕊 ⊑ₛ[ ρ ] (𝕊 ⟨ ρ ⟩ₛ)

delay-reach {ρ} = reach (≤ₛ-lock ≤ₛ-refl) (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ ρ))

-- Extending twice is extending once along the composite.

-- The grade bound is invisible: it only ever reaches a `⟨⟩-≤-ren`.

suc-comp-ren-irr : ∀ {𝕊 𝕊₁ : State []} {ρ₀ ρ₁ : R} → (e : 𝕊 ≤ₛ 𝕊₁)
                 → (b b' : κₛ e ·ᵣ ρ₁ ≾ᵣ ρ₀)
                 → suc-comp-ren e b ≐ʳ suc-comp-ren e b'
suc-comp-ren-irr e b b' rewrite ≾ᵣ-irrelevant b b' = ≐ʳ-refl

-- A grade relaxation commutes past the two renamings `suc-comp-ren` inserts.

⟨⟩-μ-≤-comm : ∀ {Γ ρ ρ₁ ρ₂} → (p : ρ₂ ≾ᵣ ρ₁) → (p' : ρ ·ᵣ ρ₂ ≾ᵣ ρ ·ᵣ ρ₁)
            → (⟨⟩-≤-ren p' ∘ʳ ⟨⟩-μ-ren {Δ = Γ} {ρ = ρ} {ρ' = ρ₂})
            ≐ʳ (⟨⟩-μ-ren ∘ʳ ⟨⟩-≤-ren p)
⟨⟩-μ-≤-comm p p' = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

wk-≤-comm : ∀ {Γ A ρ₁ ρ₂} → (p : ρ₂ ≾ᵣ ρ₁)
          → (⟨⟩-≤-ren p ∘ʳ cong-⟨⟩-ren {ρ = ρ₂} (wk-ren {Δ = Γ} {A = A}))
          ≐ʳ (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren p)
wk-≤-comm p = mk≐ʳ go
  where
    go : ∀ {A' σ} → (x : A' ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

-- Changing the residual grade is post-composing with a relaxation.

suc-comp-ren-≤ : ∀ {𝕊 𝕊₁ : State []} {ρ₀ ρ₁ ρ₂ : R} → (e : 𝕊 ≤ₛ 𝕊₁)
               → (b  : κₛ e ·ᵣ ρ₂ ≾ᵣ ρ₀)
               → (b₁ : κₛ e ·ᵣ ρ₁ ≾ᵣ ρ₀)
               → (p  : ρ₂ ≾ᵣ ρ₁)
               → suc-comp-ren e b ≐ʳ (suc-comp-ren e b₁ ∘ʳ ⟨⟩-≤-ren p)

suc-comp-ren-≤ ≤ₛ-refl b b₁ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

suc-comp-ren-≤ (≤ₛ-lock q) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ q _ _ (·ᵣ-monoʳ-≾ᵣ p)) ≐ʳ-refl)
    (≐ʳ-trans (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) (⟨⟩-≤-ren (·ᵣ-monoʳ-≾ᵣ p))
                          ⟨⟩-μ-ren)
      (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (⟨⟩-μ-≤-comm p (·ᵣ-monoʳ-≾ᵣ p)))
                (≐ʳ-sym (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) ⟨⟩-μ-ren (⟨⟩-≤-ren p)))))

suc-comp-ren-≤ (≤ₛ-res q) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ q _ _ p) ≐ʳ-refl)
    (≐ʳ-trans (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) (⟨⟩-≤-ren p)
                          (cong-⟨⟩-ren wk-ren))
      (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (wk-≤-comm p))
                (≐ʳ-sym (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) (cong-⟨⟩-ren wk-ren)
                                    (⟨⟩-≤-ren p)))))

-- Relaxing the source grade is pre-composing with a relaxation (the mirror of
-- `suc-comp-ren-≤`, which relaxes the residual one).

suc-comp-ren-≤ˡ : ∀ {𝕊 𝕊₁ : State []} {ρ₀ ρ₁ ρ₂ : R} → (e : 𝕊 ≤ₛ 𝕊₁)
                → (b  : κₛ e ·ᵣ ρ₂ ≾ᵣ ρ₀)
                → (b₁ : κₛ e ·ᵣ ρ₂ ≾ᵣ ρ₁)
                → (p  : ρ₁ ≾ᵣ ρ₀)
                → suc-comp-ren e b ≐ʳ (⟨⟩-≤-ren p ∘ʳ suc-comp-ren e b₁)

suc-comp-ren-≤ˡ ≤ₛ-refl b b₁ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

suc-comp-ren-≤ˡ (≤ₛ-lock e) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ˡ e _ _ p) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren p) (suc-comp-ren e _) ⟨⟩-μ-ren)

suc-comp-ren-≤ˡ (≤ₛ-res e) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ˡ e _ _ p) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren p) (suc-comp-ren e _)
                       (cong-⟨⟩-ren wk-ren))

-- Extending twice is extending once along the composite.

suc-comp-ren-∘-≐ʳ : ∀ {𝕊 𝕊₁ 𝕊₂ : State []} {ρ₀ ρ₁ ρ₂ : R}
                 → (e : 𝕊 ≤ₛ 𝕊₁) → (e' : 𝕊₁ ≤ₛ 𝕊₂)
                 → (b  : κₛ (≤ₛ-trans e e') ·ᵣ ρ₂ ≾ᵣ ρ₀)
                 → (b₁ : κₛ e  ·ᵣ ρ₁ ≾ᵣ ρ₀)
                 → (b₂ : κₛ e' ·ᵣ ρ₂ ≾ᵣ ρ₁)
                 ------------------------------------------------------
                 → suc-comp-ren (≤ₛ-trans e e') b
                 ≐ʳ (suc-comp-ren e b₁ ∘ʳ suc-comp-ren e' b₂)

-- `≤ₛ-trans e ≤ₛ-refl` is `e`, so the composite is `e` at a relaxed grade
suc-comp-ren-∘-≐ʳ {ρ₂ = ρ₂} e ≤ₛ-refl b b₁ b₂ =
  suc-comp-ren-≤ e b b₁
    (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ ρ₂)) b₂)

suc-comp-ren-∘-≐ʳ e (≤ₛ-lock e') b b₁ b₂ =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-∘-≐ʳ e e' _ b₁ _) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (suc-comp-ren e b₁) (suc-comp-ren e' _) ⟨⟩-μ-ren)

suc-comp-ren-∘-≐ʳ e (≤ₛ-res e') b b₁ b₂ =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-∘-≐ʳ e e' _ b₁ _) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (suc-comp-ren e b₁) (suc-comp-ren e' _)
                       (cong-⟨⟩-ren wk-ren))

-- `suc-comp-ren` sends a locked variable to a locked variable: the extension
-- embeds `toCtx 𝕊` into `toCtx 𝕊₁`, under the lock.

≤ₛ-embed : ∀ {𝕊 𝕊₁ : State []} → (e : 𝕊 ≤ₛ 𝕊₁) → ∀ {A σ}
         → A ∈[ σ ] toCtx 𝕊 → Σ[ σ' ∈ R ] A ∈[ σ' ] toCtx 𝕊₁
≤ₛ-embed ≤ₛ-refl             {σ = σ} x = σ , x
≤ₛ-embed (≤ₛ-lock {ρ = ρ} e) x with ≤ₛ-embed e x
... | σ' , y = σ' ·ᵣ ρ , Tl-⟨⟩ y
≤ₛ-embed (≤ₛ-res e)          x with ≤ₛ-embed e x
... | σ' , y = σ' , Tl-∷ y

suc-comp-ren-img : ∀ {𝕊 𝕊₁ : State []} {ρ₂ ρ₃ : R} → (e : 𝕊 ≤ₛ 𝕊₁)
                 → (b : κₛ e ·ᵣ ρ₃ ≾ᵣ ρ₂)
                 → ∀ {A σ} → (x : A ∈[ σ ] toCtx 𝕊)
                 → var-img (suc-comp-ren e b) (Tl-⟨⟩ x)
                 ≡ (proj₁ (≤ₛ-embed e x) ·ᵣ ρ₃ , Tl-⟨⟩ (proj₂ (≤ₛ-embed e x)))

suc-comp-ren-img ≤ₛ-refl     b x = refl
suc-comp-ren-img (≤ₛ-lock e) b x =
  cong (var-img′ ⟨⟩-μ-ren) (suc-comp-ren-img e _ x)
suc-comp-ren-img (≤ₛ-res e)  b x =
  cong (var-img′ (cong-⟨⟩-ren wk-ren)) (suc-comp-ren-img e _ x)

-- The embedding is functorial, and the two `⟨⟩-η` renamings are its identity
-- steps. Together these compute what `reach-renᵘ` and `unbox-ren` do to a
-- variable, which is all the lookup coherences need.

≤ₛ-embed-∘ : ∀ {𝕊 𝕊₁ 𝕊₂ : State []} → (e : 𝕊 ≤ₛ 𝕊₁) → (e' : 𝕊₁ ≤ₛ 𝕊₂)
           → ∀ {A σ} → (x : A ∈[ σ ] toCtx 𝕊)
           → ≤ₛ-embed (≤ₛ-trans e e') x ≡ ≤ₛ-embed e' (proj₂ (≤ₛ-embed e x))
≤ₛ-embed-∘ e ≤ₛ-refl              x = refl
≤ₛ-embed-∘ e (≤ₛ-lock {ρ = ρ} e') x =
  cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (≤ₛ-embed-∘ e e' x)
≤ₛ-embed-∘ e (≤ₛ-res e')          x =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (≤ₛ-embed-∘ e e' x)

-- What the embedding does to a variable's grade: it accumulates exactly the
-- extension's own grade, the locks passed being the same ones.

≤ₛ-embed-grade : ∀ {𝕊 𝕊₁ : State []} → (e : 𝕊 ≤ₛ 𝕊₁) → ∀ {A σ}
               → (x : A ∈[ σ ] toCtx 𝕊)
               → proj₁ (≤ₛ-embed e x) ≃ᵣ σ ·ᵣ κₛ e
≤ₛ-embed-grade ≤ₛ-refl             {σ = σ} x = ≃ᵣ-sym (·ᵣ-identityʳ σ)
≤ₛ-embed-grade (≤ₛ-lock {ρ = ρ} e) {σ = σ} x =
  ≃ᵣ-trans (·ᵣ-cong (≤ₛ-embed-grade e x) ≃ᵣ-refl)
           (·ᵣ-assoc σ (κₛ e) ρ)
≤ₛ-embed-grade (≤ₛ-res e)          x = ≤ₛ-embed-grade e x

-- What a reach does to a variable: the embedding of its extension.

reach-renᵘ-img : ∀ {𝕊 𝕊' : State []} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
               → ∀ {A σ} → (x : A ∈[ σ ] toCtx 𝕊)
               → var-img (reach-renᵘ q) x ≡ ≤ₛ-embed (ext q) x
reach-renᵘ-img q x =
  trans (cong (λ t → var-img′ ⟨⟩-η-ren
                       (var-img′ (suc-comp-ren (ext q) (reach-bound q)) t))
              (⟨⟩-η⁻¹-img x))
        (cong (var-img′ ⟨⟩-η-ren)
              (suc-comp-ren-img (ext q) (reach-bound q) x))

unbox-ren-img : ∀ {𝕊 𝕊' : State []} {ρ : R} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
              → ∀ {A σ} → (x : A ∈[ σ ] toCtx 𝕊)
              → var-img (unbox-ren q) (Tl-⟨⟩ x) ≡ ≤ₛ-embed (ext q) x
unbox-ren-img q x =
  cong (var-img′ ⟨⟩-η-ren) (suc-comp-ren-img (ext q) (reach-bound q) x)

-- What a whole run accumulates: the closure of `Reduction`'s
-- per-step facts under composition, packaged as the reach a run licenses.

steps-extends-state : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
                    → cf ⟶* cf' → Config.state cf ≤ₛ Config.state cf'

steps-extends-state done     = ≤ₛ-refl
steps-extends-state (r ▸ rs) =
  ≤ₛ-trans (step-extends-state r) (steps-extends-state rs)

steps-grade-≾ : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
              → (rs : cf ⟶* cf')
              → κₛ (steps-extends-state rs) ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ ∣ ε ∣ᵉ

steps-grade-≾ {ε = ε} done = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ ∣ ε ∣ᵉ)
steps-grade-≾ {ε' = ε'} (r ▸ rs) =
  ≾ᵣ-trans
    (≃ᵣ⇒≾ᵣ
      (≃ᵣ-trans (·ᵣ-cong (κₛ-trans (step-extends-state r) (steps-extends-state rs)) ≃ᵣ-refl) (·ᵣ-assoc (κₛ (step-extends-state r)) (κₛ (steps-extends-state rs)) ∣ ε' ∣ᵉ)))
    (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (steps-grade-≾ rs)) (step-grade-≾ r))

-- The renaming a whole run licenses. A run's bound relates two locked contexts,
-- so it goes straight to `suc-comp-ren` rather than through a reach.

steps-ren : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
          → (rs : cf ⟶* cf')
          → Ren [] (toCtx (Config.state cf') ⟨ ∣ ε' ∣ᵉ ⟩)
                   (toCtx (Config.state cf)  ⟨ ∣ ε ∣ᵉ  ⟩)
steps-ren rs = suc-comp-ren (steps-extends-state rs) (steps-grade-≾ rs)

-- A step refines the scrutinee's value type, so a congruence rule subsumes the
-- continuation's binder. A run stacks those subsumptions up; a `subV` spine
-- does not flatten, so the stack is kept as it stands and described by what
-- substituting into it does.

subCtx-run : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
           → cf ⟶* cf' → ∀ {Γ C} → Γ ∷ A ⊢ᶜ⦂ C → Γ ∷ B ⊢ᶜ⦂ C
subCtx-run done     N = N
subCtx-run (r ▸ rs) N = subCtx-run rs (subCtx (step-refines-type r) N)

spine : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
      → cf ⟶* cf' → ∀ {Γ} → Γ ⊢ᵛ⦂ B → Γ ⊢ᵛ⦂ A
spine done     V = V
spine (r ▸ rs) V = subV (spine rs V) (step-refines-type r)

-- The subsumption laws of `MonomorphicCalculus.Syntax.Substitution.Subsumption`, iterated along
-- a run.

subCtx-run-sub : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
               → (rs : cf ⟶* cf') → ∀ {Γ C} → (N : Γ ∷ A ⊢ᶜ⦂ C) → (V : Γ ⊢ᵛ⦂ B)
               ---------------------------------------------------------------
               → subCtx-run rs N [ split-[] ↦ V ]c
               ≡ N [ split-[] ↦ spine rs V ]c

subCtx-run-sub done     N V = refl
subCtx-run-sub (r ▸ rs) N V =
  trans (subCtx-run-sub rs (subCtx (step-refines-type r) N) V)
        (subCtx-sub (step-refines-type r) N (spine rs V))

subCtx-run-ren : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
               → (rs : cf ⟶* cf') → ∀ {Γ Δ C} → (r : Ren [] Δ Γ)
               → (N : Γ ∷ A ⊢ᶜ⦂ C)
               -----------------------------------------------
               → C-rename (cong-∷-ren r) (subCtx-run rs N)
               ≡ subCtx-run rs (C-rename (cong-∷-ren r) N)

subCtx-run-ren done      r N = refl
subCtx-run-ren (r₀ ▸ rs) r N =
  trans (subCtx-run-ren rs r (subCtx (step-refines-type r₀) N))
        (cong (subCtx-run rs) (subCtx-ren r (step-refines-type r₀) N))

-- Both congruence rules retype the continuation along `suc-comp-ren` of the
-- step's own extension, and subsume its binder to the refined value type.

seq-steps : ∀ {A A₁ B ε ε' ε₂} {𝕊 𝕊₁ : State []}
          → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M₁ : toCtx 𝕊₁ ⊢ᶜ⦂ A₁ ! ε'}
          → (rs : ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₁ ∣ M₁ ⟩)
          → (N : toCtx 𝕊 ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂)
          -----------------------------------------------------------------
          → Σ[ N₁ ∈ (toCtx 𝕊₁ ⟨ ∣ ε' ∣ᵉ ⟩ ∷ A₁ ⊢ᶜ⦂ B ! ε₂) ]
              (⟨ 𝕊 ∣ M ⨟ N ⟩ ⟶* ⟨ 𝕊₁ ∣ M₁ ⨟ N₁ ⟩)
            × (N₁ ≡ subCtx-run rs (C-rename (cong-∷-ren (steps-ren rs)) N))

seq-steps done N =
  N , done , sym (C-rename-id-≡ (cong-∷-ren-id-≐ʳ (⟨⟩-≤-ren-id-≐ʳ _)) N)

seq-steps (r ▸ rs) N
  with seq-steps rs
         (subCtx (step-refines-type r)
           (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                               (step-grade-≾ r))) N))
... | N₁ , rs' , eN₁ =
    N₁
  , SEQ-STEP r (step-grade-≾ r) ▸ rs'
  , trans eN₁
      (cong (subCtx-run rs)
        (trans
          (subCtx-ren (steps-ren rs) (step-refines-type r)
            (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                (step-grade-≾ r))) N))
          (cong (subCtx (step-refines-type r))
            (trans
              (sym (C-rename-∘ (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                            (step-grade-≾ r)))
                                  (cong-∷-ren (steps-ren rs)) N))
              (C-rename-≡
                (≐ʳ-trans
                  (≐ʳ-sym (cong-∷-ren-∘-≐ʳ (suc-comp-ren (step-extends-state r)
                                                        (step-grade-≾ r))
                                          (steps-ren rs)))
                  (cong-∷-ren-≐ʳ
                    (≐ʳ-sym (suc-comp-ren-∘-≐ʳ (step-extends-state r)
                                              (steps-extends-state rs)
                                              _ (step-grade-≾ r)
                                              (steps-grade-≾ rs)))))
                N)))))

-- The same under `handle`, which also retypes the clauses along the barrier
-- lock, at the run's own extension.

steps-barrier-ren : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
                  → (rs : cf ⟶* cf')
                  → Ren [] (toCtx (Config.state cf') ⟨ ⊤ᵣ ⟩)
                           (toCtx (Config.state cf)  ⟨ ⊤ᵣ ⟩)
steps-barrier-ren rs = suc-comp-ren (steps-extends-state rs) (≾-⊤ᵣ _)

handle-steps : ∀ {A A₁ B ε ε' ε₂} {𝕊 𝕊₁ : State []}
             → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M₁ : toCtx 𝕊₁ ⊢ᶜ⦂ A₁ ! ε'}
             → (rs : ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₁ ∣ M₁ ⟩)
             → (H : (op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx 𝕊 ⟨ ⊤ᵣ ⟩))
             → (N : toCtx 𝕊 ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂)
             ---------------------------------------------------------------
             → Σ[ H₁ ∈ ((op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx 𝕊₁ ⟨ ⊤ᵣ ⟩)) ]
               Σ[ N₁ ∈ (toCtx 𝕊₁ ⟨ ∣ ε' ∣ᵉ ⟩ ∷ A₁ ⊢ᶜ⦂ B ! ε₂) ]
                 (⟨ 𝕊 ∣ handle M `with H `in N ⟩ ⟶*
                  ⟨ 𝕊₁ ∣ handle M₁ `with H₁ `in N₁ ⟩)
               × (∀ op ε₃ → H₁ op ε₃
                    ≡ C-rename (cong-∷-ren (cong-∷-ren (steps-barrier-ren rs)))
                               (H op ε₃))
               × (N₁ ≡ subCtx-run rs (C-rename (cong-∷-ren (steps-ren rs)) N))

handle-steps {B = B} {𝕊 = 𝕊} done H N =
    H , N , done
  , (λ op ε₃ →
       sym (C-rename-id-≡
              (cong-∷-ren-id-≐ʳ (cong-∷-ren-id-≐ʳ (⟨⟩-≤-ren-id-≐ʳ _)))
              (H op ε₃)))
  , sym (C-rename-id-≡ (cong-∷-ren-id-≐ʳ (⟨⟩-≤-ren-id-≐ʳ _)) N)

handle-steps {B = B} {𝕊 = 𝕊} {𝕊₁ = 𝕊₁} (_▸_ {cf₂ = ⟨ 𝕊' ∣ M' ⟩} r rs) H N
  with handle-steps rs
         (λ op ε₃ →
            C-rename (cong-∷-ren (cong-∷-ren
                       (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _))))
              (H op ε₃))
         (subCtx (step-refines-type r)
           (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                               (step-grade-≾ r))) N))
... | H₁ , N₁ , rs' , eH₁ , eN₁ =
    H₁ , N₁
  , HANDLE-STEP r (step-grade-≾ r) ▸ rs'
  , (λ op ε₃ →
       trans (eH₁ op ε₃)
         (trans
           (sym (C-rename-∘
                   (cong-∷-ren (cong-∷-ren
                     (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _))))
                   (cong-∷-ren (cong-∷-ren (steps-barrier-ren rs)))
                   (H op ε₃)))
           (C-rename-≡
             (≐ʳ-trans
               (≐ʳ-sym (cong-∷-ren-∘-≐ʳ
                          (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                    (≾-⊤ᵣ _)))
                          (cong-∷-ren (steps-barrier-ren rs))))
               (cong-∷-ren-≐ʳ
                 (≐ʳ-trans
                   (≐ʳ-sym (cong-∷-ren-∘-≐ʳ
                              (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _))
                              (steps-barrier-ren rs)))
                   (cong-∷-ren-≐ʳ
                     (≐ʳ-sym (suc-comp-ren-∘-≐ʳ (step-extends-state r)
                                               (steps-extends-state rs)
                                               _ (≾-⊤ᵣ _) (≾-⊤ᵣ _)))))))
             (H op ε₃))))
  , trans eN₁
      (cong (subCtx-run rs)
        (trans
          (subCtx-ren (steps-ren rs) (step-refines-type r)
            (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                (step-grade-≾ r))) N))
          (cong (subCtx (step-refines-type r))
            (trans
              (sym (C-rename-∘ (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                            (step-grade-≾ r)))
                                  (cong-∷-ren (steps-ren rs)) N))
              (C-rename-≡
                (≐ʳ-trans
                  (≐ʳ-sym (cong-∷-ren-∘-≐ʳ (suc-comp-ren (step-extends-state r)
                                                        (step-grade-≾ r))
                                          (steps-ren rs)))
                  (cong-∷-ren-≐ʳ
                    (≐ʳ-sym (suc-comp-ren-∘-≐ʳ (step-extends-state r)
                                              (steps-extends-state rs)
                                              _ (step-grade-≾ r)
                                              (steps-grade-≾ rs)))))
                N)))))

-- Transporting a reach's residual grade along a grade equality: the renaming is
-- unchanged, since the bound is all that differs (`suc-comp-ren-irr`). This is
-- what reconciles a run's `∣ 𝟏ₑ ∣ᵉ` with the `𝟏ᵣ` a graded reach wants.

suc-comp-ren-grade : ∀ {𝕊 𝕊₁ : State []} {ρ'' ρ₁ ρ₂ : R} → (e : 𝕊 ≤ₛ 𝕊₁)
                   → (eg : ρ₁ ≡ ρ₂)
                   → (b₁ : κₛ e ·ᵣ ρ₁ ≾ᵣ ρ'')
                   → (b₂ : κₛ e ·ᵣ ρ₂ ≾ᵣ ρ'')
                   → (suc-comp-ren e b₁ ∘ʳ eq-ren (cong (toCtx 𝕊₁ ⟨_⟩) eg))
                   ≐ʳ suc-comp-ren e b₂
suc-comp-ren-grade e refl b₁ b₂ =
  ≐ʳ-trans (∘ʳ-identityʳ-≐ʳ (suc-comp-ren e b₁)) (suc-comp-ren-irr e b₁ b₂)

-- The same on the source side: an extension started at a propositionally
-- equal guard is the same renaming, `eq-ren` being the identity there.

suc-comp-ren-grade-src : ∀ {𝕊 𝕊₁ : State []} {ρ₁ ρ₂ ρ₃ : R} → (e : 𝕊 ≤ₛ 𝕊₁)
                       → (eg : ρ₁ ≡ ρ₂)
                       → (b₁ : κₛ e ·ᵣ ρ₃ ≾ᵣ ρ₂)
                       → (b₂ : κₛ e ·ᵣ ρ₃ ≾ᵣ ρ₁)
                       → (eq-ren (cong (toCtx 𝕊 ⟨_⟩) eg) ∘ʳ suc-comp-ren e b₁)
                       ≐ʳ suc-comp-ren e b₂
suc-comp-ren-grade-src e refl b₁ b₂ =
  ≐ʳ-trans (∘ʳ-identityˡ-≐ʳ (suc-comp-ren e b₁)) (suc-comp-ren-irr e b₁ b₂)

-- Crossing a lock and then moving on is crossing it into the later state: both
-- send `Tl-⟨⟩ x` to the composite extension's embedding.

reach-unbox-ren-≐ʳ : ∀ {ρ} {𝕊 𝕊' 𝕊'' : State []}
                  → (q' : 𝕊' ⊑ₛ[ 𝟏ᵣ ] 𝕊'') → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
                  → (unbox-ren q ∘ʳ reach-renᵘ q') ≐ʳ unbox-ren (reach-∘ q' q)
reach-unbox-ren-≐ʳ q' q = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) =
      trans (cong (var-img′ (reach-renᵘ q')) (unbox-ren-img q x))
        (trans (reach-renᵘ-img q' (proj₂ (≤ₛ-embed (ext q) x)))
          (trans (sym (≤ₛ-embed-∘ (ext q) (ext q') x))
                 (sym (unbox-ren-img (reach-∘ q' q) x))))

-- Composition for `reach-renᵘ`: the same law conjugated by `⟨⟩-η⁻¹-ren`.

reach-renᵘ-∘ : ∀ {𝕊 𝕊' 𝕊'' : State []}
             → (q' : 𝕊' ⊑ₛ[ 𝟏ᵣ ] 𝕊'') → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
             → reach-renᵘ (reach-∘ q' q) ≐ʳ (reach-renᵘ q ∘ʳ reach-renᵘ q')
reach-renᵘ-∘ q' q =
  ≐ʳ-trans (reach-renᵘ-unbox (reach-∘ q' q))
    (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (≐ʳ-sym (reach-unbox-ren-≐ʳ q' q)))
      (≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ʳ ⟨⟩-η⁻¹-ren (unbox-ren q) (reach-renᵘ q')))
                (∘ʳ-≐ʳ (≐ʳ-sym (reach-renᵘ-unbox q)) ≐ʳ-refl)))

-- Allocating a cell renames the old context by weakening past it.

alloc-ren-≐ʳ : ∀ {A ρ} {𝕊 : State []} → (V : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢ᵛ⦂ A)
            → reach-renᵘ (alloc-reach V) ≐ʳ wk-ren
alloc-ren-≐ʳ V = mk≐ʳ (λ x → reach-renᵘ-img (alloc-reach V) x)

-- The same for the renaming an `unbox` consumes: splitting the guard into the
-- reach's own part and a residual `σ`, then crossing the lock under `σ`, is the
-- extension at residual `σ`.

unbox-ren-μ-≐ʳ : ∀ {𝕊 𝕊₁ : State []} {ρ σ : R} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊₁)
              → (b : κₛ (ext q) ·ᵣ σ ≾ᵣ ρ ·ᵣ σ)
              → (⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren {ρ = σ} (unbox-ren q))
              ≐ʳ suc-comp-ren (ext q) b
unbox-ren-μ-≐ʳ {σ = σ} q b = mk≐ʳ go
  where
    go : ∀ {A τ} → (x : A ∈[ τ ] _) → _
    go (Tl-⟨⟩ x) = trans (cong (Var-⟨⟩ σ) (unbox-ren-img q x))
                         (sym (suc-comp-ren-img (ext q) b x))

-- Entering the barrier and then following an extension is the reach at budget
-- `⊤ᵣ`: the residual grade is relaxed from `𝟏ᵣ` to `⊤ᵣ` (`suc-comp-ren-≤`).

barrier-unbox-≐ʳ : ∀ {𝕊 𝕊₁ : State []} → (q : 𝕊 ⊑ₛ[ ⊤ᵣ ] 𝕊₁)
                 → (b : κₛ (ext q) ·ᵣ ⊤ᵣ ≾ᵣ ⊤ᵣ)
                 → (suc-comp-ren (ext q) b ∘ʳ barrier-ren) ≐ʳ unbox-ren q
barrier-unbox-≐ʳ q b =
  ≐ʳ-trans
    (≐ʳ-sym (∘ʳ-assoc-≐ʳ (suc-comp-ren (ext q) b) (⟨⟩-≤-ren (≾-⊤ᵣ 𝟏ᵣ))
                        ⟨⟩-η-ren))
    (∘ʳ-≐ʳ (≐ʳ-sym (suc-comp-ren-≤ (ext q) (reach-bound q) b (≾-⊤ᵣ 𝟏ᵣ)))
          ≐ʳ-refl)

-- At the state itself the `⊤ᵣ`-reach is entering the barrier.

barrier-reach : ∀ {𝕊 : State []} → 𝕊 ⊑ₛ[ ⊤ᵣ ] 𝕊
barrier-reach = reach ≤ₛ-refl (≾-⊤ᵣ _)

barrier-reach-≐ʳ : ∀ {𝕊 : State []} → unbox-ren (barrier-reach {𝕊}) ≐ʳ barrier-ren
barrier-reach-≐ʳ = ∘ʳ-≐ʳ (⟨⟩-≤-ren-≐ʳ _ _) ≐ʳ-refl

-- Crossing a lock and then following a guarded reach is following the same reach
-- at the unit budget (`reach-≤`): the source grade is relaxed from `ρ` to `𝟏ᵣ`,
-- which is pre-composition with `⟨⟩-≤-ren` (`suc-comp-ren-≤ˡ`).

unbox-ren-unit : ∀ {ρ} {𝕊 𝕊' : State []} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊') → (p : ρ ≾ᵣ 𝟏ᵣ)
               → ((⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p) ∘ʳ unbox-ren q)
               ≐ʳ reach-renᵘ (reach-≤ q p)
unbox-ren-unit q p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go x = cong (var-img′ ⟨⟩-η-ren)
                (sym (at (suc-comp-ren-≤ˡ (ext q) (reach-bound (reach-≤ q p))
                                          (reach-bound q) p)
                         (proj₂ (var-img ⟨⟩-η⁻¹-ren x))))

-- Two reaches whose renamings are identity-like: the unit reach at a state, and
-- the reach a `DELAY` takes (whose target context is the source under the
-- lock). Both are needed to recognise a reduct as the action of an environment.

-- Both are `≤ₛ-embed` of the identity extension, which is the identity: a
-- variable of a state context cannot be case-split on, so this goes through the
-- `var-img` layer rather than pointwise.

reach-renᵘ-id-≐ʳ : ∀ {𝕊 : State []} → reach-renᵘ (reach-id {𝕊}) ≐ʳ id-ren
reach-renᵘ-id-≐ʳ = mk≐ʳ (λ x → reach-renᵘ-img reach-id x)

unbox-ren-delay-≐ʳ : ∀ {ρ} {𝕊 : State []}
                  → unbox-ren (delay-reach {ρ} {𝕊}) ≐ʳ id-ren
unbox-ren-delay-≐ʳ = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = unbox-ren-img delay-reach x

-- The lookup's renaming composite depends on the state only through two
-- contexts, the stored value, and three proofs.

lookup-ren′ : ∀ {A ρ σ} {Γ : Ctx} → (Γf Γs : Ctx)
            → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
            → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≾ᵣ σ)
            → (rel : σ ≾ᵣ ρ)
            → Ren [] Γ (([] ++ᶜ Γf) ⟨ ρ ⟩)
lookup-ren′ {A} {ρ} Γf Γs eq h rel =
  (((  eq-ren ++ᶜ-identityˡ
   ∘ʳ ⟨⟩-≤-ren rel)
   ∘ʳ (⟨⟩-≤-ren h ∘ʳ wk-ren-⟨ρ⟩-ctx refl))
   ∘ʳ eq-ren (sym (++ᶜ-assoc Γf ([] ∷ [ ρ ] A) Γs)))
   ∘ʳ eq-ren eq

lookup-body′ : ∀ {A ρ σ} {Γ : Ctx} → (Γf Γs : Ctx)
             → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
             → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≾ᵣ σ)
             → (rel : σ ≾ᵣ ρ)
             → ([] ++ᶜ Γf) ⟨ ρ ⟩ ⊢ᵛ⦂ A
             → Γ ⊢ᵛ⦂ A
lookup-body′ Γf Γs eq h rel U = V-rename (lookup-ren′ Γf Γs eq h rel) U

lookup-body : ∀ {A ρ} → (𝕊 : State []) → (t : Var (toCtx 𝕊) ([ ρ ] A))
            → proj₁ t ≾ᵣ ρ → toCtx 𝕊 ⊢ᵛ⦂ A
lookup-body {A} {ρ} 𝕊 (ρ' , z) rel =
  lookup-body′
    (toCtx (split-state-fst 𝕊 z)) (toCtx (split-state-snd 𝕊 z))
    (split-state-++ᶜ 𝕊 z)
    (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-trans (≃ᵣ-trans (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd 𝕊 z))) (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd 𝕊 z))))) (≃ᵣ-reflexive (sym (grades-≡ (split-state-snd 𝕊 z))))) (≃ᵣ-reflexive (snd-split-time≡time-from-head 𝕊 z))))
    rel
    (resource-lookup 𝕊 z)

-- Two lookups at corresponding data agree: match the context equalities, and
-- everything else is proof-irrelevant.

lookup-body′-≡ : ∀ {A ρ σ} {Γ Γ' : Ctx} → (eΓ : Γ' ≡ Γ)
               → {Γf Γf' Γs Γs' : Ctx} → (eF : Γf' ≡ Γf) → (eS : Γs' ≡ Γs)
               → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
               → (eq' : (Γf' ∷ [ ρ ] A) ++ᶜ Γs' ≡ Γ')
               → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≾ᵣ σ)
               → (h' : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs') ≾ᵣ σ)
               → (rel rel' : σ ≾ᵣ ρ)
               → (U : ([] ++ᶜ Γf) ⟨ ρ ⟩ ⊢ᵛ⦂ A)
               → (U' : ([] ++ᶜ Γf') ⟨ ρ ⟩ ⊢ᵛ⦂ A)
               → U ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) eF) U'
               → lookup-body′ Γf Γs eq h rel U
               ≡ castᵛ eΓ (lookup-body′ Γf' Γs' eq' h' rel' U')
lookup-body′-≡ refl refl refl eq eq' h h' rel rel' U U' eU
  rewrite uip {p = eq} {q = eq'} | ≾ᵣ-irrelevant h h'
        | ≾ᵣ-irrelevant rel rel' = V-rename-cong _ eU

-- Same cell, same value: the bound is `≾ᵣ`-irrelevant.

lookup-body-≡ : ∀ {A ρ} → (𝕊 : State [])
              → {t t' : Var (toCtx 𝕊) ([ ρ ] A)} → t ≡ t'
              → (rel : proj₁ t ≾ᵣ ρ) → (rel' : proj₁ t' ≾ᵣ ρ)
              → lookup-body 𝕊 t rel ≡ lookup-body 𝕊 t' rel'
lookup-body-≡ 𝕊 refl rel rel' =
  cong (lookup-body 𝕊 _) (≾ᵣ-irrelevant rel rel')


-- An already-allocated cell is split off at the same state, and holds the
-- same value, however far the state has grown since.

≤ₛ-embed-fst : ∀ {𝕊 𝕊₁ : State []} → (e : 𝕊 ≤ₛ 𝕊₁) → ∀ {A ρ σ}
             → (x : [ ρ ] A ∈[ σ ] toCtx 𝕊)
             → split-state-fst 𝕊₁ (proj₂ (≤ₛ-embed e x))
             ≡ split-state-fst 𝕊 x

≤ₛ-embed-fst ≤ₛ-refl     x = refl
≤ₛ-embed-fst (≤ₛ-lock e) x = ≤ₛ-embed-fst e x
≤ₛ-embed-fst (≤ₛ-res e)  x = ≤ₛ-embed-fst e x

≤ₛ-embed-lookup : ∀ {𝕊 𝕊₁ : State []} → (e : 𝕊 ≤ₛ 𝕊₁) → ∀ {A ρ σ}
                → (x : [ ρ ] A ∈[ σ ] toCtx 𝕊)
                → resource-lookup 𝕊₁ (proj₂ (≤ₛ-embed e x))
                ≡ subst (λ 𝕊₀ → ([] ++ᶜ toCtx 𝕊₀) ⟨ ρ ⟩ ⊢ᵛ⦂ A)
                        (sym (≤ₛ-embed-fst e x))
                        (resource-lookup 𝕊 x)

≤ₛ-embed-lookup ≤ₛ-refl     x = refl
≤ₛ-embed-lookup (≤ₛ-lock e) x = ≤ₛ-embed-lookup e x
≤ₛ-embed-lookup (≤ₛ-res e)  x = ≤ₛ-embed-lookup e x

-- `SRed-fresh` compares the lookup at a later state with the value that was
-- stored: the part after the cell grows by exactly the context the extension
-- adds.

≤ₛ-ctx : {𝕊₀ 𝕊₂ : State []} → 𝕊₀ ≤ₛ 𝕊₂ → Ctx
≤ₛ-ctx ≤ₛ-refl                    = []
≤ₛ-ctx (≤ₛ-lock {ρ = ρ} e)        = ≤ₛ-ctx e ⟨ ρ ⟩
≤ₛ-ctx (≤ₛ-res {ρ = ρ} {A = A} e) = ≤ₛ-ctx e ∷ [ ρ ] A

≤ₛ-embed-snd-ctx : ∀ {A ρ σ} {𝕊₀ 𝕊₂ : State []} → (e : 𝕊₀ ≤ₛ 𝕊₂)
                 → (c : [ ρ ] A ∈[ σ ] toCtx 𝕊₀)
                 → toCtx (split-state-snd 𝕊₂ (proj₂ (≤ₛ-embed e c)))
                 ≡ toCtx (split-state-snd 𝕊₀ c) ++ᶜ ≤ₛ-ctx e

≤ₛ-embed-snd-ctx ≤ₛ-refl             c = refl
≤ₛ-embed-snd-ctx (≤ₛ-lock {ρ = ρ} e) c = cong (_⟨ ρ ⟩) (≤ₛ-embed-snd-ctx e c)
≤ₛ-embed-snd-ctx (≤ₛ-res e)          c = cong (_∷ _) (≤ₛ-embed-snd-ctx e c)

-- And the state itself grows the same way.

≤ₛ-ctx-toCtx : {𝕊₀ 𝕊₂ : State []} → (e : 𝕊₀ ≤ₛ 𝕊₂)
             → toCtx 𝕊₂ ≡ toCtx 𝕊₀ ++ᶜ ≤ₛ-ctx e
≤ₛ-ctx-toCtx ≤ₛ-refl             = refl
≤ₛ-ctx-toCtx (≤ₛ-lock {ρ = ρ} e) = cong (_⟨ ρ ⟩) (≤ₛ-ctx-toCtx e)
≤ₛ-ctx-toCtx (≤ₛ-res e)          = cong (_∷ _) (≤ₛ-ctx-toCtx e)

-- So an extension's embedding is the push under the context it adds.

≤ₛ-embed-push : ∀ {A ρ} {𝕊₀ 𝕊₂ : State []} → (e : 𝕊₀ ≤ₛ 𝕊₂)
              → (y : A ∈[ ρ ] toCtx 𝕊₀)
              → ≤ₛ-embed e y
              ≡ Var-cast (sym (≤ₛ-ctx-toCtx e))
                  (grade-++ᶜˡ ρ (≤ₛ-ctx e) , ∈-++ᶜˡ (≤ₛ-ctx e) y)

≤ₛ-embed-push ≤ₛ-refl             y = refl
≤ₛ-embed-push (≤ₛ-lock {ρ = ρ} e) y =
  trans (cong (Var-⟨⟩ ρ) (≤ₛ-embed-push e y))
    (trans (sym (Var-cast-⟨⟩ ρ (sym (≤ₛ-ctx-toCtx e)) _))
           (Var-cast-irr (cong (_⟨ ρ ⟩) (sym (≤ₛ-ctx-toCtx e)))
                         (sym (≤ₛ-ctx-toCtx (≤ₛ-lock e))) _))
≤ₛ-embed-push (≤ₛ-res {V = V} e)  y =
  trans (cong Var-∷ (≤ₛ-embed-push e y))
    (trans (sym (Var-cast-∷ (sym (≤ₛ-ctx-toCtx e)) _))
           (Var-cast-irr (cong (_∷ _) (sym (≤ₛ-ctx-toCtx e)))
                         (sym (≤ₛ-ctx-toCtx (≤ₛ-res {V = V} e))) _))

-- Looking up, at whatever state the run has reached, the cell `BOX` just
-- allocated returns the stored value, renamed.

-- Transporting a stored value along an equality of the states it was split off
-- at is transporting it along the contexts.

subst-state-castᵛ : ∀ {A ρ} {𝕊 𝕊' : State []} → (p : 𝕊 ≡ 𝕊')
                   → (U : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢ᵛ⦂ A)
                   → subst (λ 𝕊₀ → ([] ++ᶜ toCtx 𝕊₀ ⟨ ρ ⟩) ⊢ᵛ⦂ A) p U
                   ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) (cong toCtx p)) U
subst-state-castᵛ refl U = refl

alloc-lookup-ren : ∀ {A ρ σ} {𝕊 𝕊' : State []}
                 → (V : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢ᵛ⦂ A)
                 → (e : (𝕊 ∷ₛ V) ≤ₛ 𝕊')
                 → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ ≤ₛ-ctx e) ≾ᵣ σ)
                 → (rel : σ ≾ᵣ ρ)
                 → (q₀ : 𝕊 ⊑ₛ[ ρ ] 𝕊')
                 → ext q₀ ≡ ≤ₛ-trans (≤ₛ-res ≤ₛ-refl) e
                 → (lookup-ren′ (toCtx 𝕊) (≤ₛ-ctx e) refl h rel
                     ∘ʳ eq-ren (sym (≤ₛ-ctx-toCtx e)))
                 ≐ʳ (eq-ren (++ᶜ-identityˡ {toCtx 𝕊 ⟨ ρ ⟩}) ∘ʳ unbox-ren q₀)

alloc-lookup-ren {A} {ρ} {σ} {𝕊} {𝕊'} V e h rel q₀ eq₀ = mk≐ʳ go
  where
    Δ  = ≤ₛ-ctx e
    Δ₁ = [] ∷ [ ρ ] A
    eΓ = sym (≤ₛ-ctx-toCtx e)

    assoc = sym (++ᶜ-assoc (toCtx 𝕊) Δ₁ Δ)

    go : ∀ {A' τ} → (x : A' ∈[ τ ] (([] ++ᶜ toCtx 𝕊) ⟨ ρ ⟩)) → _
    go {A'} (Tl-⟨⟩ {ρ' = τ'} w) =
      trans (cong (λ t → f₅ (f₄ (f₃ (f₂ (f₁ t))))) s₀)
        (trans (cong (λ t → f₅ (f₄ (f₃ t)))
                     (wk-ren-⟨ρ⟩-ctx-img (Δ₁ ++ᶜ Δ) refl y))
          (trans (cong (λ t → f₅ (f₄ t))
                       (trans (eq-ren-img assoc (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) y))
                              (∈-++ᶜˡ-assoc Δ₁ Δ y)))
            (trans (eq-ren-img eΓ (∈-++ᶜˡ Δ (Tl-∷ y)))
              (sym (trans (cong (var-img′ (unbox-ren q₀)) s₀)
                     (trans (unbox-ren-img q₀ y)
                       (trans (cong (λ z → ≤ₛ-embed z y) eq₀)
                         (trans (≤ₛ-embed-∘ (≤ₛ-res ≤ₛ-refl) e y)
                                (≤ₛ-embed-push e (Tl-∷ y))))))))))
      where
        y : A' ∈[ τ' ] toCtx 𝕊
        y = subst (λ Γ₀ → A' ∈[ τ' ] Γ₀) ++ᶜ-identityˡ w

        f₁ = var-img′ {A = A'} (⟨⟩-≤-ren rel)
        f₂ = var-img′ {A = A'} (⟨⟩-≤-ren h ∘ʳ wk-ren-⟨ρ⟩-ctx refl)
        f₃ = var-img′ {A = A'} (eq-ren assoc)
        f₄ = var-img′ {A = A'} (eq-ren (refl {x = (toCtx 𝕊 ∷ [ ρ ] A) ++ᶜ Δ}))
        f₅ = var-img′ {A = A'} (eq-ren eΓ)

        s₀ : var-img (eq-ren (++ᶜ-identityˡ {toCtx 𝕊 ⟨ ρ ⟩})) (Tl-⟨⟩ w)
           ≡ (τ' ·ᵣ ρ , Tl-⟨⟩ y)
        s₀ = trans (eq-ren-img (++ᶜ-identityˡ {toCtx 𝕊 ⟨ ρ ⟩}) (Tl-⟨⟩ w))
                   (cong (λ z → τ' ·ᵣ ρ , z)
                         (subst-Tl-⟨⟩ (++ᶜ-identityˡ {toCtx 𝕊}) w))

-- `lookup-body′-≡` moves the lookup's own data onto the data the allocation
-- presents, via `≤ₛ-embed-fst`, `≤ₛ-embed-snd-ctx`, and `≤ₛ-embed-lookup`.

alloc-lookup-≡ : ∀ {A ρ} {𝕊 𝕊' : State []}
               → (V : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢ᵛ⦂ A)
               → (e : (𝕊 ∷ₛ V) ≤ₛ 𝕊')
               → (rel : proj₁ (≤ₛ-embed e (Hd {Γ = toCtx 𝕊})) ≾ᵣ ρ)
               → (q₀ : 𝕊 ⊑ₛ[ ρ ] 𝕊')
               → ext q₀ ≡ ≤ₛ-trans (≤ₛ-res ≤ₛ-refl) e
               → lookup-body 𝕊' (≤ₛ-embed e (Hd {Γ = toCtx 𝕊})) rel
               ≡ V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q₀) V

alloc-lookup-≡ {A} {ρ} {𝕊} {𝕊'} V e rel q₀ eq₀ =
  trans (lookup-body′-≡ eΓ eF eS _ refl _ h rel rel _ V eU)
    (trans (castᵛ-rename eΓ (lookup-ren′ (toCtx 𝕊) Δ refl h rel) V)
              (V-rename-≡ (alloc-lookup-ren V e h rel q₀ eq₀) V))
  where
    Δ  = ≤ₛ-ctx e
    Δ₁ = [] ∷ [ ρ ] A
    eΓ = sym (≤ₛ-ctx-toCtx e)
    eF = cong toCtx (sym (≤ₛ-embed-fst e (Hd {Γ = toCtx 𝕊})))
    eS = sym (trans (≤ₛ-embed-snd-ctx e (Hd {Γ = toCtx 𝕊})) ++ᶜ-identityˡ)

    h : ctx-grade (Δ₁ ++ᶜ Δ) ≾ᵣ proj₁ (≤ₛ-embed e (Hd {Γ = toCtx 𝕊}))
    h = ≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-trans (ctx-grade-++ᶜ Δ₁ Δ) (·ᵣ-identityˡ (ctx-grade Δ)))
                (≃ᵣ-reflexive (trans (sym (grade-++ᶜˡ-𝟏ᵣ Δ))
                     (sym (cong proj₁ (≤ₛ-embed-push e (Hd {Γ = toCtx 𝕊})))))))

    eU : resource-lookup 𝕊' (proj₂ (≤ₛ-embed e (Hd {Γ = toCtx 𝕊})))
       ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) eF) V
    eU = (trans (≤ₛ-embed-lookup e (Hd {Γ = toCtx 𝕊}))
                      (subst-state-castᵛ
                         (sym (≤ₛ-embed-fst e (Hd {Γ = toCtx 𝕊}))) V))

-- `𝕊 [ c ]⊑ᶜ 𝕊'`: an extension under which the cell `c` has ripened:
-- enough grade has accumulated at `c`'s own position for its `ρ`-box to be
-- read.

infix 4 _[_]⊑ᶜ_

record _[_]⊑ᶜ_ {A ρ σ} (𝕊 : State [])
                (c : [ ρ ] A ∈[ σ ] toCtx 𝕊) (𝕊' : State []) : Set where
  constructor read
  field
    extᶜ  : 𝕊 ≤ₛ 𝕊'
    ready : proj₁ (≤ₛ-embed extᶜ c) ≾ᵣ ρ

open _[_]⊑ᶜ_ public

-- What reading it yields.

lookupᶜ : ∀ {A ρ σ} {𝕊 𝕊' : State []} {c : [ ρ ] A ∈[ σ ] toCtx 𝕊}
        → 𝕊 [ c ]⊑ᶜ 𝕊' → toCtx 𝕊' ⊢ᵛ⦂ A
lookupᶜ {c = c} r = lookup-body _ (≤ₛ-embed (extᶜ r) c) (ready r)

