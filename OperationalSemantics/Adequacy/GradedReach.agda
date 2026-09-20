------------------------------------------------------------------------
-- Graded reachability: the frame the logical relation is indexed by. --
--                                                                    --
-- Kripke over an accessibility that carries a grade budget: an       --
-- extension together with the bound licensing the lock it crossed    --
-- — rather than over `≤ₛ` alone, since reindexing along `≤ₛ` is not  --
-- free weakening.                                                    --
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.GradedReach (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Substitutions.Base   Spec
open import Syntax.Substitutions.Action Spec
open import Syntax.Substitutions.Laws   Spec

-- `St ⊑ₛ[ ρ ] St'` — `St'` is reachable from `St` on the budget `ρ`: the grade
-- the extension accumulated stays below `ρ`. The `ₛ` marks it as refining the
-- state extension `≤ₛ`.

infix 4 _⊑ₛ[_]_

record _⊑ₛ[_]_ (St : 𝕊 []) (ρ : R) (St' : 𝕊 []) : Set where
  constructor reach
  field
    ext   : St ≤ₛ St'
    bound : ≤ₛ-grade ext ≾ᵣ ρ

open _⊑ₛ[_]_ public

-- The bound in the form `suc-comp-ren` consumes, with the residual spent.

reach-bound : ∀ {St St' ρ} → (q : St ⊑ₛ[ ρ ] St')
            → ≤ₛ-grade (ext q) ·ᵣ uᵣ ≾ᵣ ρ
reach-bound q = ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityʳ _)) (bound q)

-- The witness an `unbox` needs: enough time has passed for a `ρ`-boxed value
-- to be ready at `St'`. This is the shape of `UNBOX`'s premise, hence what
-- `unbox-lookup` consumes.

unbox-ren : ∀ {St ρ St'} → St ⊑ₛ[ ρ ] St' → Ren [] (toCtx St') (toCtx St ⟨ ρ ⟩)
unbox-ren q = suc-comp-ren (ext q) (reach-bound q) ∘ʳ ⟨⟩-η-ren

-- At the unit budget it is a plain renaming `toCtx St → toCtx St'`: `unbox-ren`
-- with the source lock unwound. So each of its laws is the corresponding
-- `unbox-ren` law conjugated by `⟨⟩-η⁻¹-ren`.

reach-renᵘ : ∀ {St St'} → St ⊑ₛ[ uᵣ ] St' → Ren [] (toCtx St') (toCtx St)
reach-renᵘ q = ⟨⟩-η⁻¹-ren ∘ʳ suc-comp-ren (ext q) (reach-bound q) ∘ʳ ⟨⟩-η-ren

reach-renᵘ-unbox : ∀ {St St' : 𝕊 []} → (q : St ⊑ₛ[ uᵣ ] St')
                 → reach-renᵘ q ≐ʳ (⟨⟩-η⁻¹-ren ∘ʳ unbox-ren q)
reach-renᵘ-unbox q = ≐ʳ-refl

reach-val : ∀ {St St' A} → St ⊑ₛ[ uᵣ ] St' → toCtx St ⊢V⦂ A → toCtx St' ⊢V⦂ A
reach-val q = V-rename (reach-renᵘ q)

-- Transporting a term with one more variable on top (a `lam` body).

reach-under : ∀ {St St' A C} → St ⊑ₛ[ uᵣ ] St'
            → toCtx St ∷ A ⊢C⦂ C → toCtx St' ∷ A ⊢C⦂ C
reach-under q = C-rename (cong-∷-ren (reach-renᵘ q))

-- Resuming a continuation guarded by `ρ` at a state where `ρ` has elapsed:
-- cross the lock along the reach, then feed it the arity value. The reach is the
-- one `unbox` consumes, because that is how a resumption is reached — `HANDLE-OP`
-- boxes it at `ρ` and the clause unboxes it once `ρ` has passed.

resume : ∀ {St St' ρ A ε B}
       → (q : St ⊑ₛ[ ρ ] St')
       → toCtx St ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε
       → toCtx St' ⊢V⦂ B
       → toCtx St' ⊢C⦂ A ‼ ε
resume q M W = (C-rename (cong-∷-ren (unbox-ren q)) M) [ split-[] ↦ W ]c

-- Two general facts about `_≤ₛ_` that `OperationalSemantics.State` does not
-- carry: extensions compose, and their accumulated grades multiply.

≤ₛ-trans : ∀ {Γ Γ' Γ''} → {St : 𝕊 Γ} → {St' : 𝕊 Γ'} → {St'' : 𝕊 Γ''}
         → St ≤ₛ St' → St' ≤ₛ St''
         -------------------------
         → St ≤ₛ St''

≤ₛ-trans q id-suc        = q
≤ₛ-trans q (⟨⟩-suc ρ q') = ⟨⟩-suc ρ (≤ₛ-trans q q')
≤ₛ-trans q (∷-suc V q')  = ∷-suc V (≤ₛ-trans q q')

≤ₛ-grade-trans : ∀ {Γ Γ' Γ''} → {St : 𝕊 Γ} → {St' : 𝕊 Γ'} → {St'' : 𝕊 Γ''}
               → (q : St ≤ₛ St') → (q' : St' ≤ₛ St'')
               ---------------------------------------------------------
               → ≤ₛ-grade (≤ₛ-trans q q') ≡ ≤ₛ-grade q ·ᵣ ≤ₛ-grade q'

≤ₛ-grade-trans q id-suc        =
  sym (·ᵣ-identityʳ (≤ₛ-grade q))
≤ₛ-grade-trans q (⟨⟩-suc ρ q') =
  trans (cong (_·ᵣ ρ) (≤ₛ-grade-trans q q')) (·ᵣ-assoc _ _ ρ)
≤ₛ-grade-trans q (∷-suc V q')  =
  ≤ₛ-grade-trans q q'

reach-≤ : ∀ {St St' ρ ρ₀} → St ⊑ₛ[ ρ ] St' → ρ ≾ᵣ ρ₀ → St ⊑ₛ[ ρ₀ ] St'
reach-≤ (reach e b) p = reach e (≾ᵣ-trans b p)

reach-id : ∀ {St} → St ⊑ₛ[ uᵣ ] St
reach-id = reach id-suc ≾ᵣ-refl

reach-∘ᵍ : ∀ {St St' St'' ρ ρ'}
         → St' ⊑ₛ[ ρ' ] St'' → St ⊑ₛ[ ρ ] St'
         --------------------------------------
         → St ⊑ₛ[ ρ ·ᵣ ρ' ] St''

reach-∘ᵍ (reach e' b') (reach e b) =
  reach (≤ₛ-trans e e')
    (≾ᵣ-trans (≾ᵣ-reflexive (≤ₛ-grade-trans e e'))
              (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ b) (·ᵣ-monoʳ-≾ᵣ b')))

-- The two shapes the development uses: a unit reach appended to a guarded one,
-- and a guarded reach appended to a unit one. Both are the graded law at a
-- product a unit law collapses.

reach-∘ : ∀ {St St' St'' ρ} → St' ⊑ₛ[ uᵣ ] St'' → St ⊑ₛ[ ρ ] St'
        → St ⊑ₛ[ ρ ] St''
reach-∘ {ρ = ρ} q' q = reach-≤ (reach-∘ᵍ q' q) (≾ᵣ-reflexive (·ᵣ-identityʳ ρ))

-- Allocating a cell accumulates nothing (`BOX`); letting time pass costs
-- exactly the lock it passes (`DELAY`).

alloc-reach : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            ------------------------------------------------------------
            → St ⊑ₛ[ uᵣ ] (St ∷ₛ V)

alloc-reach V = reach (∷-suc V id-suc) ≾ᵣ-refl

delay-reach : ∀ {ρ} {St : 𝕊 []}
            ----------------------------
            → St ⊑ₛ[ ρ ] (St ⟨ ρ ⟩ₛ)

delay-reach {ρ} = reach (⟨⟩-suc ρ id-suc) (≾ᵣ-reflexive (·ᵣ-identityˡ ρ))

-- Extending twice is extending once along the composite.

-- The grade bound is invisible: it only ever reaches a `⟨⟩-≤-ren`.

suc-comp-ren-irr : ∀ {St St₁ : 𝕊 []} {ρ₀ ρ₁ : R} → (e : St ≤ₛ St₁)
                 → (b b' : ≤ₛ-grade e ·ᵣ ρ₁ ≾ᵣ ρ₀)
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

suc-comp-ren-≤ : ∀ {St St₁ : 𝕊 []} {ρ₀ ρ₁ ρ₂ : R} → (e : St ≤ₛ St₁)
               → (b  : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ₀)
               → (b₁ : ≤ₛ-grade e ·ᵣ ρ₁ ≾ᵣ ρ₀)
               → (p  : ρ₂ ≾ᵣ ρ₁)
               → suc-comp-ren e b ≐ʳ (suc-comp-ren e b₁ ∘ʳ ⟨⟩-≤-ren p)

suc-comp-ren-≤ id-suc b b₁ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

suc-comp-ren-≤ (⟨⟩-suc ρ q) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ q _ _ (·ᵣ-monoʳ-≾ᵣ p)) ≐ʳ-refl)
    (≐ʳ-trans (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) (⟨⟩-≤-ren (·ᵣ-monoʳ-≾ᵣ p))
                          ⟨⟩-μ-ren)
      (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (⟨⟩-μ-≤-comm p (·ᵣ-monoʳ-≾ᵣ p)))
                (≐ʳ-sym (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) ⟨⟩-μ-ren (⟨⟩-≤-ren p)))))

suc-comp-ren-≤ (∷-suc V q) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ q _ _ p) ≐ʳ-refl)
    (≐ʳ-trans (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) (⟨⟩-≤-ren p)
                          (cong-⟨⟩-ren wk-ren))
      (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (wk-≤-comm p))
                (≐ʳ-sym (∘ʳ-assoc-≐ʳ (suc-comp-ren q _) (cong-⟨⟩-ren wk-ren)
                                    (⟨⟩-≤-ren p)))))

-- Relaxing the *source* grade is pre-composing with a relaxation (the mirror of
-- `suc-comp-ren-≤`, which relaxes the residual one).

suc-comp-ren-≤ˡ : ∀ {St St₁ : 𝕊 []} {ρ₀ ρ₁ ρ₂ : R} → (e : St ≤ₛ St₁)
                → (b  : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ₀)
                → (b₁ : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ₁)
                → (p  : ρ₁ ≾ᵣ ρ₀)
                → suc-comp-ren e b ≐ʳ (⟨⟩-≤-ren p ∘ʳ suc-comp-ren e b₁)

suc-comp-ren-≤ˡ id-suc b b₁ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

suc-comp-ren-≤ˡ (⟨⟩-suc ρ e) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ˡ e _ _ p) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren p) (suc-comp-ren e _) ⟨⟩-μ-ren)

suc-comp-ren-≤ˡ (∷-suc V e) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≤ˡ e _ _ p) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren p) (suc-comp-ren e _)
                       (cong-⟨⟩-ren wk-ren))

-- Extending twice is extending once along the composite.

suc-comp-ren-∘-≐ʳ : ∀ {St St₁ St₂ : 𝕊 []} {ρ₀ ρ₁ ρ₂ : R}
                 → (e : St ≤ₛ St₁) → (e' : St₁ ≤ₛ St₂)
                 → (b  : ≤ₛ-grade (≤ₛ-trans e e') ·ᵣ ρ₂ ≾ᵣ ρ₀)
                 → (b₁ : ≤ₛ-grade e  ·ᵣ ρ₁ ≾ᵣ ρ₀)
                 → (b₂ : ≤ₛ-grade e' ·ᵣ ρ₂ ≾ᵣ ρ₁)
                 ------------------------------------------------------
                 → suc-comp-ren (≤ₛ-trans e e') b
                 ≐ʳ (suc-comp-ren e b₁ ∘ʳ suc-comp-ren e' b₂)

-- `≤ₛ-trans e id-suc` *is* `e`, so the composite is `e` at a relaxed grade
suc-comp-ren-∘-≐ʳ {ρ₂ = ρ₂} e id-suc b b₁ b₂ =
  suc-comp-ren-≤ e b b₁
    (≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityˡ ρ₂))) b₂)

suc-comp-ren-∘-≐ʳ e (⟨⟩-suc ρ e') b b₁ b₂ =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-∘-≐ʳ e e' _ b₁ _) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (suc-comp-ren e b₁) (suc-comp-ren e' _) ⟨⟩-μ-ren)

suc-comp-ren-∘-≐ʳ e (∷-suc V e') b b₁ b₂ =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-∘-≐ʳ e e' _ b₁ _) ≐ʳ-refl)
           (∘ʳ-assoc-≐ʳ (suc-comp-ren e b₁) (suc-comp-ren e' _)
                       (cong-⟨⟩-ren wk-ren))

-- `suc-comp-ren` sends a locked variable to a locked variable: the extension
-- embeds `toCtx St` into `toCtx St₁`, under the lock.

≤ₛ-embed : ∀ {St St₁ : 𝕊 []} → (e : St ≤ₛ St₁) → ∀ {A σ}
         → A ∈[ σ ] toCtx St → Σ[ σ' ∈ R ] A ∈[ σ' ] toCtx St₁
≤ₛ-embed id-suc        {σ = σ} x = σ , x
≤ₛ-embed (⟨⟩-suc ρ e)  x with ≤ₛ-embed e x
... | σ' , y = σ' ·ᵣ ρ , Tl-⟨⟩ y
≤ₛ-embed (∷-suc V e)   x with ≤ₛ-embed e x
... | σ' , y = σ' , Tl-∷ y

suc-comp-ren-img : ∀ {St St₁ : 𝕊 []} {ρ₂ ρ₃ : R} → (e : St ≤ₛ St₁)
                 → (b : ≤ₛ-grade e ·ᵣ ρ₃ ≾ᵣ ρ₂)
                 → ∀ {A σ} → (x : A ∈[ σ ] toCtx St)
                 → var-img (suc-comp-ren e b) (Tl-⟨⟩ x)
                 ≡ (proj₁ (≤ₛ-embed e x) ·ᵣ ρ₃ , Tl-⟨⟩ (proj₂ (≤ₛ-embed e x)))

suc-comp-ren-img id-suc       b x = refl
suc-comp-ren-img (⟨⟩-suc ρ e) b x =
  cong (var-img′ ⟨⟩-μ-ren) (suc-comp-ren-img e _ x)
suc-comp-ren-img (∷-suc V e)  b x =
  cong (var-img′ (cong-⟨⟩-ren wk-ren)) (suc-comp-ren-img e _ x)

-- The embedding is functorial, and the two `⟨⟩-η` renamings are its identity
-- steps. Together these compute what `reach-renᵘ` and `unbox-ren` do to a
-- variable, which is all the lookup coherences need.

≤ₛ-embed-∘ : ∀ {St St₁ St₂ : 𝕊 []} → (e : St ≤ₛ St₁) → (e' : St₁ ≤ₛ St₂)
           → ∀ {A σ} → (x : A ∈[ σ ] toCtx St)
           → ≤ₛ-embed (≤ₛ-trans e e') x ≡ ≤ₛ-embed e' (proj₂ (≤ₛ-embed e x))
≤ₛ-embed-∘ e id-suc        x = refl
≤ₛ-embed-∘ e (⟨⟩-suc ρ e') x =
  cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (≤ₛ-embed-∘ e e' x)
≤ₛ-embed-∘ e (∷-suc V e')  x =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (≤ₛ-embed-∘ e e' x)

-- What the embedding does to a variable's grade: it accumulates exactly the
-- extension's own grade, the locks passed being the same ones.

≤ₛ-embed-grade : ∀ {St St₁ : 𝕊 []} → (e : St ≤ₛ St₁) → ∀ {A σ}
               → (x : A ∈[ σ ] toCtx St)
               → proj₁ (≤ₛ-embed e x) ≡ σ ·ᵣ ≤ₛ-grade e
≤ₛ-embed-grade id-suc       {σ = σ} x = sym (·ᵣ-identityʳ σ)
≤ₛ-embed-grade (⟨⟩-suc ρ e) {σ = σ} x =
  trans (cong (_·ᵣ ρ) (≤ₛ-embed-grade e x))
        (·ᵣ-assoc σ (≤ₛ-grade e) ρ)
≤ₛ-embed-grade (∷-suc V e)  x = ≤ₛ-embed-grade e x

-- What a reach does to a variable: the embedding of its extension.

reach-renᵘ-img : ∀ {St St' : 𝕊 []} → (q : St ⊑ₛ[ uᵣ ] St')
               → ∀ {A σ} → (x : A ∈[ σ ] toCtx St)
               → var-img (reach-renᵘ q) x ≡ ≤ₛ-embed (ext q) x
reach-renᵘ-img q x =
  trans (cong (λ t → var-img′ ⟨⟩-η-ren
                       (var-img′ (suc-comp-ren (ext q) (reach-bound q)) t))
              (⟨⟩-η⁻¹-img x))
        (cong (var-img′ ⟨⟩-η-ren)
              (suc-comp-ren-img (ext q) (reach-bound q) x))

unbox-ren-img : ∀ {St St' : 𝕊 []} {ρ : R} → (q : St ⊑ₛ[ ρ ] St')
              → ∀ {A σ} → (x : A ∈[ σ ] toCtx St)
              → var-img (unbox-ren q) (Tl-⟨⟩ x) ≡ ≤ₛ-embed (ext q) x
unbox-ren-img q x =
  cong (var-img′ ⟨⟩-η-ren) (suc-comp-ren-img (ext q) (reach-bound q) x)

-- What a whole run accumulates: the closure of `PreservationTheorem`'s
-- per-step facts under composition, packaged as the reach a run licenses.

steps-extends-state : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
                    → cf ↝* cf' → Config.state cf ≤ₛ Config.state cf'

steps-extends-state ε*       = id-suc
steps-extends-state (r ◅ rs) =
  ≤ₛ-trans (step-extends-state r) (steps-extends-state rs)

steps-grade-≾ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
              → (rs : cf ↝* cf')
              → ≤ₛ-grade (steps-extends-state rs) ·ᵣ mapᵉ ε' ≾ᵣ mapᵉ ε

steps-grade-≾ {ε = ε} ε* = ≾ᵣ-reflexive (·ᵣ-identityˡ (mapᵉ ε))
steps-grade-≾ {ε' = ε'} (r ◅ rs) =
  ≾ᵣ-trans
    (≾ᵣ-reflexive
      (trans (cong (_·ᵣ mapᵉ ε')
                   (≤ₛ-grade-trans (step-extends-state r)
                                   (steps-extends-state rs)))
             (·ᵣ-assoc (≤ₛ-grade (step-extends-state r))
                       (≤ₛ-grade (steps-extends-state rs)) (mapᵉ ε'))))
    (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (steps-grade-≾ rs)) (step-grade-≾ r))

-- The renaming a whole run licenses. A run's bound relates two locked contexts,
-- so it goes straight to `suc-comp-ren` rather than through a reach.

steps-ren : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
          → (rs : cf ↝* cf')
          → Ren [] (toCtx (Config.state cf') ⟨ mapᵉ ε' ⟩)
                   (toCtx (Config.state cf)  ⟨ mapᵉ ε  ⟩)
steps-ren rs = suc-comp-ren (steps-extends-state rs) (steps-grade-≾ rs)

-- A step refines the scrutinee's value type, so a congruence rule narrows the
-- continuation's binder. A run stacks those narrowings up; a `subV` spine does
-- not flatten, so the stack is kept as it stands and described by what
-- substituting into it does.

narrow-run : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
           → cf ↝* cf' → ∀ {Γ C} → Γ ∷ A ⊢C⦂ C → Γ ∷ B ⊢C⦂ C
narrow-run ε*       N = N
narrow-run (r ◅ rs) N = narrow-run rs (narrow-∷ (step-refines-type r) N)

spine : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
      → cf ↝* cf' → ∀ {Γ} → Γ ⊢V⦂ B → Γ ⊢V⦂ A
spine ε*       V = V
spine (r ◅ rs) V = subV (spine rs V) (step-refines-type r)

-- Substituting into a narrowed binder subsumes the value first.

narrow-∷-sub : ∀ {Γ A A₀ C} → (w : A₀ <:ᵛ A) → (N : Γ ∷ A ⊢C⦂ C)
             → (V : Γ ⊢V⦂ A₀)
             ------------------------------------------------------------
             → narrow-∷ w N [ split-[] ↦ V ]c ≡ N [ split-[] ↦ subV V w ]c

narrow-∷-sub {A = A} w N V =
  trans (sub-swap-≡ᶜ V (subV (var (λ _ → ≾ᵣ-refl) Hd) w)
                     (C-rename (cong-∷-ren wk-ren) N))
        (cong (C-sub₀ (val-sub (subV V w))) (sub-wk-≡ᶜ ([] ∷ A) V N))

-- A narrowing only touches the top binder, so a renaming of the rest passes it.

narrow-∷-ren : ∀ {Γ Δ A A₀ C} → (r : Ren [] Δ Γ) → (w : A₀ <:ᵛ A)
             → (N : Γ ∷ A ⊢C⦂ C)
             --------------------------------------------------
             → C-rename (cong-∷-ren r) (narrow-∷ w N)
             ≡ narrow-∷ w (C-rename (cong-∷-ren r) N)

narrow-∷-ren r w N =
  trans (sym (ren-sub-≡ᶜ [] (cong-∷-ren r)
                         (subV (var (λ _ → ≾ᵣ-refl) Hd) w)
                         (C-rename (cong-∷-ren wk-ren) N)))
        (cong₂ (λ U X → C-sub₀ (val-sub U) X) (subV-≡ var-≡) renM)
  where
    renM : C-rename (cong-∷-ren (cong-∷-ren r))
             (C-rename (cong-∷-ren wk-ren) N)
         ≡ C-rename (cong-∷-ren wk-ren) (C-rename (cong-∷-ren r) N)
    renM =
      trans (sym (C-rename-∘ (cong-∷-ren wk-ren)
                             (cong-∷-ren (cong-∷-ren r)) N))
        (trans
          (C-rename-≡
            (≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ʳ wk-ren (cong-∷-ren r)))
              (≐ʳ-trans (cong-∷-ren-≐ʳ (wk-ren-nat-≐ʳ r))
                        (cong-∷-ren-∘-≐ʳ r wk-ren)))
            N)
          (C-rename-∘ (cong-∷-ren r) (cong-∷-ren wk-ren) N))

-- A narrowing is stable under a context equality, the binder it narrows being
-- the one the equality leaves alone.

cast-narrow-∷ : ∀ {Γ Γ' A A₀ C} → (f : Ctx → Ctx) → (e : Γ' ≡ Γ)
              → (w : A₀ <:ᵛ A) → (N : f Γ' ∷ A ⊢C⦂ C)
              ------------------------------------------------------
              → narrow-∷ w (castᶜ (cong (λ Γ₀ → f Γ₀ ∷ A) e) N)
              ≡ castᶜ (cong (λ Γ₀ → f Γ₀ ∷ A₀) e) (narrow-∷ w N)

cast-narrow-∷ f refl w N = refl

-- Both laws, iterated along a run.

narrow-run-sub : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
               → (rs : cf ↝* cf') → ∀ {Γ C} → (N : Γ ∷ A ⊢C⦂ C) → (V : Γ ⊢V⦂ B)
               ---------------------------------------------------------------
               → narrow-run rs N [ split-[] ↦ V ]c
               ≡ N [ split-[] ↦ spine rs V ]c

narrow-run-sub ε*       N V = refl
narrow-run-sub (r ◅ rs) N V =
  trans (narrow-run-sub rs (narrow-∷ (step-refines-type r) N) V)
        (narrow-∷-sub (step-refines-type r) N (spine rs V))

narrow-run-ren : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
               → (rs : cf ↝* cf') → ∀ {Γ Δ C} → (r : Ren [] Δ Γ)
               → (N : Γ ∷ A ⊢C⦂ C)
               -----------------------------------------------
               → C-rename (cong-∷-ren r) (narrow-run rs N)
               ≡ narrow-run rs (C-rename (cong-∷-ren r) N)

narrow-run-ren ε*        r N = refl
narrow-run-ren (r₀ ◅ rs) r N =
  trans (narrow-run-ren rs r (narrow-∷ (step-refines-type r₀) N))
        (cong (narrow-run rs) (narrow-∷-ren r (step-refines-type r₀) N))

-- Both congruence rules retype the continuation along `suc-comp-ren` of the
-- step's own extension, and narrow its binder to the refined value type.

seq-steps : ∀ {A A₁ B ε ε' ε₂} {St St₁ : 𝕊 []}
          → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₁ : toCtx St₁ ⊢C⦂ A₁ ‼ ε'}
          → (rs : ⟨ St , M ⟩ ↝* ⟨ St₁ , M₁ ⟩)
          → (N : toCtx St ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
          -----------------------------------------------------------------
          → Σ[ N₁ ∈ (toCtx St₁ ⟨ mapᵉ ε' ⟩ ∷ A₁ ⊢C⦂ B ‼ ε₂) ]
              (⟨ St , M ⨟ N ⟩ ↝* ⟨ St₁ , M₁ ⨟ N₁ ⟩)
            × (N₁ ≡ narrow-run rs (C-rename (cong-∷-ren (steps-ren rs)) N))

seq-steps ε* N =
  N , ε* , sym (C-rename-id-≡ (cong-∷-ren-id-≐ʳ (⟨⟩-≤-ren-id-≐ʳ _)) N)

seq-steps (r ◅ rs) N
  with seq-steps rs
         (narrow-∷ (step-refines-type r)
           (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                               (step-grade-≾ r))) N))
... | N₁ , rs' , eN₁ =
    N₁
  , SEQ-STEP r (step-grade-≾ r) ◅ rs'
  , trans eN₁
      (cong (narrow-run rs)
        (trans
          (narrow-∷-ren (steps-ren rs) (step-refines-type r)
            (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                (step-grade-≾ r))) N))
          (cong (narrow-∷ (step-refines-type r))
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

steps-barrier-ren : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
                  → (rs : cf ↝* cf')
                  → Ren [] (toCtx (Config.state cf') ⟨ ⊤ᵣ ⟩)
                           (toCtx (Config.state cf)  ⟨ ⊤ᵣ ⟩)
steps-barrier-ren rs = suc-comp-ren (steps-extends-state rs) (≾-⊤ᵣ _)

handle-steps : ∀ {A A₁ B ε ε' ε₂} {St St₁ : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₁ : toCtx St₁ ⊢C⦂ A₁ ‼ ε'}
             → (rs : ⟨ St , M ⟩ ↝* ⟨ St₁ , M₁ ⟩)
             → (H : (op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St ⟨ ⊤ᵣ ⟩))
             → (N : toCtx St ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
             ---------------------------------------------------------------
             → Σ[ H₁ ∈ ((op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St₁ ⟨ ⊤ᵣ ⟩)) ]
               Σ[ N₁ ∈ (toCtx St₁ ⟨ mapᵉ ε' ⟩ ∷ A₁ ⊢C⦂ B ‼ ε₂) ]
                 (⟨ St , handle M `with H `in N ⟩ ↝*
                  ⟨ St₁ , handle M₁ `with H₁ `in N₁ ⟩)
               × (∀ op ε₃ → H₁ op ε₃
                    ≡ C-rename (cong-∷-ren (cong-∷-ren (steps-barrier-ren rs)))
                               (H op ε₃))
               × (N₁ ≡ narrow-run rs (C-rename (cong-∷-ren (steps-ren rs)) N))

handle-steps {B = B} {St = St} ε* H N =
    H , N , ε*
  , (λ op ε₃ →
       sym (C-rename-id-≡
              (cong-∷-ren-id-≐ʳ (cong-∷-ren-id-≐ʳ (⟨⟩-≤-ren-id-≐ʳ _)))
              (H op ε₃)))
  , sym (C-rename-id-≡ (cong-∷-ren-id-≐ʳ (⟨⟩-≤-ren-id-≐ʳ _)) N)

handle-steps {B = B} {St = St} {St₁ = St₁} (_◅_ {cf₂ = ⟨ St' , M' ⟩} r rs) H N
  with handle-steps rs
         (λ op ε₃ →
            C-rename (cong-∷-ren (cong-∷-ren
                       (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _))))
              (H op ε₃))
         (narrow-∷ (step-refines-type r)
           (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                               (step-grade-≾ r))) N))
... | H₁ , N₁ , rs' , eH₁ , eN₁ =
    H₁ , N₁
  , HANDLE-STEP r (step-grade-≾ r) ◅ rs'
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
      (cong (narrow-run rs)
        (trans
          (narrow-∷-ren (steps-ren rs) (step-refines-type r)
            (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                (step-grade-≾ r))) N))
          (cong (narrow-∷ (step-refines-type r))
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
-- what reconciles a run's `mapᵉ uₑ` with the `uᵣ` a graded reach wants.

suc-comp-ren-grade : ∀ {St St₁ : 𝕊 []} {ρ'' ρ₁ ρ₂ : R} → (e : St ≤ₛ St₁)
                   → (eg : ρ₁ ≡ ρ₂)
                   → (b₁ : ≤ₛ-grade e ·ᵣ ρ₁ ≾ᵣ ρ'')
                   → (b₂ : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ'')
                   → (suc-comp-ren e b₁ ∘ʳ eq-ren (cong (toCtx St₁ ⟨_⟩) eg))
                   ≐ʳ suc-comp-ren e b₂
suc-comp-ren-grade e refl b₁ b₂ =
  ≐ʳ-trans (∘ʳ-identityʳ-≐ʳ (suc-comp-ren e b₁)) (suc-comp-ren-irr e b₁ b₂)

-- The same on the *source* side: an extension started at a propositionally
-- equal guard is the same renaming, `eq-ren` being the identity there.

suc-comp-ren-grade-src : ∀ {St St₁ : 𝕊 []} {ρ₁ ρ₂ ρ₃ : R} → (e : St ≤ₛ St₁)
                       → (eg : ρ₁ ≡ ρ₂)
                       → (b₁ : ≤ₛ-grade e ·ᵣ ρ₃ ≾ᵣ ρ₂)
                       → (b₂ : ≤ₛ-grade e ·ᵣ ρ₃ ≾ᵣ ρ₁)
                       → (eq-ren (cong (toCtx St ⟨_⟩) eg) ∘ʳ suc-comp-ren e b₁)
                       ≐ʳ suc-comp-ren e b₂
suc-comp-ren-grade-src e refl b₁ b₂ =
  ≐ʳ-trans (∘ʳ-identityˡ-≐ʳ (suc-comp-ren e b₁)) (suc-comp-ren-irr e b₁ b₂)

-- Crossing a lock and then moving on is crossing it into the later state: both
-- send `Tl-⟨⟩ x` to the composite extension's embedding.

reach-unbox-ren-≐ʳ : ∀ {ρ} {St St' St'' : 𝕊 []}
                  → (q' : St' ⊑ₛ[ uᵣ ] St'') → (q : St ⊑ₛ[ ρ ] St')
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

reach-renᵘ-∘ : ∀ {St St' St'' : 𝕊 []}
             → (q' : St' ⊑ₛ[ uᵣ ] St'') → (q : St ⊑ₛ[ uᵣ ] St')
             → reach-renᵘ (reach-∘ q' q) ≐ʳ (reach-renᵘ q ∘ʳ reach-renᵘ q')
reach-renᵘ-∘ q' q =
  ≐ʳ-trans (reach-renᵘ-unbox (reach-∘ q' q))
    (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (≐ʳ-sym (reach-unbox-ren-≐ʳ q' q)))
      (≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ʳ ⟨⟩-η⁻¹-ren (unbox-ren q) (reach-renᵘ q')))
                (∘ʳ-≐ʳ (≐ʳ-sym (reach-renᵘ-unbox q)) ≐ʳ-refl)))

-- Allocating a cell renames the old context by weakening past it.

alloc-ren-≐ʳ : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → reach-renᵘ (alloc-reach V) ≐ʳ wk-ren
alloc-ren-≐ʳ V = mk≐ʳ (λ x → reach-renᵘ-img (alloc-reach V) x)

-- The same for the renaming an `unbox` consumes: splitting the guard into the
-- reach's own part and a residual `σ`, then crossing the lock under `σ`, is the
-- extension at residual `σ`.

unbox-ren-μ-≐ʳ : ∀ {St St₁ : 𝕊 []} {ρ σ : R} → (q : St ⊑ₛ[ ρ ] St₁)
              → (b : ≤ₛ-grade (ext q) ·ᵣ σ ≾ᵣ ρ ·ᵣ σ)
              → (⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren {ρ = σ} (unbox-ren q))
              ≐ʳ suc-comp-ren (ext q) b
unbox-ren-μ-≐ʳ {σ = σ} q b = mk≐ʳ go
  where
    go : ∀ {A τ} → (x : A ∈[ τ ] _) → _
    go (Tl-⟨⟩ x) = trans (cong (Var-⟨⟩ σ) (unbox-ren-img q x))
                         (sym (suc-comp-ren-img (ext q) b x))

-- Entering the barrier and then following an extension is the reach at budget
-- `⊤ᵣ`: the residual grade is relaxed from `uᵣ` to `⊤ᵣ` (`suc-comp-ren-≤`).

barrier-unbox-≐ʳ : ∀ {St St₁ : 𝕊 []} → (q : St ⊑ₛ[ ⊤ᵣ ] St₁)
                 → (b : ≤ₛ-grade (ext q) ·ᵣ ⊤ᵣ ≾ᵣ ⊤ᵣ)
                 → (suc-comp-ren (ext q) b ∘ʳ barrier-ren) ≐ʳ unbox-ren q
barrier-unbox-≐ʳ q b =
  ≐ʳ-trans
    (≐ʳ-sym (∘ʳ-assoc-≐ʳ (suc-comp-ren (ext q) b) (⟨⟩-≤-ren (≾-⊤ᵣ uᵣ))
                        ⟨⟩-η-ren))
    (∘ʳ-≐ʳ (≐ʳ-sym (suc-comp-ren-≤ (ext q) (reach-bound q) b (≾-⊤ᵣ uᵣ)))
          ≐ʳ-refl)

-- Crossing a lock and then following a guarded reach is following the same reach
-- at the unit budget (`reach-≤`): the source grade is relaxed from `ρ` to `uᵣ`,
-- which is pre-composition with `⟨⟩-≤-ren` (`suc-comp-ren-≤ˡ`).

unbox-ren-unit : ∀ {ρ} {St St' : 𝕊 []} → (q : St ⊑ₛ[ ρ ] St') → (p : ρ ≾ᵣ uᵣ)
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
-- the reach a `DELAY` takes (whose target context *is* the source under the
-- lock). Both are needed to recognise a reduct as the action of an environment.

-- Both are `≤ₛ-embed` of the identity extension, which is the identity: a
-- variable of a state context cannot be case-split on, so this goes through the
-- `var-img` layer rather than pointwise.

reach-renᵘ-id-≐ʳ : ∀ {St : 𝕊 []} → reach-renᵘ (reach-id {St}) ≐ʳ id-ren
reach-renᵘ-id-≐ʳ = mk≐ʳ (λ x → reach-renᵘ-img reach-id x)

unbox-ren-delay-≐ʳ : ∀ {ρ} {St : 𝕊 []}
                  → unbox-ren (delay-reach {ρ} {St}) ≐ʳ id-ren
unbox-ren-delay-≐ʳ = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = unbox-ren-img delay-reach x

-- The lookup's renaming composite depends on the state only through two
-- contexts, the stored value, and three proofs.

lookup-ren′ : ∀ {A ρ σ} {Γ : Ctx} → (Γf Γs : Ctx)
            → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
            → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≡ σ)
            → (rel : σ ≾ᵣ ρ)
            → Ren [] Γ (([] ++ᶜ Γf) ⟨ ρ ⟩)
lookup-ren′ {A} {ρ} Γf Γs eq h rel =
  (((  eq-ren ++ᶜ-identityˡ
   ∘ʳ ⟨⟩-≤-ren rel)
   ∘ʳ wk-ren-⟨ρ⟩-ctx h)
   ∘ʳ eq-ren (sym (++ᶜ-assoc Γf ([] ∷ [ ρ ] A) Γs)))
   ∘ʳ eq-ren eq

lookup-body′ : ∀ {A ρ σ} {Γ : Ctx} → (Γf Γs : Ctx)
             → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
             → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≡ σ)
             → (rel : σ ≾ᵣ ρ)
             → ([] ++ᶜ Γf) ⟨ ρ ⟩ ⊢V⦂ A
             → Γ ⊢V⦂ A
lookup-body′ Γf Γs eq h rel U = V-rename (lookup-ren′ Γf Γs eq h rel) U

lookup-body : ∀ {A ρ} → (St : 𝕊 []) → (t : Var (toCtx St) ([ ρ ] A))
            → proj₁ t ≾ᵣ ρ → toCtx St ⊢V⦂ A
lookup-body {A} {ρ} St (ρ' , z) rel =
  lookup-body′
    (toCtx (split-state-fst St z)) (toCtx (split-state-snd St z))
    (split-state-++ᶜ St z)
    (trans
      (trans
        (trans
          (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd St z)))
          (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd St z)))))
        (sym (grades-≡ (split-state-snd St z))))
      (snd-split-time≡time-from-head St z))
    rel
    (resource-lookup St z)

-- Two lookups at corresponding data agree: match the context equalities, and
-- everything else is proof-irrelevant.

lookup-body′-≡ : ∀ {A ρ σ} {Γ Γ' : Ctx} → (eΓ : Γ' ≡ Γ)
               → {Γf Γf' Γs Γs' : Ctx} → (eF : Γf' ≡ Γf) → (eS : Γs' ≡ Γs)
               → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
               → (eq' : (Γf' ∷ [ ρ ] A) ++ᶜ Γs' ≡ Γ')
               → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≡ σ)
               → (h' : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs') ≡ σ)
               → (rel rel' : σ ≾ᵣ ρ)
               → (U : ([] ++ᶜ Γf) ⟨ ρ ⟩ ⊢V⦂ A)
               → (U' : ([] ++ᶜ Γf') ⟨ ρ ⟩ ⊢V⦂ A)
               → U ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) eF) U'
               → lookup-body′ Γf Γs eq h rel U
               ≡ castᵛ eΓ (lookup-body′ Γf' Γs' eq' h' rel' U')
lookup-body′-≡ refl refl refl eq eq' h h' rel rel' U U' eU
  rewrite uip {p = eq} {q = eq'} | uip {p = h} {q = h'}
        | ≾ᵣ-irrelevant rel rel' = V-rename-cong _ eU

-- Same cell, same value: the bound is `≾ᵣ`-irrelevant.

lookup-body-≡ : ∀ {A ρ} → (St : 𝕊 [])
              → {t t' : Var (toCtx St) ([ ρ ] A)} → t ≡ t'
              → (rel : proj₁ t ≾ᵣ ρ) → (rel' : proj₁ t' ≾ᵣ ρ)
              → lookup-body St t rel ≡ lookup-body St t' rel'
lookup-body-≡ St refl rel rel' =
  cong (lookup-body St _) (≾ᵣ-irrelevant rel rel')


-- An already-allocated cell is split off at the same state, and holds the
-- same value, however far the state has grown since.

≤ₛ-embed-fst : ∀ {St St₁ : 𝕊 []} → (e : St ≤ₛ St₁) → ∀ {A ρ σ}
             → (x : [ ρ ] A ∈[ σ ] toCtx St)
             → split-state-fst St₁ (proj₂ (≤ₛ-embed e x))
             ≡ split-state-fst St x

≤ₛ-embed-fst id-suc       x = refl
≤ₛ-embed-fst (⟨⟩-suc ρ e) x = ≤ₛ-embed-fst e x
≤ₛ-embed-fst (∷-suc V e)  x = ≤ₛ-embed-fst e x

≤ₛ-embed-lookup : ∀ {St St₁ : 𝕊 []} → (e : St ≤ₛ St₁) → ∀ {A ρ σ}
                → (x : [ ρ ] A ∈[ σ ] toCtx St)
                → resource-lookup St₁ (proj₂ (≤ₛ-embed e x))
                ≡ subst (λ S → ([] ++ᶜ toCtx S) ⟨ ρ ⟩ ⊢V⦂ A)
                        (sym (≤ₛ-embed-fst e x))
                        (resource-lookup St x)

≤ₛ-embed-lookup id-suc       x = refl
≤ₛ-embed-lookup (⟨⟩-suc ρ e) x = ≤ₛ-embed-lookup e x
≤ₛ-embed-lookup (∷-suc V e)  x = ≤ₛ-embed-lookup e x

-- `SRed-fresh` compares the lookup at a later state with the value that was
-- stored: the part after the cell grows by exactly the context the extension
-- adds.

≤ₛ-ctx : {St₀ St₂ : 𝕊 []} → St₀ ≤ₛ St₂ → Ctx
≤ₛ-ctx id-suc                  = []
≤ₛ-ctx (⟨⟩-suc ρ e)            = ≤ₛ-ctx e ⟨ ρ ⟩
≤ₛ-ctx (∷-suc {ρ = ρ} {A = A} V e) = ≤ₛ-ctx e ∷ [ ρ ] A

≤ₛ-embed-snd-ctx : ∀ {A ρ σ} {St₀ St₂ : 𝕊 []} → (e : St₀ ≤ₛ St₂)
                 → (c : [ ρ ] A ∈[ σ ] toCtx St₀)
                 → toCtx (split-state-snd St₂ (proj₂ (≤ₛ-embed e c)))
                 ≡ toCtx (split-state-snd St₀ c) ++ᶜ ≤ₛ-ctx e

≤ₛ-embed-snd-ctx id-suc       c = refl
≤ₛ-embed-snd-ctx (⟨⟩-suc ρ e) c = cong (_⟨ ρ ⟩) (≤ₛ-embed-snd-ctx e c)
≤ₛ-embed-snd-ctx (∷-suc V e)  c = cong (_∷ _) (≤ₛ-embed-snd-ctx e c)

-- And the state itself grows the same way.

≤ₛ-ctx-toCtx : {St₀ St₂ : 𝕊 []} → (e : St₀ ≤ₛ St₂)
             → toCtx St₂ ≡ toCtx St₀ ++ᶜ ≤ₛ-ctx e
≤ₛ-ctx-toCtx id-suc       = refl
≤ₛ-ctx-toCtx (⟨⟩-suc ρ e) = cong (_⟨ ρ ⟩) (≤ₛ-ctx-toCtx e)
≤ₛ-ctx-toCtx (∷-suc V e)  = cong (_∷ _) (≤ₛ-ctx-toCtx e)

-- So an extension's embedding *is* the push under the context it adds.

≤ₛ-embed-push : ∀ {A ρ} {St₀ St₂ : 𝕊 []} → (e : St₀ ≤ₛ St₂)
              → (y : A ∈[ ρ ] toCtx St₀)
              → ≤ₛ-embed e y
              ≡ Var-cast (sym (≤ₛ-ctx-toCtx e))
                  (grade-++ᶜˡ ρ (≤ₛ-ctx e) , ∈-++ᶜˡ (≤ₛ-ctx e) y)

≤ₛ-embed-push id-suc       y = refl
≤ₛ-embed-push (⟨⟩-suc ρ e) y =
  trans (cong (Var-⟨⟩ ρ) (≤ₛ-embed-push e y))
    (trans (sym (Var-cast-⟨⟩ ρ (sym (≤ₛ-ctx-toCtx e)) _))
           (Var-cast-irr (cong (_⟨ ρ ⟩) (sym (≤ₛ-ctx-toCtx e)))
                         (sym (≤ₛ-ctx-toCtx (⟨⟩-suc ρ e))) _))
≤ₛ-embed-push (∷-suc V e)  y =
  trans (cong Var-∷ (≤ₛ-embed-push e y))
    (trans (sym (Var-cast-∷ (sym (≤ₛ-ctx-toCtx e)) _))
           (Var-cast-irr (cong (_∷ _) (sym (≤ₛ-ctx-toCtx e)))
                         (sym (≤ₛ-ctx-toCtx (∷-suc V e))) _))

-- Looking up, at whatever state the run has reached, the cell `BOX` just
-- allocated returns the value that was stored — renamed.

-- Transporting a stored value along an equality of the states it was split off
-- at is transporting it along the contexts.

subst-state-castᵛ : ∀ {A ρ} {St St' : 𝕊 []} → (p : St ≡ St')
                   → (U : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
                   → subst (λ S → ([] ++ᶜ toCtx S ⟨ ρ ⟩) ⊢V⦂ A) p U
                   ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) (cong toCtx p)) U
subst-state-castᵛ refl U = refl

alloc-lookup-ren : ∀ {A ρ σ} {St St' : 𝕊 []}
                 → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
                 → (e : (St ∷ₛ V) ≤ₛ St')
                 → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ ≤ₛ-ctx e) ≡ σ)
                 → (rel : σ ≾ᵣ ρ)
                 → (q₀ : St ⊑ₛ[ ρ ] St')
                 → ext q₀ ≡ ≤ₛ-trans (∷-suc V id-suc) e
                 → (lookup-ren′ (toCtx St) (≤ₛ-ctx e) refl h rel
                     ∘ʳ eq-ren (sym (≤ₛ-ctx-toCtx e)))
                 ≐ʳ (eq-ren (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}) ∘ʳ unbox-ren q₀)

alloc-lookup-ren {A} {ρ} {σ} {St} {St'} V e h rel q₀ eq₀ = mk≐ʳ go
  where
    Δ  = ≤ₛ-ctx e
    Δ₁ = [] ∷ [ ρ ] A
    eΓ = sym (≤ₛ-ctx-toCtx e)

    assoc = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)

    go : ∀ {A' τ} → (x : A' ∈[ τ ] (([] ++ᶜ toCtx St) ⟨ ρ ⟩)) → _
    go {A'} (Tl-⟨⟩ {ρ' = τ'} w) =
      trans (cong (λ t → f₅ (f₄ (f₃ (f₂ (f₁ t))))) s₀)
        (trans (cong (λ t → f₅ (f₄ (f₃ t)))
                     (wk-ren-⟨ρ⟩-ctx-img (Δ₁ ++ᶜ Δ) h y))
          (trans (cong (λ t → f₅ (f₄ t))
                       (trans (eq-ren-img assoc (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) y))
                              (∈-++ᶜˡ-assoc Δ₁ Δ y)))
            (trans (eq-ren-img eΓ (∈-++ᶜˡ Δ (Tl-∷ y)))
              (sym (trans (cong (var-img′ (unbox-ren q₀)) s₀)
                     (trans (unbox-ren-img q₀ y)
                       (trans (cong (λ z → ≤ₛ-embed z y) eq₀)
                         (trans (≤ₛ-embed-∘ (∷-suc V id-suc) e y)
                                (≤ₛ-embed-push e (Tl-∷ y))))))))))
      where
        y : A' ∈[ τ' ] toCtx St
        y = subst (λ Γ₀ → A' ∈[ τ' ] Γ₀) ++ᶜ-identityˡ w

        f₁ = var-img′ {A = A'} (⟨⟩-≤-ren rel)
        f₂ = var-img′ {A = A'} (wk-ren-⟨ρ⟩-ctx h)
        f₃ = var-img′ {A = A'} (eq-ren assoc)
        f₄ = var-img′ {A = A'} (eq-ren (refl {x = (toCtx St ∷ [ ρ ] A) ++ᶜ Δ}))
        f₅ = var-img′ {A = A'} (eq-ren eΓ)

        s₀ : var-img (eq-ren (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩})) (Tl-⟨⟩ w)
           ≡ (τ' ·ᵣ ρ , Tl-⟨⟩ y)
        s₀ = trans (eq-ren-img (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}) (Tl-⟨⟩ w))
                   (cong (λ z → τ' ·ᵣ ρ , z)
                         (subst-Tl-⟨⟩ (++ᶜ-identityˡ {toCtx St}) w))

-- `lookup-body′-≡` moves the lookup's own data onto the data the allocation
-- presents, via `≤ₛ-embed-fst`, `≤ₛ-embed-snd-ctx`, and `≤ₛ-embed-lookup`.

alloc-lookup-≡ : ∀ {A ρ} {St St' : 𝕊 []}
               → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
               → (e : (St ∷ₛ V) ≤ₛ St')
               → (rel : proj₁ (≤ₛ-embed e (Hd {Γ = toCtx St})) ≾ᵣ ρ)
               → (q₀ : St ⊑ₛ[ ρ ] St')
               → ext q₀ ≡ ≤ₛ-trans (∷-suc V id-suc) e
               → lookup-body St' (≤ₛ-embed e (Hd {Γ = toCtx St})) rel
               ≡ V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q₀) V

alloc-lookup-≡ {A} {ρ} {St} {St'} V e rel q₀ eq₀ =
  trans (lookup-body′-≡ eΓ eF eS _ refl _ h rel rel _ V eU)
    (trans (castᵛ-rename eΓ (lookup-ren′ (toCtx St) Δ refl h rel) V)
              (V-rename-≡ (alloc-lookup-ren V e h rel q₀ eq₀) V))
  where
    Δ  = ≤ₛ-ctx e
    Δ₁ = [] ∷ [ ρ ] A
    eΓ = sym (≤ₛ-ctx-toCtx e)
    eF = cong toCtx (sym (≤ₛ-embed-fst e (Hd {Γ = toCtx St})))
    eS = sym (trans (≤ₛ-embed-snd-ctx e (Hd {Γ = toCtx St})) ++ᶜ-identityˡ)

    h : ctx-grade (Δ₁ ++ᶜ Δ) ≡ proj₁ (≤ₛ-embed e (Hd {Γ = toCtx St}))
    h = trans (trans (ctx-grade-++ᶜ Δ₁ Δ) (·ᵣ-identityˡ (ctx-grade Δ)))
              (trans (sym (grade-++ᶜˡ-uᵣ Δ))
                     (sym (cong proj₁ (≤ₛ-embed-push e (Hd {Γ = toCtx St})))))

    eU : resource-lookup St' (proj₂ (≤ₛ-embed e (Hd {Γ = toCtx St})))
       ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) eF) V
    eU = (trans (≤ₛ-embed-lookup e (Hd {Γ = toCtx St}))
                      (subst-state-castᵛ
                         (sym (≤ₛ-embed-fst e (Hd {Γ = toCtx St}))) V))

-- `St [ c ]⊑ᶜ St'`: an extension under which the cell `c` has ripened —
-- enough grade has accumulated at `c`'s own position for its `ρ`-box to be
-- read.

infix 4 _[_]⊑ᶜ_

record _[_]⊑ᶜ_ {A ρ σ} (St : 𝕊 [])
                (c : [ ρ ] A ∈[ σ ] toCtx St) (St' : 𝕊 []) : Set where
  constructor read
  field
    extᶜ  : St ≤ₛ St'
    ready : proj₁ (≤ₛ-embed extᶜ c) ≾ᵣ ρ

open _[_]⊑ᶜ_ public

-- What reading it yields.

lookupᶜ : ∀ {A ρ σ} {St St' : 𝕊 []} {c : [ ρ ] A ∈[ σ ] toCtx St}
        → St [ c ]⊑ᶜ St' → toCtx St' ⊢V⦂ A
lookupᶜ {c = c} r = lookup-body _ (≤ₛ-embed (extᶜ r) c) (ready r)

