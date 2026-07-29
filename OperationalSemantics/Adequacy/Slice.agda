------------------------------------------------------------------------
-- The index of the logical relation: guarded state extensions.       --
--                                                                    --
-- Reindexing along `S ≤ₛ S'` is not free weakening — `suc-comp-ren`  --
-- takes a grade side-condition. So the relation is Kripke over the   --
-- *slice* that `suc-comp-ren` accepts: an extension together with    --
-- the bound licensing the lock it was guarded by.                    --
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Slice (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

-- A `ρ`-guarded extension: `St'` extends `St`, and the grade it accumulated,
-- composed with the residual lock `ρ'`, stays below the guarding lock `ρ`.
-- This is precisely the data `suc-comp-ren` consumes.

record Slice (St : 𝕊 []) (ρ : R) (St' : 𝕊 []) (ρ' : R) : Set where
  constructor slice
  field
    ext   : St ≤ₛ St'
    bound : ≤ₛ-grade ext ·ᵣ ρ' ≾ᵣ ρ

open Slice public

-- The renaming a slice licenses.

slice-ren : ∀ {St ρ St' ρ'} → Slice St ρ St' ρ' → Ren [] (toCtx St ⟨ ρ ⟩) (toCtx St' ⟨ ρ' ⟩)
slice-ren (slice e b) = suc-comp-ren e b

-- Identity: no extension, nothing accumulated.

slice-id : ∀ {St ρ} → Slice St ρ St ρ
slice-id {ρ = ρ} = slice id-suc (≾ᵣ-reflexive (·ᵣ-identityˡ ρ))

-- A guarded slice whose guard is itself below the unit is a unit slice: the
-- extension is the same, only the bound is relaxed. This is how a value under a
-- lock is moved forward — a *usable* variable's grade bound gives `ρ ≾ᵣ uᵣ` by
-- the grade monoid's zero-product law.

slice-unit : ∀ {St St' ρ} → Slice St ρ St' uᵣ → ρ ≾ᵣ uᵣ → Slice St uᵣ St' uᵣ
slice-unit (slice e b) p = slice e (≾ᵣ-trans b p)

-- At the unit lock the slice is a plain renaming `toCtx St → toCtx St'`.

slice-renᵘ : ∀ {St St'} → Slice St uᵣ St' uᵣ → Ren [] (toCtx St) (toCtx St')
slice-renᵘ q = ⟨⟩-η-ren ∘ʳ slice-ren q ∘ʳ ⟨⟩-η⁻¹-ren

slice-val : ∀ {St St' A} → Slice St uᵣ St' uᵣ → toCtx St ⊢V⦂ A → toCtx St' ⊢V⦂ A
slice-val q = V-rename (slice-renᵘ q)

slice-comp : ∀ {St St' C} → Slice St uᵣ St' uᵣ → toCtx St ⊢C⦂ C → toCtx St' ⊢C⦂ C
slice-comp q = C-rename (slice-renᵘ q)

-- Transporting a term with one more variable on top (a `lam` body).

slice-under : ∀ {St St' A C} → Slice St uᵣ St' uᵣ
            → toCtx St ∷ A ⊢C⦂ C → toCtx St' ∷ A ⊢C⦂ C
slice-under q = C-rename (cong-∷-ren (slice-renᵘ q))

-- The witness an `unbox` needs: enough time has passed for a `ρ`-boxed value
-- to be ready at `St'`. This is the shape of `UNBOX`'s premise, hence what
-- `unbox-lookup` consumes.

unbox-ren : ∀ {St ρ St'} → Slice St ρ St' uᵣ → Ren [] (toCtx St ⟨ ρ ⟩) (toCtx St')
unbox-ren q = ⟨⟩-η-ren ∘ʳ slice-ren q

-- Resuming a continuation guarded by `ρ` at a state where `ρ` has elapsed:
-- cross the lock along the slice, then feed it the arity value. The slice is the
-- one `unbox` consumes, because that is how a resumption is reached — `HANDLE-OP`
-- boxes it at `ρ` and the clause unboxes it once `ρ` has passed.

resume : ∀ {St St' ρ A ε B}
       → (q : Slice St ρ St' uᵣ)
       → toCtx St ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε
       → toCtx St' ⊢V⦂ B
       → toCtx St' ⊢C⦂ A ‼ ε
resume q M W = (C-rename (cong-∷-ren (unbox-ren q)) M) [ Hd ↦ W ]c

-- TRANSITIVITY OF STATE EXTENSION
--
-- Two general facts about `_≤ₛ_` that `OperationalSemantics.State` does not
-- carry: extensions compose, and their accumulated grades multiply. Kept here
-- while the adequacy development is separate.

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

-- THE SLICE IS A CATEGORY
--
-- Composition: the extensions compose and the two bounds chain, the inner one
-- under `_·ᵣ_`'s monotonicity.

slice-∘ : ∀ {St St' St'' ρ ρ' ρ''}
        → Slice St' ρ' St'' ρ'' → Slice St ρ St' ρ'
        -------------------------------------------
        → Slice St ρ St'' ρ''

slice-∘ {ρ'' = ρ''} (slice e' b') (slice e b) =
  slice (≤ₛ-trans e e')
    (≾ᵣ-trans
      (≾ᵣ-reflexive
        (trans (cong (_·ᵣ ρ'') (≤ₛ-grade-trans e e')) (·ᵣ-assoc _ _ ρ'')))
      (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ b') b))

-- Composition against a unit slice on the right: a `ρ`-guarded step out of a
-- later state still starts `ρ`-guarded from the earlier one. `slice-∘` needs
-- its middle grades to agree, so this is a separate lemma; `Val`'s box clause
-- needs it to be monotone.

slice-∘ᵘ : ∀ {St St' St'' ρ}
         → Slice St' ρ St'' uᵣ → Slice St uᵣ St' uᵣ
         -------------------------------------------
         → Slice St ρ St'' uᵣ

slice-∘ᵘ {ρ = ρ} (slice e' b') (slice e b) =
  slice (≤ₛ-trans e e')
    (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityʳ _))
      (≾ᵣ-trans (≾ᵣ-reflexive (≤ₛ-grade-trans e e'))
        (≾ᵣ-trans
          (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityʳ _))) b))
          (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ _))
                    (≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityʳ _))) b')))))

-- THE SLICES THE MACHINE PRODUCES
--
-- A step extends the state at the unit lock whenever the grade it accumulated
-- permits (`step-extends-state`); allocating a cell accumulates nothing
-- (`BOX`); letting time pass is a slice at exactly the lock it passes
-- (`DELAY`).

step-slice : ∀ {A B ε ε'} {St St' : 𝕊 []}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ B ‼ ε'}
           → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
           → ≤ₛ-grade (step-extends-state r) ≾ᵣ uᵣ
           ---------------------------------------
           → Slice St uᵣ St' uᵣ

step-slice r h =
  slice (step-extends-state r)
    (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityʳ (≤ₛ-grade (step-extends-state r)))) h)

alloc-slice : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            ------------------------------------------------------------
            → Slice St uᵣ (St ∷ₛ V) uᵣ

alloc-slice V = slice (∷-suc V id-suc) (≾ᵣ-reflexive (·ᵣ-identityˡ uᵣ))

delay-slice : ∀ {ρ} {St : 𝕊 []}
            ------------------------------
            → Slice St ρ (St ⟨ ρ ⟩ₛ) uᵣ

delay-slice {ρ} =
  slice (⟨⟩-suc ρ id-suc)
    (≾ᵣ-reflexive (trans (·ᵣ-identityʳ (uᵣ ·ᵣ ρ)) (·ᵣ-identityˡ ρ)))

------------------------------------------------------------------------
-- COMPOSING EXTENSIONS
--
-- `Val`'s Kripke clauses compose two transports, and the composite has to be
-- recognised as one: extending twice is extending once along the composite.
-- Everything here is cast-free — both sides are renamings between the same
-- contexts — so it is a statement about `suc-comp-ren` alone.
------------------------------------------------------------------------

-- The grade bound is invisible: it only ever reaches a `⟨⟩-≤-ren`.

suc-comp-ren-irr : ∀ {St St₁ : 𝕊 []} {ρ₀ ρ₁ : R} → (e : St ≤ₛ St₁)
                 → (b b' : ≤ₛ-grade e ·ᵣ ρ₁ ≾ᵣ ρ₀)
                 → suc-comp-ren e b ≐ʳ suc-comp-ren e b'
suc-comp-ren-irr e b b' rewrite ≾ᵣ-irrelevant b b' = ≐ʳ-refl

-- A grade relaxation commutes past the two renamings `suc-comp-ren` inserts.

⟨⟩-μ-≤-comm : ∀ {Γ ρ ρ₁ ρ₂} → (p : ρ₂ ≾ᵣ ρ₁) → (p' : ρ ·ᵣ ρ₂ ≾ᵣ ρ ·ᵣ ρ₁)
            → (⟨⟩-μ-ren {Δ = Γ} {ρ = ρ} {ρ' = ρ₂} ∘ʳ ⟨⟩-≤-ren p')
            ≐ʳ (⟨⟩-≤-ren p ∘ʳ ⟨⟩-μ-ren)
⟨⟩-μ-≤-comm p p' = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

wk-≤-comm : ∀ {Γ A ρ₁ ρ₂} → (p : ρ₂ ≾ᵣ ρ₁)
          → (cong-⟨⟩-ren {Δ = Γ} {ρ = ρ₂} (wk-ren {A = A}) ∘ʳ ⟨⟩-≤-ren p)
          ≐ʳ (⟨⟩-≤-ren p ∘ʳ cong-⟨⟩-ren wk-ren)
wk-≤-comm p = mk≐ʳ go
  where
    go : ∀ {A' σ} → (x : A' ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

-- Changing the residual grade is post-composing with a relaxation.

suc-comp-ren-≤ : ∀ {St St₁ : 𝕊 []} {ρ₀ ρ₁ ρ₂ : R} → (e : St ≤ₛ St₁)
               → (b  : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ₀)
               → (b₁ : ≤ₛ-grade e ·ᵣ ρ₁ ≾ᵣ ρ₀)
               → (p  : ρ₂ ≾ᵣ ρ₁)
               → suc-comp-ren e b ≐ʳ (⟨⟩-≤-ren p ∘ʳ suc-comp-ren e b₁)

suc-comp-ren-≤ id-suc b b₁ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

suc-comp-ren-≤ (⟨⟩-suc ρ q) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (suc-comp-ren-≤ q _ _ (·ᵣ-monoʳ-≾ᵣ p)))
    (≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ ⟨⟩-μ-ren (⟨⟩-≤-ren (·ᵣ-monoʳ-≾ᵣ p))
                                  (suc-comp-ren q _)))
      (≐ʳ-trans (∘ʳ-≐ (⟨⟩-μ-≤-comm p (·ᵣ-monoʳ-≾ᵣ p)) ≐ʳ-refl)
                (∘ʳ-assoc-≐ (⟨⟩-≤-ren p) ⟨⟩-μ-ren (suc-comp-ren q _))))

suc-comp-ren-≤ (∷-suc V q) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (suc-comp-ren-≤ q _ _ p))
    (≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ (cong-⟨⟩-ren wk-ren) (⟨⟩-≤-ren p)
                                  (suc-comp-ren q _)))
      (≐ʳ-trans (∘ʳ-≐ (wk-≤-comm p) ≐ʳ-refl)
                (∘ʳ-assoc-≐ (⟨⟩-≤-ren p) (cong-⟨⟩-ren wk-ren)
                            (suc-comp-ren q _))))

-- Relaxing the *source* grade is pre-composing with a relaxation (the mirror of
-- `suc-comp-ren-≤`, which relaxes the residual one).

suc-comp-ren-≤ˡ : ∀ {St St₁ : 𝕊 []} {ρ₀ ρ₁ ρ₂ : R} → (e : St ≤ₛ St₁)
                → (b  : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ₀)
                → (b₁ : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ₁)
                → (p  : ρ₁ ≾ᵣ ρ₀)
                → suc-comp-ren e b ≐ʳ (suc-comp-ren e b₁ ∘ʳ ⟨⟩-≤-ren p)

suc-comp-ren-≤ˡ id-suc b b₁ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

suc-comp-ren-≤ˡ (⟨⟩-suc ρ e) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (suc-comp-ren-≤ˡ e _ _ p))
           (≐ʳ-sym (∘ʳ-assoc-≐ ⟨⟩-μ-ren (suc-comp-ren e _) (⟨⟩-≤-ren p)))

suc-comp-ren-≤ˡ (∷-suc V e) b b₁ p =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (suc-comp-ren-≤ˡ e _ _ p))
           (≐ʳ-sym (∘ʳ-assoc-≐ (cong-⟨⟩-ren wk-ren) (suc-comp-ren e _)
                               (⟨⟩-≤-ren p)))

-- Extending twice is extending once along the composite.

suc-comp-ren-∘-≐ : ∀ {St St₁ St₂ : 𝕊 []} {ρ₀ ρ₁ ρ₂ : R}
                 → (e : St ≤ₛ St₁) → (e' : St₁ ≤ₛ St₂)
                 → (b  : ≤ₛ-grade (≤ₛ-trans e e') ·ᵣ ρ₂ ≾ᵣ ρ₀)
                 → (b₁ : ≤ₛ-grade e  ·ᵣ ρ₁ ≾ᵣ ρ₀)
                 → (b₂ : ≤ₛ-grade e' ·ᵣ ρ₂ ≾ᵣ ρ₁)
                 ------------------------------------------------------
                 → suc-comp-ren (≤ₛ-trans e e') b
                 ≐ʳ (suc-comp-ren e' b₂ ∘ʳ suc-comp-ren e b₁)

-- `≤ₛ-trans e id-suc` *is* `e`, so the composite is `e` at a relaxed grade
suc-comp-ren-∘-≐ {ρ₂ = ρ₂} e id-suc b b₁ b₂ =
  suc-comp-ren-≤ e b b₁
    (≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityˡ ρ₂))) b₂)

suc-comp-ren-∘-≐ e (⟨⟩-suc ρ e') b b₁ b₂ =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (suc-comp-ren-∘-≐ e e' _ b₁ _))
           (≐ʳ-sym (∘ʳ-assoc-≐ ⟨⟩-μ-ren (suc-comp-ren e' _)
                               (suc-comp-ren e b₁)))

suc-comp-ren-∘-≐ e (∷-suc V e') b b₁ b₂ =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (suc-comp-ren-∘-≐ e e' _ b₁ _))
           (≐ʳ-sym (∘ʳ-assoc-≐ (cong-⟨⟩-ren wk-ren) (suc-comp-ren e' _)
                               (suc-comp-ren e b₁)))

-- Lifting it to `slice-renᵘ`: the two copies leave a `⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-η-ren`
-- in the middle, which is the identity up to `_≐ʳ_`.

⟨⟩-η-cancel : ∀ {Γ} → (⟨⟩-η⁻¹-ren {Δ = Γ} ∘ʳ ⟨⟩-η-ren) ≐ʳ id-ren
⟨⟩-η-cancel = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ Hd)        = refl
    go (Tl-⟨⟩ (Tl-∷ x))  = refl
    go (Tl-⟨⟩ (Tl-⟨⟩ x)) = refl

slice-renᵘ-∘ : ∀ {St St' St'' : 𝕊 []}
             → (q' : Slice St' uᵣ St'' uᵣ) → (q : Slice St uᵣ St' uᵣ)
             → slice-renᵘ (slice-∘ q' q) ≐ʳ (slice-renᵘ q' ∘ʳ slice-renᵘ q)
slice-renᵘ-∘ (slice e' b') (slice e b) = mk≐ʳ go
  where
    -- `_≐ʳ_` does not see associativity (`var-tgt` of a composite *is* the
    -- composite), so the whole thing is pointwise: replace the composite
    -- extension by the two, then cancel the `⟨⟩-η` pair in the middle.
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go x =
      trans (cong (var-tgt′ ⟨⟩-η-ren)
                  (at (suc-comp-ren-∘-≐ e e' _ b b') _))
            (cong (λ z → var-tgt′ ⟨⟩-η-ren (var-tgt′ (suc-comp-ren e' b') z))
                  (sym (at ⟨⟩-η-cancel _)))

------------------------------------------------------------------------
-- WHAT AN EXTENSION DOES TO A VARIABLE
--
-- `suc-comp-ren` sends a locked variable to a locked variable: the extension
-- embeds `toCtx St` into `toCtx St₁`, and the renaming is that embedding under
-- the lock. Making this explicit is what lets the `⟨⟩-η` round trip in
-- `slice-renᵘ`/`unbox-ren` be cancelled at a specific variable.
------------------------------------------------------------------------

≤ₛ-embed : ∀ {St St₁ : 𝕊 []} → (e : St ≤ₛ St₁) → ∀ {A σ}
         → A ∈[ σ ] toCtx St → Σ[ σ' ∈ R ] A ∈[ σ' ] toCtx St₁
≤ₛ-embed id-suc        {σ = σ} x = σ , x
≤ₛ-embed (⟨⟩-suc ρ e)  x with ≤ₛ-embed e x
... | σ' , y = σ' ·ᵣ ρ , Tl-⟨⟩ y
≤ₛ-embed (∷-suc V e)   x with ≤ₛ-embed e x
... | σ' , y = σ' , Tl-∷ y

suc-comp-ren-tgt : ∀ {St St₁ : 𝕊 []} {ρ₂ ρ₃ : R} → (e : St ≤ₛ St₁)
                 → (b : ≤ₛ-grade e ·ᵣ ρ₃ ≾ᵣ ρ₂)
                 → ∀ {A σ} → (x : A ∈[ σ ] toCtx St)
                 → var-tgt (suc-comp-ren e b) (Tl-⟨⟩ x)
                 ≡ (proj₁ (≤ₛ-embed e x) ·ᵣ ρ₃ , Tl-⟨⟩ (proj₂ (≤ₛ-embed e x)))

suc-comp-ren-tgt id-suc       b x = refl
suc-comp-ren-tgt (⟨⟩-suc ρ e) b x =
  cong (var-tgt′ ⟨⟩-μ-ren) (suc-comp-ren-tgt e _ x)
suc-comp-ren-tgt (∷-suc V e)  b x =
  cong (var-tgt′ (cong-⟨⟩-ren wk-ren)) (suc-comp-ren-tgt e _ x)

-- The embedding is functorial, and the two `⟨⟩-η` renamings are its identity
-- steps. Together these compute what `slice-renᵘ` and `unbox-ren` do to a
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

-- What a slice does to a variable: the embedding of its extension.

slice-renᵘ-tgt : ∀ {St St' : 𝕊 []} → (q : Slice St uᵣ St' uᵣ)
               → ∀ {A σ} → (x : A ∈[ σ ] toCtx St)
               → var-tgt (slice-renᵘ q) x ≡ ≤ₛ-embed (ext q) x
slice-renᵘ-tgt (slice e b) x =
  trans (cong (λ t → var-tgt′ ⟨⟩-η-ren (var-tgt′ (suc-comp-ren e b) t))
              (⟨⟩-η⁻¹-tgt x))
        (cong (var-tgt′ ⟨⟩-η-ren) (suc-comp-ren-tgt e b x))

unbox-ren-tgt : ∀ {St St' : 𝕊 []} {ρ : R} → (q : Slice St ρ St' uᵣ)
              → ∀ {A σ} → (x : A ∈[ σ ] toCtx St)
              → var-tgt (unbox-ren q) (Tl-⟨⟩ x) ≡ ≤ₛ-embed (ext q) x
unbox-ren-tgt (slice e b) x = cong (var-tgt′ ⟨⟩-η-ren) (suc-comp-ren-tgt e b x)

-- Looking a resource up after transporting it along a slice
-- reaches the same cell as looking it up along the composite.

unbox-cells : ∀ {A ρ} {St St' St₂ : 𝕊 []}
            → (q₀ : Slice St uᵣ St' uᵣ) → (q' : Slice St' ρ St₂ uᵣ)
            → ∀ {σ} → (x : [ ρ ] A ∈[ σ ] toCtx St)
            → var-tgt (unbox-ren q') (Tl-⟨⟩ (proj₂ (var-tgt (slice-renᵘ q₀) x)))
            ≡ var-tgt (unbox-ren (slice-∘ᵘ q' q₀)) (Tl-⟨⟩ x)
unbox-cells q₀ q' x =
  trans (unbox-ren-tgt q' (proj₂ (var-tgt (slice-renᵘ q₀) x)))
    (trans (cong (λ t → ≤ₛ-embed (ext q') (proj₂ t)) (slice-renᵘ-tgt q₀ x))
      (trans (sym (≤ₛ-embed-∘ (ext q₀) (ext q') x))
             (sym (unbox-ren-tgt (slice-∘ᵘ q' q₀) x))))

-- The same at the level `unbox-lookup` consumes it: a boxed value *is* a
-- variable, so the cell it names is `unbox-cells`.

unbox-cellsᵛ : ∀ {A ρ} {St St' St₂ : 𝕊 []}
             → (q₀ : Slice St uᵣ St' uᵣ) → (q' : Slice St' ρ St₂ uᵣ)
             → (V : toCtx St ⊢V⦂ [ ρ ] A)
             → unbox-tgt (unbox-ren q') (slice-val q₀ V)
             ≡ unbox-tgt (unbox-ren (slice-∘ᵘ q' q₀)) V
unbox-cellsᵛ q₀ q' (var f x) = unbox-cells q₀ q' x

------------------------------------------------------------------------
-- RUNS
--
-- What a whole run accumulates. `PreservationTheorem` has the per-step facts;
-- these are their closure under composition, packaged as the slice a run
-- licenses. The `Slice` is exactly the data `SEQ-STEP`/`HANDLE-STEP` consume,
-- which is what lets a run be lifted under those two formers.
------------------------------------------------------------------------

steps-extends-state : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
                    → cf ↝* cf' → Config.state cf ≤ₛ Config.state cf'

steps-extends-state ε*       = id-suc
steps-extends-state (r ◅ rs) =
  ≤ₛ-trans (step-extends-state r) (steps-extends-state rs)

steps-grade-≾ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
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

steps-slice : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
            → (rs : cf ↝* cf')
            → Slice (Config.state cf) (mapᵉ ε) (Config.state cf') (mapᵉ ε')
steps-slice rs = slice (steps-extends-state rs) (steps-grade-≾ rs)

-- LIFTING A RUN UNDER A FORMER
--
-- Both congruence rules retype the continuation along `suc-comp-ren` of the
-- step's own extension, so after a run it has been renamed once per step.
-- The composite is the run's own renaming only up to `_≐ʳ_`
-- (`suc-comp-ren-∘-≐`), and at the empty run it is a grade relaxation rather
-- than the identity, so the continuation reached is returned as it stands.

seq-steps : ∀ {A B ε ε' ε₂} {St St₁ : 𝕊 []}
          → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₁ : toCtx St₁ ⊢C⦂ A ‼ ε'}
          → (rs : ⟨ St , M ⟩ ↝* ⟨ St₁ , M₁ ⟩)
          → (N : toCtx St ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
          -----------------------------------------------------------------
          → Σ[ N₁ ∈ (toCtx St₁ ⟨ mapᵉ ε' ⟩ ∷ A ⊢C⦂ B ‼ ε₂) ]
              (⟨ St , M ⨟ N ⟩ ↝* ⟨ St₁ , M₁ ⨟ N₁ ⟩)
            × (N₁ ≐ᶜ C-rename (cong-∷-ren (slice-ren (steps-slice rs))) N)

seq-steps ε* N =
  N , ε* , ≐ᶜ-sym (C-rename-id-≐ (cong-∷-ren-id-≐ (⟨⟩-≤-ren-id-≐ _)) N)

seq-steps (r ◅ rs) N
  with seq-steps rs
         (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                             (step-grade-≾ r))) N)
... | N₁ , rs' , eN₁ =
    N₁
  , SEQ-STEP r (step-grade-≾ r) ◅ rs'
  , ≐ᶜ-trans eN₁
      (≐ᶜ-trans
        (≐ᶜ-sym (C-rename-∘ (cong-∷-ren (slice-ren (steps-slice rs)))
                            (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                      (step-grade-≾ r))) N))
        (C-rename-≐
          (≐ʳ-trans
            (≐ʳ-sym (cong-∷-ren-∘-≐ (slice-ren (steps-slice rs))
                                    (suc-comp-ren (step-extends-state r)
                                                  (step-grade-≾ r))))
            (cong-∷-ren-≐
              (≐ʳ-sym (suc-comp-ren-∘-≐ (step-extends-state r)
                                        (steps-extends-state rs)
                                        _ (step-grade-≾ r)
                                        (steps-grade-≾ rs)))))
          N))

-- The same under `handle`, which also retypes the clauses — along an equality
-- of the two states' eternal parts, both empty. The transports compose, and any
-- two proofs of the equality agree, so the clauses reached are the original ones
-- transported once.

toCtxᴱ-≡ : (St St₁ : 𝕊 []) → toCtx St ᴱ ≡ toCtx St₁ ᴱ
toCtxᴱ-≡ St St₁ = trans (toCtxᴱ-[] St) (sym (toCtxᴱ-[] St₁))

subst² : ∀ {a} {X : Set a} {P : X → Set} {x y z : X}
       → (e₁ : x ≡ y) → (e₂ : y ≡ z) → (e₃ : x ≡ z) → (v : P x)
       → subst P e₂ (subst P e₁ v) ≡ subst P e₃ v
subst² refl refl refl v = refl

handle-steps : ∀ {A B ε ε' ε₂} {St St₁ : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₁ : toCtx St₁ ⊢C⦂ A ‼ ε'}
             → (rs : ⟨ St , M ⟩ ↝* ⟨ St₁ , M₁ ⟩)
             → (H : (op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St ᴱ))
             → (N : toCtx St ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
             ---------------------------------------------------------------
             → Σ[ H₁ ∈ ((op : Op) → (ε₃ : E) → Cl B op ε₃ (toCtx St₁ ᴱ)) ]
               Σ[ N₁ ∈ (toCtx St₁ ⟨ mapᵉ ε' ⟩ ∷ A ⊢C⦂ B ‼ ε₂) ]
                 (⟨ St , handle M `with H `in N ⟩ ↝*
                  ⟨ St₁ , handle M₁ `with H₁ `in N₁ ⟩)
               × (∀ op ε₃ → H₁ op ε₃
                    ≡ subst (Cl B op ε₃) (toCtxᴱ-≡ St St₁) (H op ε₃))
               × (N₁ ≐ᶜ C-rename (cong-∷-ren (slice-ren (steps-slice rs))) N)

handle-steps {B = B} {St = St} ε* H N =
    H , N , ε*
  , (λ op ε₃ →
       cong (λ e → subst (Cl B op ε₃) e (H op ε₃))
            (uip {p = refl} {q = toCtxᴱ-≡ St St}))
  , ≐ᶜ-sym (C-rename-id-≐ (cong-∷-ren-id-≐ (⟨⟩-≤-ren-id-≐ _)) N)

handle-steps {B = B} {St = St} {St₁ = St₁} (_◅_ {cf₂ = ⟨ St' , M' ⟩} r rs) H N
  with handle-steps rs
         (λ op ε₃ →
            subst (Cl B op ε₃) (toCtxᴱ-≡ St St') (H op ε₃))
         (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                             (step-grade-≾ r))) N)
... | H₁ , N₁ , rs' , eH₁ , eN₁ =
    H₁ , N₁
  , HANDLE-STEP r (step-grade-≾ r) ◅ rs'
  , (λ op ε₃ →
       trans (eH₁ op ε₃)
             (subst² (toCtxᴱ-≡ St St') (toCtxᴱ-≡ St' St₁) (toCtxᴱ-≡ St St₁)
                     (H op ε₃)))
  , ≐ᶜ-trans eN₁
      (≐ᶜ-trans
        (≐ᶜ-sym (C-rename-∘ (cong-∷-ren (slice-ren (steps-slice rs)))
                            (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                                      (step-grade-≾ r))) N))
        (C-rename-≐
          (≐ʳ-trans
            (≐ʳ-sym (cong-∷-ren-∘-≐ (slice-ren (steps-slice rs))
                                    (suc-comp-ren (step-extends-state r)
                                                  (step-grade-≾ r))))
            (cong-∷-ren-≐
              (≐ʳ-sym (suc-comp-ren-∘-≐ (step-extends-state r)
                                        (steps-extends-state rs)
                                        _ (step-grade-≾ r)
                                        (steps-grade-≾ rs)))))
          N))

-- Transporting a slice's residual grade along a grade equality: the renaming is
-- unchanged, since the bound is all that differs (`suc-comp-ren-irr`). This is
-- what reconciles a run's `mapᵉ uₑ` with the `uᵣ` a `Slice` wants.

suc-comp-ren-grade : ∀ {St St₁ : 𝕊 []} {ρ'' ρ₁ ρ₂ : R} → (e : St ≤ₛ St₁)
                   → (eg : ρ₁ ≡ ρ₂)
                   → (b₁ : ≤ₛ-grade e ·ᵣ ρ₁ ≾ᵣ ρ'')
                   → (b₂ : ≤ₛ-grade e ·ᵣ ρ₂ ≾ᵣ ρ'')
                   → (eq-ren (cong (toCtx St₁ ⟨_⟩) eg) ∘ʳ suc-comp-ren e b₁)
                   ≐ʳ suc-comp-ren e b₂
suc-comp-ren-grade e refl b₁ b₂ =
  ≐ʳ-trans (∘ʳ-identityˡ-≐ (suc-comp-ren e b₁)) (suc-comp-ren-irr e b₁ b₂)

-- The same on the *source* side: an extension started at a propositionally
-- equal guard is the same renaming, `eq-ren` being the identity there.

suc-comp-ren-grade-src : ∀ {St St₁ : 𝕊 []} {ρ₁ ρ₂ ρ₃ : R} → (e : St ≤ₛ St₁)
                       → (eg : ρ₁ ≡ ρ₂)
                       → (b₁ : ≤ₛ-grade e ·ᵣ ρ₃ ≾ᵣ ρ₂)
                       → (b₂ : ≤ₛ-grade e ·ᵣ ρ₃ ≾ᵣ ρ₁)
                       → (suc-comp-ren e b₁ ∘ʳ eq-ren (cong (toCtx St ⟨_⟩) eg))
                       ≐ʳ suc-comp-ren e b₂
suc-comp-ren-grade-src e refl b₁ b₂ =
  ≐ʳ-trans (∘ʳ-identityʳ-≐ (suc-comp-ren e b₁)) (suc-comp-ren-irr e b₁ b₂)

-- Crossing a lock and then moving on is crossing it into the later state: both
-- send `Tl-⟨⟩ x` to the composite extension's embedding.

slice-unbox-ren-≐ : ∀ {ρ} {St St' St'' : 𝕊 []}
                  → (q' : Slice St' uᵣ St'' uᵣ) → (q : Slice St ρ St' uᵣ)
                  → (slice-renᵘ q' ∘ʳ unbox-ren q) ≐ʳ unbox-ren (slice-∘ q' q)
slice-unbox-ren-≐ q' q = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) =
      trans (cong (var-tgt′ (slice-renᵘ q')) (unbox-ren-tgt q x))
        (trans (slice-renᵘ-tgt q' (proj₂ (≤ₛ-embed (ext q) x)))
          (trans (sym (≤ₛ-embed-∘ (ext q) (ext q') x))
                 (sym (unbox-ren-tgt (slice-∘ q' q) x))))

-- Allocating a cell renames the old context by weakening past it.

alloc-ren-≐ : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → slice-renᵘ (alloc-slice V) ≐ʳ wk-ren
alloc-ren-≐ V = mk≐ʳ (λ x → slice-renᵘ-tgt (alloc-slice V) x)

-- The same for the renaming an `unbox` consumes: splitting the guard into the
-- slice's own part and a residual `σ`, then crossing the lock under `σ`, is the
-- extension at residual `σ`. Both send `Tl-⟨⟩ x` to the embedding under `σ`.

unbox-ren-μ-≐ : ∀ {St St₁ : 𝕊 []} {ρ σ : R} → (q : Slice St ρ St₁ uᵣ)
              → (b : ≤ₛ-grade (ext q) ·ᵣ σ ≾ᵣ ρ ·ᵣ σ)
              → (cong-⟨⟩-ren {ρ = σ} (unbox-ren q) ∘ʳ ⟨⟩-μ-ren)
              ≐ʳ suc-comp-ren (ext q) b
unbox-ren-μ-≐ {σ = σ} q b = mk≐ʳ go
  where
    go : ∀ {A τ} → (x : A ∈[ τ ] _) → _
    go (Tl-⟨⟩ x) = trans (cong (Tgt-⟨⟩ σ) (unbox-ren-tgt q x))
                         (sym (suc-comp-ren-tgt (ext q) b x))

-- Crossing a lock and then following a guarded slice is following the
-- corresponding unit slice (`slice-unit`): the source grade is relaxed from `ρ`
-- to `uᵣ`, which is pre-composition with `⟨⟩-≤-ren` (`suc-comp-ren-≤ˡ`).

unbox-ren-unit : ∀ {ρ} {St St' : 𝕊 []} → (q : Slice St ρ St' uᵣ) → (p : ρ ≾ᵣ uᵣ)
               → (unbox-ren q ∘ʳ (⟨⟩-≤-ren p ∘ʳ ⟨⟩-η⁻¹-ren))
               ≐ʳ slice-renᵘ (slice-unit q p)
unbox-ren-unit q p = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go x = cong (var-tgt′ ⟨⟩-η-ren)
                (sym (at (suc-comp-ren-≤ˡ (ext q) (bound (slice-unit q p))
                                          (bound q) p)
                         (proj₂ (var-tgt ⟨⟩-η⁻¹-ren x))))

-- Two slices whose renamings are identity-like: the unit slice at a state, and
-- the slice a `DELAY` takes (whose target context *is* the source under the
-- lock). Both are needed to recognise a reduct as the action of an environment.

-- Both are `≤ₛ-embed` of the identity extension, which is the identity: a
-- variable of a state context cannot be case-split on, so this goes through the
-- `var-tgt` layer rather than pointwise.

slice-renᵘ-id-≐ : ∀ {St : 𝕊 []} → slice-renᵘ (slice-id {St} {uᵣ}) ≐ʳ id-ren
slice-renᵘ-id-≐ = mk≐ʳ (λ x → slice-renᵘ-tgt slice-id x)

unbox-ren-delay-≐ : ∀ {ρ} {St : 𝕊 []}
                  → unbox-ren (delay-slice {ρ} {St}) ≐ʳ id-ren
unbox-ren-delay-≐ = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = unbox-ren-tgt delay-slice x

------------------------------------------------------------------------
-- UNFOLDING THE LOOKUP
--
-- `unbox-lookup` is a `with` on `unbox⇒var`, so it does not reduce at an
-- abstract boxed value — but `Σ` has eta, so the scrutinee *is* its own triple
-- of projections and the block unfolds against them. Naming the body as a
-- function of the cell (`Tgt`) and the grade bound is therefore an equality
-- proved by `refl`, and it is what makes the lookup coherences provable: the
-- cell is `unbox-tgt`, whose behaviour is already known, and the bound is
-- irrelevant.
------------------------------------------------------------------------

≡→≐ᵛˢ : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≡ V' → V ≐ᵛ V'
≡→≐ᵛˢ refl = ≐ᵛ-refl _


-- Retyping along a context equality (the state equivalence needs these here).

castᵛˢ : ∀ {Γ Γ' A} → Γ ≡ Γ' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A
castᵛˢ refl V = V

castʳˢ : ∀ {Γ Γ' Δ ρ} → Γ' ≡ Γ → Ren [] (Δ ⟨ ρ ⟩) Γ' → Ren [] (Δ ⟨ ρ ⟩) Γ
castʳˢ refl w = w
castᵛˢ-pair : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
            → castᵛˢ e ⦉ V , W ⦊ ≡ ⦉ castᵛˢ e V , castᵛˢ e W ⦊
castᵛˢ-pair refl V W = refl

-- The lookup's renaming composite depends on the state only through two
-- contexts, the stored value and three proofs — so it is factored out. That is
-- what lets two lookups be compared: at corresponding contexts the proofs are
-- irrelevant (`uip`, `≾ᵣ-irrelevant`) and only the values have to be related.

lookup-ren′ : ∀ {A ρ σ} {Γ : Ctx} → (Γf Γs : Ctx)
            → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
            → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≡ σ)
            → (rel : σ ≾ᵣ ρ)
            → Ren [] (([] ++ᶜ Γf) ⟨ ρ ⟩) Γ
lookup-ren′ {A} {ρ} Γf Γs eq h rel =
     eq-ren eq
  ∘ʳ eq-ren (sym (++ᶜ-assoc Γf ([] ∷ [ ρ ] A) Γs))
  ∘ʳ wk-ren-⟨ρ⟩-ctx h
  ∘ʳ ⟨⟩-≤-ren rel
  ∘ʳ eq-ren ++ᶜ-identityˡ

lookup-body′ : ∀ {A ρ σ} {Γ : Ctx} → (Γf Γs : Ctx)
             → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
             → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≡ σ)
             → (rel : σ ≾ᵣ ρ)
             → ([] ++ᶜ Γf) ⟨ ρ ⟩ ⊢V⦂ A
             → Γ ⊢V⦂ A
lookup-body′ Γf Γs eq h rel U = V-rename (lookup-ren′ Γf Γs eq h rel) U

-- What is left for `store-fresh` is `var-tgt` of this: `eq-ren ++ᶜ-identityˡ`
-- (`eq-ren-tgt`, then `∈-++ᶜʳ-[]`), `⟨⟩-≤-ren`, the push
-- `wk-ren-⟨ρ⟩-ctx-tgt` computes, and the two relocations (`eq-ren-tgt`).

lookup-body : ∀ {A ρ} → (St : 𝕊 []) → (t : Tgt (toCtx St) ([ ρ ] A))
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

lookup-body′-≐ : ∀ {A ρ σ} {Γ Γ' : Ctx} → (eΓ : Γ' ≡ Γ)
               → {Γf Γf' Γs Γs' : Ctx} → (eF : Γf' ≡ Γf) → (eS : Γs' ≡ Γs)
               → (eq : (Γf ∷ [ ρ ] A) ++ᶜ Γs ≡ Γ)
               → (eq' : (Γf' ∷ [ ρ ] A) ++ᶜ Γs' ≡ Γ')
               → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs) ≡ σ)
               → (h' : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ Γs') ≡ σ)
               → (rel rel' : σ ≾ᵣ ρ)
               → (U : ([] ++ᶜ Γf) ⟨ ρ ⟩ ⊢V⦂ A)
               → (U' : ([] ++ᶜ Γf') ⟨ ρ ⟩ ⊢V⦂ A)
               → U ≐ᵛ castᵛˢ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) eF) U'
               → lookup-body′ Γf Γs eq h rel U
               ≐ᵛ castᵛˢ eΓ (lookup-body′ Γf' Γs' eq' h' rel' U')
lookup-body′-≐ refl refl refl eq eq' h h' rel rel' U U' eU
  rewrite uip {p = eq} {q = eq'} | uip {p = h} {q = h'}
        | ≾ᵣ-irrelevant rel rel' = V-rename-cong _ eU

-- Transporting the renaming an `unbox` consults relocates the cell it names.

unbox-tgt-cast : ∀ {Γ Γ' A ρ Δ} → (e : Γ' ≡ Γ) → (w' : Ren [] (Δ ⟨ ρ ⟩) Γ')
               → (V : Δ ⊢V⦂ [ ρ ] A)
               → unbox-tgt (castʳˢ e w') V
               ≡ (proj₁ (unbox-tgt w' V)
                 , subst (λ Γ₀ → [ ρ ] A ∈[ proj₁ (unbox-tgt w' V) ] Γ₀) e
                         (proj₂ (unbox-tgt w' V)))
unbox-tgt-cast refl w' V = refl

unbox-lookup-≡ : ∀ {A ρ Δ} → (St : 𝕊 [])
               → (w : Ren [] (Δ ⟨ ρ ⟩) (toCtx St)) → (V : Δ ⊢V⦂ [ ρ ] A)
               → unbox-lookup St w V
               ≡ lookup-body St (unbox-tgt w V) (proj₂ (proj₂ (unbox⇒var w V)))
unbox-lookup-≡ St w V = refl

-- Same cell, same value: the bound is `≾ᵣ`-irrelevant.

lookup-body-≡ : ∀ {A ρ} → (St : 𝕊 [])
              → {t t' : Tgt (toCtx St) ([ ρ ] A)} → t ≡ t'
              → (rel : proj₁ t ≾ᵣ ρ) → (rel' : proj₁ t' ≾ᵣ ρ)
              → lookup-body St t rel ≡ lookup-body St t' rel'
lookup-body-≡ St refl rel rel' =
  cong (lookup-body St _) (≾ᵣ-irrelevant rel rel')

-- Retyping the *boxed value* instead: the lookup sees it only through
-- `unbox⇒var`, so moving it along a context equality is precomposing the
-- consulted renaming with that equality.

unbox-lookup-cast-val : ∀ {Δ Δ' A ρ} → (St : 𝕊 []) → (e : Δ' ≡ Δ)
                      → (w : Ren [] (Δ ⟨ ρ ⟩) (toCtx St)) → (V : Δ' ⊢V⦂ [ ρ ] A)
                      → unbox-lookup St w (castᵛˢ e V)
                      ≐ᵛ unbox-lookup St (w ∘ʳ cong-⟨⟩-ren (eq-ren e)) V
unbox-lookup-cast-val St refl w V =
  ≡→≐ᵛˢ (lookup-body-≡ St
           (unbox-tgt-≐ (≐ʳ-sym (∘ʳ-id-≐ʳ w (cong-⟨⟩-ren-id-≐ ≐ʳ-refl))) V)
           _ _)


------------------------------------------------------------------------
-- THE STORE IS STABLE UNDER AN EXTENSION
--
-- An already-allocated cell is split off at the same state, and holds the same
-- value, however far the state has grown since. Both `≤ₛ` constructors leave
-- `split-state-fst` and `resource-lookup` alone — a lock is crossed and a newer
-- cell is skipped — so each is its own induction hypothesis.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- WHAT THE LOOKUP'S WEAKENING DOES TO A VARIABLE
--
-- `wk-ren-⟨ρ⟩-ctx` weakens out of a lock into everything the context holds
-- beyond it, which on a variable is `var-ρ-++ᶜ` — the same push, with the same
-- grade. Recursion on that context, as the renaming's own.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- WHAT AN EXTENSION ADDS AFTER AN ALREADY-ALLOCATED CELL
--
-- `store-fresh` compares the lookup at a later state with the value that was
-- stored. `≤ₛ-embed-fst` already says the cell is split off at the same state;
-- what is left is that the part *after* it grows by exactly the context the
-- extension adds. Three cases, each a `cong` of the next.
------------------------------------------------------------------------

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
              ≡ Tgt-cast (sym (≤ₛ-ctx-toCtx e))
                  (grade-++ᶜˡ ρ (≤ₛ-ctx e) , ∈-++ᶜˡ (≤ₛ-ctx e) y)

≤ₛ-embed-push id-suc       y = refl
≤ₛ-embed-push (⟨⟩-suc ρ e) y =
  trans (cong (Tgt-⟨⟩ ρ) (≤ₛ-embed-push e y))
    (trans (sym (Tgt-cast-⟨⟩ ρ (sym (≤ₛ-ctx-toCtx e)) _))
           (Tgt-cast-irr (cong (_⟨ ρ ⟩) (sym (≤ₛ-ctx-toCtx e)))
                         (sym (≤ₛ-ctx-toCtx (⟨⟩-suc ρ e))) _))
≤ₛ-embed-push (∷-suc V e)  y =
  trans (cong Tgt-∷ (≤ₛ-embed-push e y))
    (trans (sym (Tgt-cast-∷ (sym (≤ₛ-ctx-toCtx e)) _))
           (Tgt-cast-irr (cong (_∷ _) (sym (≤ₛ-ctx-toCtx e)))
                         (sym (≤ₛ-ctx-toCtx (∷-suc V e))) _))

------------------------------------------------------------------------
-- READING BACK A FRESHLY ALLOCATED CELL
--
-- What `store-fresh` needs. Looking up, at whatever state the run has reached,
-- the cell `BOX` just allocated returns the value that was stored — renamed.
-- Both sides are that value renamed, so the content is a renaming agreement,
-- and both renamings *push* the value's context under everything the state has
-- gained since: the lookup by `wk-ren-⟨ρ⟩-ctx` out of the cell's own lock, the
-- slice by `≤ₛ-embed`.
------------------------------------------------------------------------

-- Casting the target of a renaming is prefixing it with an `eq-ren`.

castᵛˢ-rename : ∀ {Γ Γ' Γ'' A} → (e : Γ' ≡ Γ'') → (r : Ren [] Γ Γ')
              → (V : Γ ⊢V⦂ A)
              → castᵛˢ e (V-rename r V) ≐ᵛ V-rename (eq-ren e ∘ʳ r) V
castᵛˢ-rename refl r V =
  ≐ᵛ-sym (≐ᵛ-trans (V-rename-∘ id-ren r V) (V-rename-id-≐ ≐ʳ-refl _))

-- Transporting a stored value along an equality of the states it was split off
-- at is transporting it along the contexts.

subst-state-castᵛˢ : ∀ {A ρ} {St St' : 𝕊 []} → (p : St ≡ St')
                   → (U : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
                   → subst (λ S → ([] ++ᶜ toCtx S ⟨ ρ ⟩) ⊢V⦂ A) p U
                   ≡ castᵛˢ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) (cong toCtx p)) U
subst-state-castᵛˢ refl U = refl

-- The renaming agreement. The lookup's composite runs, right to left: out of
-- the leading `[] ++ᶜ`, across the cell's own lock at the grade the state after
-- it contributes, out of that lock into everything after the cell, and back
-- along the two context equalities. The slice's runs by `≤ₛ-embed`. Both land
-- on `∈-++ᶜˡ (≤ₛ-ctx e) (Tl-∷ y)`, relocated by the same `≤ₛ-ctx-toCtx e`.

alloc-lookup-ren : ∀ {A ρ σ} {St St' : 𝕊 []}
                 → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
                 → (e : (St ∷ₛ V) ≤ₛ St')
                 → (h : ctx-grade (([] ∷ [ ρ ] A) ++ᶜ ≤ₛ-ctx e) ≡ σ)
                 → (rel : σ ≾ᵣ ρ)
                 → (q₀ : Slice St ρ St' uᵣ)
                 → ext q₀ ≡ ≤ₛ-trans (∷-suc V id-suc) e
                 → (eq-ren (sym (≤ₛ-ctx-toCtx e))
                     ∘ʳ lookup-ren′ (toCtx St) (≤ₛ-ctx e) refl h rel)
                 ≐ʳ (unbox-ren q₀ ∘ʳ eq-ren (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}))

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
                     (wk-ren-⟨ρ⟩-ctx-tgt (Δ₁ ++ᶜ Δ) h y))
          (trans (cong (λ t → f₅ (f₄ t))
                       (trans (eq-ren-tgt assoc (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) y))
                              (∈-++ᶜˡ-assoc Δ₁ Δ y)))
            (trans (eq-ren-tgt eΓ (∈-++ᶜˡ Δ (Tl-∷ y)))
              (sym (trans (cong (var-tgt′ (unbox-ren q₀)) s₀)
                     (trans (unbox-ren-tgt q₀ y)
                       (trans (cong (λ z → ≤ₛ-embed z y) eq₀)
                         (trans (≤ₛ-embed-∘ (∷-suc V id-suc) e y)
                                (≤ₛ-embed-push e (Tl-∷ y))))))))))
      where
        y : A' ∈[ τ' ] toCtx St
        y = subst (λ Γ₀ → A' ∈[ τ' ] Γ₀) ++ᶜ-identityˡ w

        f₁ = var-tgt′ {A = A'} (⟨⟩-≤-ren rel)
        f₂ = var-tgt′ {A = A'} (wk-ren-⟨ρ⟩-ctx h)
        f₃ = var-tgt′ {A = A'} (eq-ren assoc)
        f₄ = var-tgt′ {A = A'} (eq-ren (refl {x = (toCtx St ∷ [ ρ ] A) ++ᶜ Δ}))
        f₅ = var-tgt′ {A = A'} (eq-ren eΓ)

        s₀ : var-tgt (eq-ren (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩})) (Tl-⟨⟩ w)
           ≡ (τ' ·ᵣ ρ , Tl-⟨⟩ y)
        s₀ = trans (eq-ren-tgt (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}) (Tl-⟨⟩ w))
                   (cong (λ z → τ' ·ᵣ ρ , z)
                         (subst-Tl-⟨⟩ (++ᶜ-identityˡ {toCtx St}) w))

-- Hence the lookup itself. `lookup-body′-≐` moves the lookup's own data — the
-- state the cell is split off at, what the state gained after it, and the value
-- stored — onto the data the allocation presents, which `≤ₛ-embed-fst`,
-- `≤ₛ-embed-snd-ctx` and `≤ₛ-embed-lookup` supply.

alloc-lookup-≐ : ∀ {A ρ} {St St' : 𝕊 []}
               → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
               → (e : (St ∷ₛ V) ≤ₛ St')
               → (rel : proj₁ (≤ₛ-embed e (Hd {Γ = toCtx St})) ≾ᵣ ρ)
               → (q₀ : Slice St ρ St' uᵣ)
               → ext q₀ ≡ ≤ₛ-trans (∷-suc V id-suc) e
               → lookup-body St' (≤ₛ-embed e (Hd {Γ = toCtx St})) rel
               ≐ᵛ V-rename (unbox-ren q₀ ∘ʳ eq-ren ++ᶜ-identityˡ) V

alloc-lookup-≐ {A} {ρ} {St} {St'} V e rel q₀ eq₀ =
  ≐ᵛ-trans (lookup-body′-≐ eΓ eF eS _ refl _ h rel rel _ V eU)
    (≐ᵛ-trans (castᵛˢ-rename eΓ (lookup-ren′ (toCtx St) Δ refl h rel) V)
              (V-rename-≐ (alloc-lookup-ren V e h rel q₀ eq₀) V))
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
       ≐ᵛ castᵛˢ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩) eF) V
    eU = ≡→≐ᵛˢ (trans (≤ₛ-embed-lookup e (Hd {Γ = toCtx St}))
                      (subst-state-castᵛˢ
                         (sym (≤ₛ-embed-fst e (Hd {Γ = toCtx St}))) V))
