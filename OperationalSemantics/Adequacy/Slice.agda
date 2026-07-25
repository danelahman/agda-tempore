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

open import Util.Equality

module OperationalSemantics.Adequacy.Slice (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import OperationalSemantics.Adequacy.RenEquivalence Spec

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

slice-ren : ∀ {St ρ St' ρ'} → Slice St ρ St' ρ' → Ren (toCtx St ⟨ ρ ⟩) (toCtx St' ⟨ ρ' ⟩)
slice-ren (slice e b) = suc-comp-ren e b

-- Identity: no extension, nothing accumulated.

slice-id : ∀ {St ρ} → Slice St ρ St ρ
slice-id {ρ = ρ} = slice id-suc (≾ᵣ-reflexive (·ᵣ-identityˡ ρ))

-- At the unit lock the slice is a plain renaming `toCtx St → toCtx St'`.

slice-renᵘ : ∀ {St St'} → Slice St uᵣ St' uᵣ → Ren (toCtx St) (toCtx St')
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

unbox-ren : ∀ {St ρ St'} → Slice St ρ St' uᵣ → Ren (toCtx St ⟨ ρ ⟩) (toCtx St')
unbox-ren q = ⟨⟩-η-ren ∘ʳ slice-ren q

-- Resuming a continuation guarded by `ρ` at a later state: transport it along
-- the slice, then feed it the arity value. The result lives over the *locked*
-- state `St' ⟨ ρ ⟩ₛ`, which is where `HANDLE-OP` resumes.

resume : ∀ {St St' ρ A ε B}
       → (q : Slice St ρ St' ρ)
       → toCtx St ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε
       → toCtx (St' ⟨ ρ ⟩ₛ) ⊢V⦂ B
       → toCtx (St' ⟨ ρ ⟩ₛ) ⊢C⦂ A ‼ ε
resume q M W = (C-rename (cong-∷-ren (slice-ren q)) M) [ Hd ↦ W ]c

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
            → (⟨⟩-μ-ren {Γ = Γ} {ρ = ρ} {ρ' = ρ₂} ∘ʳ ⟨⟩-≤-ren p')
            ≐ʳ (⟨⟩-≤-ren p ∘ʳ ⟨⟩-μ-ren)
⟨⟩-μ-≤-comm p p' = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) = refl

wk-≤-comm : ∀ {Γ A ρ₁ ρ₂} → (p : ρ₂ ≾ᵣ ρ₁)
          → (cong-⟨⟩-ren {Γ = Γ} {ρ = ρ₂} (wk-ren {A = A}) ∘ʳ ⟨⟩-≤-ren p)
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

⟨⟩-η-cancel : ∀ {Γ} → (⟨⟩-η⁻¹-ren {Γ = Γ} ∘ʳ ⟨⟩-η-ren) ≐ʳ id-ren
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
