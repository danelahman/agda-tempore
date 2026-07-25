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

-- A guarded slice whose guard is itself below the unit is a unit slice: the
-- extension is the same, only the bound is relaxed. This is how a value under a
-- lock is moved forward — a *usable* variable's grade bound gives `ρ ≾ᵣ uᵣ` by
-- the grade monoid's zero-product law.

slice-unit : ∀ {St St' ρ} → Slice St ρ St' uᵣ → ρ ≾ᵣ uᵣ → Slice St uᵣ St' uᵣ
slice-unit (slice e b) p = slice e (≾ᵣ-trans b p)

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

⟨⟩-η-tgt : ∀ {Γ A σ} → (x : A ∈[ σ ] Γ)
         → var-tgt (⟨⟩-η-ren {Γ = Γ}) (Tl-⟨⟩ x) ≡ (σ , x)
⟨⟩-η-tgt x = refl

⟨⟩-η⁻¹-tgt : ∀ {Γ A σ} → (x : A ∈[ σ ] Γ)
           → var-tgt (⟨⟩-η⁻¹-ren {Γ = Γ}) x ≡ (σ ·ᵣ uᵣ , Tl-⟨⟩ x)
⟨⟩-η⁻¹-tgt Hd        = refl
⟨⟩-η⁻¹-tgt (Tl-∷ x)  = refl
⟨⟩-η⁻¹-tgt (Tl-⟨⟩ x) = refl

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

-- The variable an `unbox` refers to, forgetting its grade bound. `unbox⇒var`
-- reads it off with `var-rename`, so `_≐ʳ_`-equal renamings agree on it.

unbox-tgt : ∀ {Γ A ρ Δ} → Ren (Δ ⟨ ρ ⟩) Γ → Δ ⊢V⦂ [ ρ ] A → Tgt Γ ([ ρ ] A)
unbox-tgt w V = proj₁ (unbox⇒var w V) , proj₁ (proj₂ (unbox⇒var w V))

unbox-tgt-≐ : ∀ {Γ A ρ Δ} {w w' : Ren (Δ ⟨ ρ ⟩) Γ}
            → w ≐ʳ w' → (V : Δ ⊢V⦂ [ ρ ] A)
            → unbox-tgt w V ≡ unbox-tgt w' V
unbox-tgt-≐ hw V with grad-typ⇒var V
... | _ , y , f , refl = at hw (Tl-⟨⟩ y)

-- Consequently: looking a resource up after transporting it along a slice
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

Cl : (B : VType) → (op : Op) → (ε₃ : E) → (Γ' : Ctx) → Ctx → Set
Cl B op ε₃ Γ' Γ₀ =
  Γ₀ ++ᶜ Γ' ∷ type-of-gtype (param op)
    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₃)
  ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)

toCtxᴱ-≡ : (St St₁ : 𝕊 []) → toCtx St ᴱ ≡ toCtx St₁ ᴱ
toCtxᴱ-≡ St St₁ = trans (toCtxᴱ-[] St) (sym (toCtxᴱ-[] St₁))

subst² : ∀ {a} {X : Set a} {P : X → Set} {x y z : X}
       → (e₁ : x ≡ y) → (e₂ : y ≡ z) → (e₃ : x ≡ z) → (v : P x)
       → subst P e₂ (subst P e₁ v) ≡ subst P e₃ v
subst² refl refl refl v = refl

handle-steps : ∀ {A B ε ε' ε₂} {St St₁ : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₁ : toCtx St₁ ⊢C⦂ A ‼ ε'}
             → (rs : ⟨ St , M ⟩ ↝* ⟨ St₁ , M₁ ⟩)
             → (H : (op : Op) → (ε₃ : E) → (Γ' : Ctx)
                  → Cl B op ε₃ Γ' (toCtx St ᴱ))
             → (N : toCtx St ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
             ---------------------------------------------------------------
             → Σ[ H₁ ∈ ((op : Op) → (ε₃ : E) → (Γ' : Ctx)
                        → Cl B op ε₃ Γ' (toCtx St₁ ᴱ)) ]
               Σ[ N₁ ∈ (toCtx St₁ ⟨ mapᵉ ε' ⟩ ∷ A ⊢C⦂ B ‼ ε₂) ]
                 (⟨ St , handle M `with H `in N ⟩ ↝*
                  ⟨ St₁ , handle M₁ `with H₁ `in N₁ ⟩)
               × (∀ op ε₃ Γ' → H₁ op ε₃ Γ'
                    ≡ subst (Cl B op ε₃ Γ') (toCtxᴱ-≡ St St₁) (H op ε₃ Γ'))
               × (N₁ ≐ᶜ C-rename (cong-∷-ren (slice-ren (steps-slice rs))) N)

handle-steps {B = B} {St = St} ε* H N =
    H , N , ε*
  , (λ op ε₃ Γ' →
       cong (λ e → subst (Cl B op ε₃ Γ') e (H op ε₃ Γ'))
            (uip {p = refl} {q = toCtxᴱ-≡ St St}))
  , ≐ᶜ-sym (C-rename-id-≐ (cong-∷-ren-id-≐ (⟨⟩-≤-ren-id-≐ _)) N)

handle-steps {B = B} {St = St} {St₁ = St₁} (_◅_ {cf₂ = ⟨ St' , M' ⟩} r rs) H N
  with handle-steps rs
         (λ op ε₃ Γ' →
            subst (Cl B op ε₃ Γ') (toCtxᴱ-≡ St St') (H op ε₃ Γ'))
         (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r)
                                             (step-grade-≾ r))) N)
... | H₁ , N₁ , rs' , eH₁ , eN₁ =
    H₁ , N₁
  , HANDLE-STEP r (step-grade-≾ r) ◅ rs'
  , (λ op ε₃ Γ' →
       trans (eH₁ op ε₃ Γ')
             (subst² (toCtxᴱ-≡ St St') (toCtxᴱ-≡ St' St₁) (toCtxᴱ-≡ St St₁)
                     (H op ε₃ Γ')))
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

-- Resuming: the renaming a `HANDLE-OP` resumption transports the continuation
-- by is the one the environment's own lock gives, once the resumption's slice is
-- extended by the lock it lands under. Both send a locked variable to the
-- embedding of the same extension.

unbox-ren-resume-≐ : ∀ {ρ} {St St₂ : 𝕊 []} → (q : Slice St ρ St₂ ρ)
                   → unbox-ren (slice-∘ delay-slice q) ≐ʳ slice-ren q
unbox-ren-resume-≐ {ρ} q = mk≐ʳ go
  where
    go : ∀ {A σ} → (x : A ∈[ σ ] _) → _
    go (Tl-⟨⟩ x) =
      trans (unbox-ren-tgt (slice-∘ delay-slice q) x)
        (trans (≤ₛ-embed-∘ (ext q) (⟨⟩-suc ρ id-suc) x)
               (sym (suc-comp-ren-tgt (ext q) (bound q) x)))

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

lookup-body : ∀ {A ρ} → (St : 𝕊 []) → (t : Tgt (toCtx St) ([ ρ ] A))
            → proj₁ t ≾ᵣ ρ → toCtx St ⊢V⦂ A
lookup-body {A} {ρ} St (ρ' , z) rel =
  V-rename
    (   eq-ren (split-state-++ᶜ St z)
     ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _))
     ∘ʳ wk-ren-⟨ρ⟩-ctx
          (trans
            (trans
              (trans
                (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd St z)))
                (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd St z)))))
              (sym (grades-≡ (split-state-snd St z))))
            (snd-split-time≡time-from-head St z))
     ∘ʳ ⟨⟩-≤-ren rel
     ∘ʳ eq-ren ++ᶜ-identityˡ)
    (resource-lookup St z)

unbox-lookup-≡ : ∀ {A ρ Δ} → (St : 𝕊 [])
               → (w : Ren (Δ ⟨ ρ ⟩) (toCtx St)) → (V : Δ ⊢V⦂ [ ρ ] A)
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
