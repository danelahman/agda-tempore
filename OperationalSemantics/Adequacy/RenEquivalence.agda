------------------------------------------------------------------------
-- When two renamings act alike.                                      --
--                                                                    --
-- `Ren` is a free syntactic structure: `id-ren`, `_∘ʳ_` and the      --
-- congruences are constructors, so composition is not associative    --
-- and `cong-ren` does not commute with it on the nose. What is true  --
-- is that renamings agreeing on variables act the same on terms, and --
-- `Val`'s Kripke clauses need that.                                  --
--                                                                    --
-- `_≐ʳ_` compares renamings by where they send variables — grade and --
-- position, not the grade-bound proof, which is irrelevant.          --
--                                                                    --
-- Nothing here is specific to adequacy: this is the equivalence of   --
-- renamings and the coherence laws of the action with respect to it, --
-- and it belongs in `Syntax.Renamings`/`Syntax.RenActions`. It lives --
-- here to keep the work-in-progress out of `Everything.agda`; see    --
-- the cleanup list in `notes/adequacy-plan.md`.                      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Relation.Nullary using (yes; no)

open import Util.Equality

module OperationalSemantics.Adequacy.RenEquivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings  Spec
open import Syntax.Types      Spec

-- Where a renaming sends a variable, forgetting the grade bound.

Tgt : Ctx → VType → Set
Tgt Γ' A = Σ[ ρ' ∈ R ] A ∈[ ρ' ] Γ'

var-tgt : ∀ {Γ Γ' A ρ} → Ren [] Γ Γ' → A ∈[ ρ ] Γ → Tgt Γ' A
var-tgt r x = proj₁ (var-rename r x) , proj₂ (proj₂ (var-rename r x))

-- The same, at an already-located variable: this is what makes `var-tgt` of a
-- composite the composite of `var-tgt`s, definitionally.

var-tgt′ : ∀ {Γ' Γ'' A} → Ren [] Γ' Γ'' → Tgt Γ' A → Tgt Γ'' A
var-tgt′ r (ρ' , y) = var-tgt r y

-- Pushing a `Tgt` under one more binder, resp. one more lock. Named rather than
-- written as a lambda because `Tgt` is a Σ, so `cong` cannot infer the motive.

Tgt-∷ : ∀ {Γ A B} → Tgt Γ A → Tgt (Γ ∷ B) A
Tgt-∷ (σ , y) = σ , Tl-∷ y

Tgt-⟨⟩ : ∀ {Γ A} → (ρ : R) → Tgt Γ A → Tgt (Γ ⟨ ρ ⟩) A
Tgt-⟨⟩ ρ (σ , y) = σ ·ᵣ ρ , Tl-⟨⟩ y

-- RELOCATING A VARIABLE
--
-- A context equality that only extends a smaller one relocates a variable by
-- pushing the equality inside the constructors. Kept here so that both the
-- environment and the state equivalence can use it.

-- Relocating a variable past a context equality that only extends it.

subst-Hd : ∀ {Γ Γ' A} → (e : Γ ≡ Γ')
         → subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) (cong (_∷ A) e) Hd ≡ Hd
subst-Hd refl = refl

subst-Tl-∷ : ∀ {Γ Γ' A B ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
           → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (cong (_∷ B) e) (Tl-∷ x)
           ≡ Tl-∷ (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
subst-Tl-∷ refl x = refl

subst-Tl-⟨⟩ : ∀ {Γ Γ' A ρ ρ'} → (e : Γ ≡ Γ') → (x : A ∈[ ρ' ] Γ)
            → subst (λ Γ₀ → A ∈[ ρ' ·ᵣ ρ ] Γ₀) (cong (_⟨ ρ ⟩) e) (Tl-⟨⟩ x)
            ≡ Tl-⟨⟩ (subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e x)
subst-Tl-⟨⟩ refl x = refl

subst-sym-subst′ : ∀ {a p} {X : Set a} {P : X → Set p} {u v : X}
                 → (e : u ≡ v) → (w : P u)
                 → subst P (sym e) (subst P e w) ≡ w
subst-sym-subst′ refl w = refl


-- ACTING ALIKE

infix 4 _≐ʳ_

-- A record, not a function type: the statements below are used at renamings
-- Agda has to *infer*, which needs the relation to be rigid.

record _≐ʳ_ {Γ Γ'} (r r' : Ren [] Γ Γ') : Set where
  constructor mk≐ʳ
  field at : ∀ {A ρ} → (x : A ∈[ ρ ] Γ) → var-tgt r x ≡ var-tgt r' x

open _≐ʳ_ public

≐ʳ-refl : ∀ {Γ Γ'} {r : Ren [] Γ Γ'} → r ≐ʳ r
≐ʳ-refl = mk≐ʳ (λ x → refl)

≐ʳ-sym : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'} → r ≐ʳ r' → r' ≐ʳ r
≐ʳ-sym h = mk≐ʳ (λ x → sym (at h x))

≐ʳ-trans : ∀ {Γ Γ'} {r r' r'' : Ren [] Γ Γ'} → r ≐ʳ r' → r' ≐ʳ r'' → r ≐ʳ r''
≐ʳ-trans h h' = mk≐ʳ (λ x → trans (at h x) (at h' x))

-- COMPOSITION
--
-- `var-rename (r₂ ∘ʳ r₁)` locates the variable with `r₁` and then with `r₂`,
-- so all three laws below hold at the level of `var-tgt` by computation.

∘ʳ-≐ : ∀ {Γ Γ' Γ''} {r₂ r₂' : Ren [] Γ' Γ''} {r₁ r₁' : Ren [] Γ Γ'}
     → r₂ ≐ʳ r₂' → r₁ ≐ʳ r₁'
     -------------------------------
     → (r₂ ∘ʳ r₁) ≐ʳ (r₂' ∘ʳ r₁')
∘ʳ-≐ {r₂ = r₂} h₂ h₁ =
  mk≐ʳ (λ x → trans (cong (var-tgt′ r₂) (at h₁ x)) (at h₂ _))

∘ʳ-assoc-≐ : ∀ {Γ Γ' Γ'' Γ'''}
           → (r₃ : Ren [] Γ'' Γ''') → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
           ----------------------------------------------------------
           → ((r₃ ∘ʳ r₂) ∘ʳ r₁) ≐ʳ (r₃ ∘ʳ (r₂ ∘ʳ r₁))
∘ʳ-assoc-≐ r₃ r₂ r₁ = mk≐ʳ (λ x → refl)

∘ʳ-identityˡ-≐ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (id-ren ∘ʳ r) ≐ʳ r
∘ʳ-identityˡ-≐ r = mk≐ʳ (λ x → refl)

∘ʳ-identityʳ-≐ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (r ∘ʳ id-ren) ≐ʳ r
∘ʳ-identityʳ-≐ r = mk≐ʳ (λ x → refl)

-- GRADE BOUNDS ARE INVISIBLE TO `_≐ʳ_`
--
-- `⟨⟩-≤-ren` stores a `≾ᵣ` proof, but sends a variable to itself at a grade
-- fixed by the renaming's indices, so the proof is not observable.

⟨⟩-≤-ren-≐ : ∀ {Γ ρ ρ'} → (p p' : ρ' ≾ᵣ ρ)
           → ⟨⟩-≤-ren {Δ = Γ} p ≐ʳ ⟨⟩-≤-ren p'
⟨⟩-≤-ren-≐ p p' = mk≐ʳ go
  where
    go : ∀ {A ρ₀} → (x : A ∈[ ρ₀ ] _) → _
    go (Tl-⟨⟩ x) = refl

-- Relocating a whole `Tgt` along a context equality, and the pushes it commutes
-- with. `Tgt-cast-Hd` needs only that any two proofs of a `∷`-equality agree.

Tgt-cast : ∀ {Γ Γ' A} → Γ ≡ Γ' → Tgt Γ A → Tgt Γ' A
Tgt-cast {A = A} e (σ , y) = σ , subst (λ Γ₀ → A ∈[ σ ] Γ₀) e y

Tgt-cast-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (t : Tgt Γ A)
             → Tgt-cast e t ≡ Tgt-cast e' t
Tgt-cast-irr e e' t = cong (λ z → Tgt-cast z t) uip

Tgt-cast-Hd : ∀ {Γ Γ' A} → (e : Γ ∷ A ≡ Γ' ∷ A)
            → Tgt-cast {A = A} e (uᵣ , Hd) ≡ (uᵣ , Hd)
Tgt-cast-Hd {A = A} e =
  cong (λ y → uᵣ , y)
       (trans (cong (λ z → subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) z Hd)
                    (uip {p = e} {q = cong (_∷ A) (∷ᶜ-injective-ctx e)}))
              (subst-Hd (∷ᶜ-injective-ctx e)))

Tgt-cast-∷ : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → (t : Tgt Γ A)
           → Tgt-cast {A = A} (cong (_∷ C) e) (Tgt-∷ t) ≡ Tgt-∷ (Tgt-cast e t)
Tgt-cast-∷ e (σ , y) = cong (λ v → σ , v) (subst-Tl-∷ e y)

Tgt-cast-⟨⟩ : ∀ {Γ Γ' A} → (ρ : R) → (e : Γ ≡ Γ') → (t : Tgt Γ A)
            → Tgt-cast {A = A} (cong (_⟨ ρ ⟩) e) (Tgt-⟨⟩ ρ t)
            ≡ Tgt-⟨⟩ ρ (Tgt-cast e t)
Tgt-cast-⟨⟩ ρ e (σ , y) = cong (λ v → σ ·ᵣ ρ , v) (subst-Tl-⟨⟩ e y)

-- An `eq-ren` relocates a variable and leaves its grade alone.

eq-ren-tgt : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
           → var-tgt (eq-ren e) x ≡ (ρ , subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
eq-ren-tgt refl x = refl

-- PUSHING A SUFFIX VARIABLE UNDER A PREFIX
--
-- The grade is untouched: only the suffix's own locks stand to its right.

∈-++ᶜʳ : ∀ {Γ Δ A ρ} → A ∈[ ρ ] Δ → A ∈[ ρ ] (Γ ++ᶜ Δ)
∈-++ᶜʳ Hd        = Hd
∈-++ᶜʳ (Tl-∷ x)  = Tl-∷ (∈-++ᶜʳ x)
∈-++ᶜʳ (Tl-⟨⟩ x) = Tl-⟨⟩ (∈-++ᶜʳ x)

-- At the empty prefix it is the identity, once relocated.

∈-++ᶜʳ-[] : ∀ {Δ A ρ} → (x : A ∈[ ρ ] Δ)
          → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) ++ᶜ-identityˡ (∈-++ᶜʳ {Γ = []} x) ≡ x
∈-++ᶜʳ-[] Hd        = subst-Hd ++ᶜ-identityˡ
∈-++ᶜʳ-[] (Tl-∷ x)  =
  trans (subst-Tl-∷ ++ᶜ-identityˡ (∈-++ᶜʳ x)) (cong Tl-∷ (∈-++ᶜʳ-[] x))
∈-++ᶜʳ-[] (Tl-⟨⟩ x) =
  trans (subst-Tl-⟨⟩ ++ᶜ-identityˡ (∈-++ᶜʳ x)) (cong Tl-⟨⟩ (∈-++ᶜʳ-[] x))

-- PUSHING A PREFIX VARIABLE UNDER A SUFFIX
--
-- The grade depends only on the suffix, not on the variable, so it is a function
-- of its own — which is what lets the two sides of `sub-var-l` be seen to have
-- the same grade, and what keeps every lemma about the push subst-free (unlike
-- `var-ρ-++ᶜ`, whose `[]` and `⟨⟩` clauses each carry a grade transport).

grade-++ᶜˡ : R → Ctx → R
grade-++ᶜˡ ρ []         = ρ
grade-++ᶜˡ ρ (Δ ∷ B)    = grade-++ᶜˡ ρ Δ
grade-++ᶜˡ ρ (Δ ⟨ ρ' ⟩) = grade-++ᶜˡ ρ Δ ·ᵣ ρ'

∈-++ᶜˡ : ∀ {Γ A ρ} → (Δ : Ctx) → A ∈[ ρ ] Γ
       → A ∈[ grade-++ᶜˡ ρ Δ ] (Γ ++ᶜ Δ)
∈-++ᶜˡ []        x = x
∈-++ᶜˡ (Δ ∷ B)   x = Tl-∷ (∈-++ᶜˡ Δ x)
∈-++ᶜˡ (Δ ⟨ ρ ⟩) x = Tl-⟨⟩ (∈-++ᶜˡ Δ x)

-- The grade a suffix contributes is associative in the suffix.

grade-++ᶜˡ-assoc : (ρ : R) → (Δ₁ Δ₂ : Ctx)
                 → grade-++ᶜˡ ρ (Δ₁ ++ᶜ Δ₂)
                 ≡ grade-++ᶜˡ (grade-++ᶜˡ ρ Δ₁) Δ₂
grade-++ᶜˡ-assoc ρ Δ₁ []          = refl
grade-++ᶜˡ-assoc ρ Δ₁ (Δ₂ ∷ B)    = grade-++ᶜˡ-assoc ρ Δ₁ Δ₂
grade-++ᶜˡ-assoc ρ Δ₁ (Δ₂ ⟨ ρ' ⟩) =
  cong (_·ᵣ ρ') (grade-++ᶜˡ-assoc ρ Δ₁ Δ₂)

-- Pushing under a concatenated suffix is pushing twice.

∈-++ᶜˡ-assoc : ∀ {Γ A ρ} → (Δ₁ Δ₂ : Ctx) → (x : A ∈[ ρ ] Γ)
             → Tgt-cast (sym (++ᶜ-assoc Γ Δ₁ Δ₂))
                 (grade-++ᶜˡ ρ (Δ₁ ++ᶜ Δ₂) , ∈-++ᶜˡ (Δ₁ ++ᶜ Δ₂) x)
             ≡ (grade-++ᶜˡ (grade-++ᶜˡ ρ Δ₁) Δ₂ , ∈-++ᶜˡ Δ₂ (∈-++ᶜˡ Δ₁ x))

∈-++ᶜˡ-assoc Δ₁ []         x = refl
∈-++ᶜˡ-assoc {Γ} Δ₁ (Δ₂ ∷ B)   x =
  trans (Tgt-cast-irr (sym (++ᶜ-assoc Γ Δ₁ (Δ₂ ∷ B)))
                      (cong (_∷ B) (sym (++ᶜ-assoc Γ Δ₁ Δ₂))) _)
    (trans (Tgt-cast-∷ (sym (++ᶜ-assoc Γ Δ₁ Δ₂)) _)
           (cong Tgt-∷ (∈-++ᶜˡ-assoc Δ₁ Δ₂ x)))
∈-++ᶜˡ-assoc {Γ} Δ₁ (Δ₂ ⟨ ρ' ⟩) x =
  trans (Tgt-cast-irr (sym (++ᶜ-assoc Γ Δ₁ (Δ₂ ⟨ ρ' ⟩)))
                      (cong (_⟨ ρ' ⟩) (sym (++ᶜ-assoc Γ Δ₁ Δ₂))) _)
    (trans (Tgt-cast-⟨⟩ ρ' (sym (++ᶜ-assoc Γ Δ₁ Δ₂)) _)
           (cong (Tgt-⟨⟩ ρ') (∈-++ᶜˡ-assoc Δ₁ Δ₂ x)))

-- A congruence renaming sends a pushed prefix variable to the push of its
-- image: the counterpart of `cong-ren-tgt-r`, and what makes the pushing
-- renaming family natural.

cong-ren-tgt-l : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (Δ : Ctx) → (y : A ∈[ ρ ] Γ)
               → var-tgt (cong-ren {Γ'' = Δ} r) (∈-++ᶜˡ Δ y)
               ≡ (grade-++ᶜˡ (proj₁ (var-tgt r y)) Δ
                 , ∈-++ᶜˡ Δ (proj₂ (var-tgt r y)))

cong-ren-tgt-l r []         y = refl
cong-ren-tgt-l r (Δ ∷ B)    y =
  cong (λ t → proj₁ t , Tl-∷ (proj₂ t)) (cong-ren-tgt-l r Δ y)
cong-ren-tgt-l r (Δ ⟨ ρ' ⟩) y =
  cong (λ t → proj₁ t ·ᵣ ρ' , Tl-⟨⟩ (proj₂ t)) (cong-ren-tgt-l r Δ y)

-- The suffix's contribution is monotone in the variable's own grade, and a
-- bound on it is a bound on that grade: the two directions a push needs, the
-- first to carry a renaming's grade drop under the suffix, the second to read
-- the suffix's locks off a `var`'s bound.

grade-++ᶜˡ-mono : ∀ {ρ ρ'} → (Δ : Ctx) → ρ ≾ᵣ ρ'
                → grade-++ᶜˡ ρ Δ ≾ᵣ grade-++ᶜˡ ρ' Δ
grade-++ᶜˡ-mono []         p = p
grade-++ᶜˡ-mono (Δ ∷ B)    p = grade-++ᶜˡ-mono Δ p
grade-++ᶜˡ-mono (Δ ⟨ ρ' ⟩) p = ·ᵣ-monoˡ-≾ᵣ (grade-++ᶜˡ-mono Δ p)

grade-++ᶜˡ-zeroˡ : ∀ {ρ} → (Δ : Ctx) → grade-++ᶜˡ ρ Δ ≾ᵣ uᵣ → ρ ≾ᵣ uᵣ
grade-++ᶜˡ-zeroˡ []         p = p
grade-++ᶜˡ-zeroˡ (Δ ∷ B)    p = grade-++ᶜˡ-zeroˡ Δ p
grade-++ᶜˡ-zeroˡ (Δ ⟨ ρ' ⟩) p = grade-++ᶜˡ-zeroˡ Δ (≾ᵣ-zero-productˡ p)

-- A concatenation of unit-bounded suffixes is unit-bounded.

ctx-grade-++ᶜ-≾ᵣ : (Δ₁ Δ₂ : Ctx) → ctx-grade Δ₁ ≾ᵣ uᵣ → ctx-grade Δ₂ ≾ᵣ uᵣ
                 → ctx-grade (Δ₁ ++ᶜ Δ₂) ≾ᵣ uᵣ
ctx-grade-++ᶜ-≾ᵣ Δ₁ []          p₁ p₂ = p₁
ctx-grade-++ᶜ-≾ᵣ Δ₁ (Δ₂ ∷ B)    p₁ p₂ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ₂ p₁ p₂
ctx-grade-++ᶜ-≾ᵣ Δ₁ (Δ₂ ⟨ ρ ⟩)  p₁ p₂ =
  ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ₂ p₁ (≾ᵣ-zero-productˡ p₂)))
           (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)) (≾ᵣ-zero-productʳ p₂))

-- At the unit the push contributes the suffix's own grade, which is the grade
-- `split→∈` records.

grade-++ᶜˡ-uᵣ : (Δ : Ctx) → grade-++ᶜˡ uᵣ Δ ≡ ctx-grade Δ
grade-++ᶜˡ-uᵣ []         = refl
grade-++ᶜˡ-uᵣ (Δ ∷ B)    = grade-++ᶜˡ-uᵣ Δ
grade-++ᶜˡ-uᵣ (Δ ⟨ ρ' ⟩) = cong (_·ᵣ ρ') (grade-++ᶜˡ-uᵣ Δ)

-- The variable a `Γ₁ ∷ B , Γ₂` splitting names is `B` pushed under `Γ₂`.

split→∈-∈-++ᶜˡ : (Γ₁ : Ctx) → (B : VType) → (Γ₂ : Ctx)
               → _≡_ {A = Tgt ((Γ₁ ∷ B) ++ᶜ Γ₂) B}
                   (ctx-grade Γ₂ , split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
                   (grade-++ᶜˡ uᵣ Γ₂ , ∈-++ᶜˡ {Γ = Γ₁ ∷ B} Γ₂ (Hd {Γ = Γ₁}))
split→∈-∈-++ᶜˡ Γ₁ B []         = refl
split→∈-∈-++ᶜˡ Γ₁ B (Γ₂ ∷ C)   =
  cong (λ t → proj₁ t , Tl-∷ (proj₂ t)) (split→∈-∈-++ᶜˡ Γ₁ B Γ₂)
split→∈-∈-++ᶜˡ Γ₁ B (Γ₂ ⟨ ρ ⟩) =
  cong (λ t → proj₁ t ·ᵣ ρ , Tl-⟨⟩ (proj₂ t)) (split→∈-∈-++ᶜˡ Γ₁ B Γ₂)

-- Pushing a prefix variable under a suffix commutes with pushing a suffix
-- variable under a prefix: the two injections meet in the middle context.

∈-++ᶜˡ-++ᶜʳ : ∀ {A ρ} → (Γ Γ₀ Δ : Ctx) → (y : A ∈[ ρ ] Γ₀)
            → Tgt-cast (++ᶜ-assoc Γ Γ₀ Δ)
                (grade-++ᶜˡ ρ Δ , ∈-++ᶜˡ {Γ = Γ ++ᶜ Γ₀} Δ (∈-++ᶜʳ {Γ = Γ} y))
            ≡ (grade-++ᶜˡ ρ Δ , ∈-++ᶜʳ {Γ = Γ} (∈-++ᶜˡ {Γ = Γ₀} Δ y))

∈-++ᶜˡ-++ᶜʳ Γ Γ₀ []         y = refl
∈-++ᶜˡ-++ᶜʳ Γ Γ₀ (Δ ∷ B)    y =
  trans (Tgt-cast-∷ (++ᶜ-assoc Γ Γ₀ Δ) _)
        (cong Tgt-∷ (∈-++ᶜˡ-++ᶜʳ Γ Γ₀ Δ y))
∈-++ᶜˡ-++ᶜʳ Γ Γ₀ (Δ ⟨ ρ' ⟩) y =
  trans (Tgt-cast-⟨⟩ ρ' (++ᶜ-assoc Γ Γ₀ Δ) _)
        (cong (Tgt-⟨⟩ ρ') (∈-++ᶜˡ-++ᶜʳ Γ Γ₀ Δ y))

-- Reading a `Tgt-cast` equation in the other direction.

Tgt-cast-flip : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Tgt Γ A) → (t' : Tgt Γ' A)
              → Tgt-cast e t ≡ t' → Tgt-cast (sym e) t' ≡ t
Tgt-cast-flip refl t t' q = sym q

Tgt-cast-flip⁻ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Tgt Γ' A) → (t' : Tgt Γ A)
               → Tgt-cast (sym e) t ≡ t' → Tgt-cast e t' ≡ t
Tgt-cast-flip⁻ refl t t' q = sym q

-- THE PUSHING RENAMING
--
-- The renaming that weakens a context by a whole suffix. It exists only when
-- the suffix's grade is bounded by the unit — each of its locks has to be
-- crossed, which is `⟨⟩-≤-ren` at that lock's own grade.

push-ren : ∀ {Γ₀} → (Δ : Ctx) → ctx-grade Δ ≾ᵣ uᵣ → Ren [] Γ₀ (Γ₀ ++ᶜ Δ)
push-ren []         p = id-ren
push-ren (Δ ∷ B)    p = wk-ren ∘ʳ push-ren Δ p
push-ren (Δ ⟨ ρ' ⟩) p =
  (⟨⟩-≤-ren (≾ᵣ-zero-productʳ p) ∘ʳ ⟨⟩-η⁻¹-ren)
    ∘ʳ push-ren Δ (≾ᵣ-zero-productˡ p)

-- It acts as `∈-++ᶜˡ`, which is what pins it down up to `_≐ʳ_`.

push-ren-tgt : ∀ {Γ₀ A ρ} → (Δ : Ctx) → (p : ctx-grade Δ ≾ᵣ uᵣ)
             → (y : A ∈[ ρ ] Γ₀)
             → var-tgt (push-ren {Γ₀} Δ p) y ≡ (grade-++ᶜˡ ρ Δ , ∈-++ᶜˡ Δ y)
push-ren-tgt []         p y = refl
push-ren-tgt (Δ ∷ B)    p y = cong Tgt-∷ (push-ren-tgt Δ p y)
push-ren-tgt (Δ ⟨ ρ' ⟩) p y =
  cong (Tgt-⟨⟩ ρ') (push-ren-tgt Δ (≾ᵣ-zero-productˡ p) y)

-- At a one-entry suffix it is the weakening, resp. the lock crossing — the two
-- shapes the environment's telescope zones present.

push-ren-∷ : ∀ {Γ₀ B} → (p : ctx-grade ([] ∷ B) ≾ᵣ uᵣ)
           → push-ren {Γ₀} ([] ∷ B) p ≐ʳ wk-ren
push-ren-∷ p = ∘ʳ-identityʳ-≐ wk-ren

push-ren-⟨⟩ : ∀ {Γ₀ ρ} → (p : ctx-grade ([] ⟨ ρ ⟩) ≾ᵣ uᵣ) → (p' : ρ ≾ᵣ uᵣ)
            → push-ren {Γ₀} ([] ⟨ ρ ⟩) p ≐ʳ (⟨⟩-≤-ren p' ∘ʳ ⟨⟩-η⁻¹-ren)
push-ren-⟨⟩ p p' =
  ≐ʳ-trans (∘ʳ-identityʳ-≐ _) (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ p') ≐ʳ-refl)

-- Pushing is natural: renaming the prefix and then pushing is pushing and then
-- renaming the prefix under the suffix.

push-ren-nat : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (Δ : Ctx)
             → (p : ctx-grade Δ ≾ᵣ uᵣ)
             → (cong-ren {Γ'' = Δ} r ∘ʳ push-ren Δ p) ≐ʳ (push-ren Δ p ∘ʳ r)
push-ren-nat r Δ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (y : A ∈[ σ ] _) → _
    go y =
      trans (cong (var-tgt′ (cong-ren {Γ'' = Δ} r)) (push-ren-tgt Δ p y))
        (trans (cong-ren-tgt-l r Δ y)
               (sym (push-ren-tgt Δ p (proj₂ (var-tgt r y)))))

-- Pushing by a concatenated suffix is pushing twice, the contexts differing by
-- associativity.

push-ren-++ᶜ : ∀ {Γ₀} → (Δ₁ Δ₂ : Ctx)
             → (p : ctx-grade (Δ₁ ++ᶜ Δ₂) ≾ᵣ uᵣ)
             → (p₁ : ctx-grade Δ₁ ≾ᵣ uᵣ) → (p₂ : ctx-grade Δ₂ ≾ᵣ uᵣ)
             → (eq-ren (sym (++ᶜ-assoc Γ₀ Δ₁ Δ₂)) ∘ʳ push-ren (Δ₁ ++ᶜ Δ₂) p)
             ≐ʳ (push-ren Δ₂ p₂ ∘ʳ push-ren {Γ₀} Δ₁ p₁)
push-ren-++ᶜ {Γ₀} Δ₁ Δ₂ p p₁ p₂ = mk≐ʳ go
  where
    e = sym (++ᶜ-assoc Γ₀ Δ₁ Δ₂)

    go : ∀ {A σ} → (y : A ∈[ σ ] Γ₀) → _
    go y =
      trans (cong (var-tgt′ (eq-ren e)) (push-ren-tgt (Δ₁ ++ᶜ Δ₂) p y))
        (trans (eq-ren-tgt e (∈-++ᶜˡ (Δ₁ ++ᶜ Δ₂) y))
          (trans (∈-++ᶜˡ-assoc Δ₁ Δ₂ y)
            (sym (trans (cong (var-tgt′ (push-ren Δ₂ p₂)) (push-ren-tgt Δ₁ p₁ y))
                        (push-ren-tgt Δ₂ p₂ (∈-++ᶜˡ Δ₁ y))))))

-- SUFFIX EXTENSION
--
-- `cong-ren` recurses on the suffix, so it respects `_≐ʳ_` and commutes with
-- composition up to it (`cong-∷-ren (r ∘ʳ r')` and `cong-∷-ren r ∘ʳ cong-∷-ren r'`
-- are distinct renamings acting alike).

cong-∷-ren-≐ : ∀ {Γ Γ' A} {r r' : Ren [] Γ Γ'}
             → r ≐ʳ r' → cong-∷-ren {A = A} r ≐ʳ cong-∷-ren r'
cong-∷-ren-≐ h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (at h x)

cong-⟨⟩-ren-≐ : ∀ {Γ Γ' ρ} {r r' : Ren [] Γ Γ'}
              → r ≐ʳ r' → cong-⟨⟩-ren {ρ = ρ} r ≐ʳ cong-⟨⟩-ren r'
cong-⟨⟩-ren-≐ {ρ = ρ} h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (at h x)

cong-ren-≐ : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'} → (Γ₀ : Ctx)
           → r ≐ʳ r' → cong-ren {Γ'' = Γ₀} r ≐ʳ cong-ren r'
cong-ren-≐ []         h = h
cong-ren-≐ (Γ₀ ∷ A)   h = cong-∷-ren-≐ (cong-ren-≐ Γ₀ h)
cong-ren-≐ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-ren-≐ (cong-ren-≐ Γ₀ h)

cong-∷-ren-∘-≐ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
               → cong-∷-ren {A = A} (r₂ ∘ʳ r₁)
               ≐ʳ (cong-∷-ren r₂ ∘ʳ cong-∷-ren r₁)
cong-∷-ren-∘-≐ r₂ r₁ = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = refl

cong-⟨⟩-ren-∘-≐ : ∀ {Γ Γ' Γ'' ρ} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
                → cong-⟨⟩-ren {ρ = ρ} (r₂ ∘ʳ r₁)
                ≐ʳ (cong-⟨⟩-ren r₂ ∘ʳ cong-⟨⟩-ren r₁)
cong-⟨⟩-ren-∘-≐ {ρ = ρ} r₂ r₁ = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = refl

-- Weakening is natural: renaming the prefix and then weakening is weakening
-- and then renaming under the new binder.

wk-ren-nat-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ')
             → (cong-∷-ren {A = B} r ∘ʳ wk-ren) ≐ʳ (wk-ren ∘ʳ r)
wk-ren-nat-≐ r = mk≐ʳ (λ y → refl)

cong-ren-∘-≐ : ∀ {Γ Γ' Γ''} → (Γ₀ : Ctx)
             → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → cong-ren {Γ'' = Γ₀} (r₂ ∘ʳ r₁)
             ≐ʳ (cong-ren {Γ'' = Γ₀} r₂ ∘ʳ cong-ren {Γ'' = Γ₀} r₁)
cong-ren-∘-≐ []         r₂ r₁ = ≐ʳ-refl
cong-ren-∘-≐ (Γ₀ ∷ A)   r₂ r₁ =
  ≐ʳ-trans (cong-∷-ren-≐ (cong-ren-∘-≐ Γ₀ r₂ r₁))
           (cong-∷-ren-∘-≐ (cong-ren {Γ'' = Γ₀} r₂) (cong-ren {Γ'' = Γ₀} r₁))
cong-ren-∘-≐ (Γ₀ ⟨ ρ ⟩) r₂ r₁ =
  ≐ʳ-trans (cong-⟨⟩-ren-≐ (cong-ren-∘-≐ Γ₀ r₂ r₁))
           (cong-⟨⟩-ren-∘-≐ (cong-ren {Γ'' = Γ₀} r₂) (cong-ren {Γ'' = Γ₀} r₁))

------------------------------------------------------------------------
-- THE CELL AN `unbox` NAMES
--
-- Reduction consults an `unbox` only through `unbox⇒var`, and `unbox-lookup`
-- only through this — so this, and not the stored renaming or boxed value, is
-- what `_≐ᶜ_` compares below.
------------------------------------------------------------------------

unbox-tgt : ∀ {Γ A ρ Δ} → Ren [] (Δ ⟨ ρ ⟩) Γ → Δ ⊢V⦂ [ ρ ] A → Tgt Γ ([ ρ ] A)
unbox-tgt w V = proj₁ (unbox⇒var w V) , proj₁ (proj₂ (unbox⇒var w V))

-- `_≐ʳ_`-equal renamings name the same cell: the boxed value is seen only as a
-- variable (`grad-typ⇒var`), which both consult alike.

unbox-tgt-≐ : ∀ {Γ A ρ Δ} {w w' : Ren [] (Δ ⟨ ρ ⟩) Γ}
            → w ≐ʳ w' → (V : Δ ⊢V⦂ [ ρ ] A)
            → unbox-tgt w V ≡ unbox-tgt w' V
unbox-tgt-≐ hw V with grad-typ⇒var V
... | _ , y , f , refl = at hw (Tl-⟨⟩ y)

-- Renaming an `unbox` relocates its cell — definitionally, since `var-rename`
-- of a composite is the composite.

unbox-tgt-∘ : ∀ {Γ Γ' A ρ Δ} → (r : Ren [] Γ Γ') → (w : Ren [] (Δ ⟨ ρ ⟩) Γ)
            → (V : Δ ⊢V⦂ [ ρ ] A)
            → unbox-tgt (r ∘ʳ w) V ≡ var-tgt′ r (unbox-tgt w V)
unbox-tgt-∘ r w V with grad-typ⇒var V
... | _ , y , f , refl = refl

------------------------------------------------------------------------
-- TERMS UP TO IRRELEVANT STORED DATA
--
-- A term is *not* determined by its shape: `var` stores a grade bound,
-- `coerce` an effect ordering, and `unbox` a whole renaming. The first two are
-- irrelevant (`≾ᵣ-irrelevant`, `≾ₑ-irrelevant`); the third is relevant only up
-- to `_≐ʳ_`, since reduction consults it solely through `unbox⇒var`.
--
-- So the laws below cannot be stated at `_≡_`: renaming along `r₂ ∘ʳ r₁`
-- stores that composite in every `unbox` node, where renaming twice stores
-- `r₂ ∘ʳ (r₁ ∘ʳ w)`. The two are `_≐ʳ_`-equal, never equal. `_≐ᵛ_`/`_≐ᶜ_`
-- below are the congruence that ignores exactly this data.
--
-- `EquationalTheory` is insensitive to the `coerce` witness but not to the
-- other two, so it cannot relate those `unbox` nodes either. Aligning the two
-- is on the cleanup list in `notes/adequacy-plan.md`.
------------------------------------------------------------------------

infix 4 _≐ᵛ_
infix 4 _≐ᶜ_

mutual

  data _≐ᵛ_ {Γ : Ctx} : ∀ {A} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set where

    var-≐   : ∀ {A ρ} {f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Γ}
            → var f x ≐ᵛ var f' x

    const-≐ : ∀ {b} {c : BaseConstants b} → const c ≐ᵛ const c

    ⋆-≐     : ⋆ ≐ᵛ ⋆

    pair-≐  : ∀ {A B} {V V' : Γ ⊢V⦂ A} {W W' : Γ ⊢V⦂ B}
            → V ≐ᵛ V' → W ≐ᵛ W' → ⦉ V , W ⦊ ≐ᵛ ⦉ V' , W' ⦊

    lam-≐   : ∀ {A C} {M M' : Γ ∷ A ⊢C⦂ C}
            → M ≐ᶜ M' → lam M ≐ᵛ lam M'

  data _≐ᶜ_ {Γ : Ctx} : ∀ {C} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    return-≐  : ∀ {A} {V V' : Γ ⊢V⦂ A}
              → V ≐ᵛ V' → return V ≐ᶜ return V'

    seq-≐     : ∀ {A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
                  {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
              → M ≐ᶜ M' → N ≐ᶜ N' → (M ⨟ N) ≐ᶜ (M' ⨟ N')

    app-≐     : ∀ {A C} {V V' : Γ ⊢V⦂ A ⇒ C} {W W' : Γ ⊢V⦂ A}
              → V ≐ᵛ V' → W ≐ᵛ W' → (V · W) ≐ᶜ (V' · W')

    match-≐   : ∀ {A B C} {V V' : Γ ⊢V⦂ A |×| B} {M M' : Γ ∷ A ∷ B ⊢C⦂ C}
              → V ≐ᵛ V' → M ≐ᶜ M'
              → (match V `in M) ≐ᶜ (match V' `in M')

    absurd-≐  : ∀ {C} {V V' : Γ ⊢V⦂ Empty}
              → V ≐ᵛ V' → absurd {C = C} V ≐ᶜ absurd V'

    perform-≐ : ∀ {A ε} {op : Op} {V V' : Γ ⊢V⦂ type-of-gtype (param op)}
                  {M M' : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                            ⊢C⦂ A ‼ ε}
              → V ≐ᵛ V' → M ≐ᶜ M'
              → perform op V M ≐ᶜ perform op V' M'

    delay-≐   : ∀ {A ε} {τ : ℕ} {M M' : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
              → M ≐ᶜ M' → delay τ M ≐ᶜ delay τ M'

    handle-≐  : ∀ {A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
                  {H H' : (op : Op) → (ε'' : E) →
                            Γ ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε'')
                            ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
                  {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
              → M ≐ᶜ M'
              → (∀ op ε'' → H op ε'' ≐ᶜ H' op ε'')
              → N ≐ᶜ N'
              → (handle M `with H `in N) ≐ᶜ (handle M' `with H' `in N')

    -- the two nodes storing data that matters only up to equivalence

    -- `unbox` is compared at the *cell* it names, not at the renaming and boxed
    -- value it stores: substitution renormalises those (`unbox⇒var` then
    -- `unbox-var`), so demanding they agree would make substitution lemmas false.

    unbox-≐   : ∀ {A C ρ Δ Δ'} {w : Ren [] (Δ ⟨ ρ ⟩) Γ} {w' : Ren [] (Δ' ⟨ ρ ⟩) Γ}
                  {V : Δ ⊢V⦂ [ ρ ] A} {V' : Δ' ⊢V⦂ [ ρ ] A}
                  {M M' : Γ ∷ A ⊢C⦂ C}
              → unbox-tgt w V ≡ unbox-tgt w' V' → M ≐ᶜ M'
              → unbox w V M ≐ᶜ unbox w' V' M'

    coerce-≐  : ∀ {A ε ε'} {p p' : ε ≾ₑ ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
              → M ≐ᶜ M' → coerce p M ≐ᶜ coerce p' M'

    box-≐     : ∀ {A C ρ} {V V' : Γ ⟨ ρ ⟩ ⊢V⦂ A} {M M' : Γ ∷ [ ρ ] A ⊢C⦂ C}
              → V ≐ᵛ V' → M ≐ᶜ M' → box V M ≐ᶜ box V' M'

-- Reflexivity, symmetry and transitivity.

mutual

  ≐ᵛ-refl : ∀ {Γ A} → (V : Γ ⊢V⦂ A) → V ≐ᵛ V
  ≐ᵛ-refl (var f x)   = var-≐
  ≐ᵛ-refl (const c)   = const-≐
  ≐ᵛ-refl ⋆           = ⋆-≐
  ≐ᵛ-refl ⦉ V , W ⦊    = pair-≐ (≐ᵛ-refl V) (≐ᵛ-refl W)
  ≐ᵛ-refl (lam M)     = lam-≐ (≐ᶜ-refl M)

  ≐ᶜ-refl : ∀ {Γ C} → (M : Γ ⊢C⦂ C) → M ≐ᶜ M
  ≐ᶜ-refl (return V)              = return-≐ (≐ᵛ-refl V)
  ≐ᶜ-refl (M ⨟ N)                 = seq-≐ (≐ᶜ-refl M) (≐ᶜ-refl N)
  ≐ᶜ-refl (V · W)                 = app-≐ (≐ᵛ-refl V) (≐ᵛ-refl W)
  ≐ᶜ-refl (match V `in M)         = match-≐ (≐ᵛ-refl V) (≐ᶜ-refl M)
  ≐ᶜ-refl (absurd V)              = absurd-≐ (≐ᵛ-refl V)
  ≐ᶜ-refl (perform op V M)        = perform-≐ (≐ᵛ-refl V) (≐ᶜ-refl M)
  ≐ᶜ-refl (delay τ M)             = delay-≐ (≐ᶜ-refl M)
  ≐ᶜ-refl (handle M `with H `in N) =
    handle-≐ (≐ᶜ-refl M) (λ op ε'' → ≐ᶜ-refl (H op ε'')) (≐ᶜ-refl N)
  ≐ᶜ-refl (unbox w V M)           = unbox-≐ refl (≐ᶜ-refl M)
  ≐ᶜ-refl (box V M)               = box-≐ (≐ᵛ-refl V) (≐ᶜ-refl M)
  ≐ᶜ-refl (coerce p M)            = coerce-≐ (≐ᶜ-refl M)

mutual

  ≐ᵛ-trans : ∀ {Γ A} {V V' V'' : Γ ⊢V⦂ A} → V ≐ᵛ V' → V' ≐ᵛ V'' → V ≐ᵛ V''
  ≐ᵛ-trans var-≐            var-≐              = var-≐
  ≐ᵛ-trans const-≐          const-≐            = const-≐
  ≐ᵛ-trans ⋆-≐              ⋆-≐                = ⋆-≐
  ≐ᵛ-trans (pair-≐ eV eW)   (pair-≐ eV' eW')   =
    pair-≐ (≐ᵛ-trans eV eV') (≐ᵛ-trans eW eW')
  ≐ᵛ-trans (lam-≐ eM)       (lam-≐ eM')        = lam-≐ (≐ᶜ-trans eM eM')

  ≐ᶜ-trans : ∀ {Γ C} {M M' M'' : Γ ⊢C⦂ C} → M ≐ᶜ M' → M' ≐ᶜ M'' → M ≐ᶜ M''
  ≐ᶜ-trans (return-≐ eV)      (return-≐ eV')      = return-≐ (≐ᵛ-trans eV eV')
  ≐ᶜ-trans (seq-≐ eM eN)      (seq-≐ eM' eN')     =
    seq-≐ (≐ᶜ-trans eM eM') (≐ᶜ-trans eN eN')
  ≐ᶜ-trans (app-≐ eV eW)      (app-≐ eV' eW')     =
    app-≐ (≐ᵛ-trans eV eV') (≐ᵛ-trans eW eW')
  ≐ᶜ-trans (match-≐ eV eM)    (match-≐ eV' eM')   =
    match-≐ (≐ᵛ-trans eV eV') (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (absurd-≐ eV)      (absurd-≐ eV')      = absurd-≐ (≐ᵛ-trans eV eV')
  ≐ᶜ-trans (perform-≐ eV eM)  (perform-≐ eV' eM') =
    perform-≐ (≐ᵛ-trans eV eV') (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (delay-≐ eM)       (delay-≐ eM')       = delay-≐ (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (handle-≐ eM eH eN) (handle-≐ eM' eH' eN') =
    handle-≐ (≐ᶜ-trans eM eM')
             (λ op ε'' → ≐ᶜ-trans (eH op ε'') (eH' op ε''))
             (≐ᶜ-trans eN eN')
  ≐ᶜ-trans (unbox-≐ hw eM)    (unbox-≐ hw' eM')   =
    unbox-≐ (trans hw hw') (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (coerce-≐ eM)      (coerce-≐ eM')      = coerce-≐ (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (box-≐ eV eM)      (box-≐ eV' eM')     =
    box-≐ (≐ᵛ-trans eV eV') (≐ᶜ-trans eM eM')

mutual

  ≐ᵛ-sym : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≐ᵛ V' → V' ≐ᵛ V
  ≐ᵛ-sym var-≐            = var-≐
  ≐ᵛ-sym const-≐          = const-≐
  ≐ᵛ-sym ⋆-≐              = ⋆-≐
  ≐ᵛ-sym (pair-≐ eV eW)   = pair-≐ (≐ᵛ-sym eV) (≐ᵛ-sym eW)
  ≐ᵛ-sym (lam-≐ eM)       = lam-≐ (≐ᶜ-sym eM)

  ≐ᶜ-sym : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≐ᶜ M' → M' ≐ᶜ M
  ≐ᶜ-sym (return-≐ eV)      = return-≐ (≐ᵛ-sym eV)
  ≐ᶜ-sym (seq-≐ eM eN)      = seq-≐ (≐ᶜ-sym eM) (≐ᶜ-sym eN)
  ≐ᶜ-sym (app-≐ eV eW)      = app-≐ (≐ᵛ-sym eV) (≐ᵛ-sym eW)
  ≐ᶜ-sym (match-≐ eV eM)    = match-≐ (≐ᵛ-sym eV) (≐ᶜ-sym eM)
  ≐ᶜ-sym (absurd-≐ eV)      = absurd-≐ (≐ᵛ-sym eV)
  ≐ᶜ-sym (perform-≐ eV eM)  = perform-≐ (≐ᵛ-sym eV) (≐ᶜ-sym eM)
  ≐ᶜ-sym (delay-≐ eM)       = delay-≐ (≐ᶜ-sym eM)
  ≐ᶜ-sym (handle-≐ eM eH eN) =
    handle-≐ (≐ᶜ-sym eM) (λ op ε'' → ≐ᶜ-sym (eH op ε'')) (≐ᶜ-sym eN)
  ≐ᶜ-sym (unbox-≐ hw eM)    = unbox-≐ (sym hw) (≐ᶜ-sym eM)
  ≐ᶜ-sym (coerce-≐ eM)      = coerce-≐ (≐ᶜ-sym eM)
  ≐ᶜ-sym (box-≐ eV eM)      = box-≐ (≐ᵛ-sym eV) (≐ᶜ-sym eM)

-- The eternal restriction is compositional by definition.

restrict-ren-∘-≐ : ∀ {Γ Γ' Γ''} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
                 → restrict-ren (r₂ ∘ʳ r₁)
                 ≐ʳ (restrict-ren r₂ ∘ʳ restrict-ren r₁)
restrict-ren-∘-≐ r₂ r₁ = ≐ʳ-refl

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION
--
-- `restrict-ren` recurses on the *renaming*, so `restrict-ren-≐` is not a
-- congruence of a function of `var-tgt`. It goes through the *reflection* of a
-- restricted variable, `∈-ᴱ⁻`: restricting commutes with it (`restrict-tgt⁻`),
-- so `var-tgt (restrict-ren r) x` is determined by `var-tgt r` up to
-- injectivity of `∈-ᴱ⁻`.
--
-- Everything is stated in terms of `∈-ᴱ⁻` and never `∈-ᴱ`: both split on
-- `eternal?`, but a goal mentioning `∈-ᴱ` blocks the `with`-abstraction on that
-- scrutinee, whereas `∈-ᴱ⁻`'s own recursion does not.
------------------------------------------------------------------------

-- The variable of `Γ` that a variable of `Γ ᴱ` came from, on `Tgt`s.

∈-ᴱ⁻ : (Γ : Ctx) → ∀ {A ρ} → A ∈[ ρ ] Γ ᴱ → Tgt Γ A
∈-ᴱ⁻ []        x with x
... | ()
∈-ᴱ⁻ (Γ ∷ B)   x with eternal? B
∈-ᴱ⁻ (Γ ∷ B)   Hd       | yes _ = uᵣ , Hd
∈-ᴱ⁻ (Γ ∷ B)   (Tl-∷ y) | yes _ = proj₁ (∈-ᴱ⁻ Γ y) , Tl-∷ (proj₂ (∈-ᴱ⁻ Γ y))
∈-ᴱ⁻ (Γ ∷ B)   x        | no  _ = proj₁ (∈-ᴱ⁻ Γ x) , Tl-∷ (proj₂ (∈-ᴱ⁻ Γ x))
∈-ᴱ⁻ (Γ ⟨ ρ ⟩) x =
  proj₁ (∈-ᴱ⁻ Γ x) ·ᵣ ρ , Tl-⟨⟩ (proj₂ (∈-ᴱ⁻ Γ x))

∈-ᴱ⁻′ : (Γ : Ctx) → ∀ {A} → Tgt (Γ ᴱ) A → Tgt Γ A
∈-ᴱ⁻′ Γ (ρ , x) = ∈-ᴱ⁻ Γ x

-- Forcing a `with eternal?`-defined function to reduce: `rewrite`ing the
-- scrutinee is cleaner than unfold lemmas whose statements are themselves
-- `_ᴱ`-stuck. (Also in `Interpretation.SubstitutionCoherence`; see the cleanup
-- list in `notes/adequacy-plan.md`.)

eternal?-yes : ∀ {A} → (et : Eternal A) → eternal? A ≡ yes et
eternal?-yes {A} et with eternal? A
... | yes et' = cong yes (eternal-irrelevant et' et)
... | no ¬et  = ⊥-elim (¬et et)

eternal?-no : ∀ {A} → (¬et : ¬ Eternal A) → eternal? A ≡ no ¬et
eternal?-no {A} ¬et with eternal? A
... | yes et  = ⊥-elim (¬et et)
... | no ¬et' = cong no (fun-ext (λ e → ⊥-elim (¬et e)))

-- Reflection undoes `∈-ᴱ`.

∈-ᴱ⁻-∈-ᴱ : (Γ : Ctx) → ∀ {A ρ} → (et : Eternal A) → (z : A ∈[ ρ ] Γ)
         → ∈-ᴱ⁻ Γ (∈-ᴱ et z) ≡ (ρ , z)

∈-ᴱ⁻-∈-ᴱ (Γ ∷ B)   et Hd       rewrite eternal?-yes et = refl
∈-ᴱ⁻-∈-ᴱ (Γ ∷ B)   et (Tl-∷ z) with eternal? B
... | yes _ = cong (λ w → proj₁ w , Tl-∷ (proj₂ w)) (∈-ᴱ⁻-∈-ᴱ Γ et z)
... | no  _ = cong (λ w → proj₁ w , Tl-∷ (proj₂ w)) (∈-ᴱ⁻-∈-ᴱ Γ et z)
∈-ᴱ⁻-∈-ᴱ (Γ ⟨ ρ₀ ⟩) et (Tl-⟨⟩ z) =
  cong (λ w → proj₁ w ·ᵣ ρ₀ , Tl-⟨⟩ (proj₂ w)) (∈-ᴱ⁻-∈-ᴱ Γ et z)

-- It is injective: distinct variables of `Γ ᴱ` come from distinct variables.

∈-ᴱ⁻-inj : (Γ : Ctx) → ∀ {A} → (t t' : Tgt (Γ ᴱ) A)
         → ∈-ᴱ⁻′ Γ t ≡ ∈-ᴱ⁻′ Γ t' → t ≡ t'

∈-ᴱ⁻-inj []        (_ , x) _        e with x
... | ()
∈-ᴱ⁻-inj (Γ ∷ B)   t       t'       e with eternal? B
∈-ᴱ⁻-inj (Γ ∷ B) (_ , Hd)      (_ , Hd)      e | yes _ = refl
∈-ᴱ⁻-inj (Γ ∷ B) (_ , Hd)      (_ , Tl-∷ y') e | yes _ with ∈-ᴱ⁻ Γ y'
... | _ , _ with e
... | ()
∈-ᴱ⁻-inj (Γ ∷ B) (_ , Tl-∷ y) (_ , Hd)       e | yes _ with ∈-ᴱ⁻ Γ y
... | _ , _ with e
... | ()
∈-ᴱ⁻-inj (Γ ∷ B) (ρ , Tl-∷ y) (ρ' , Tl-∷ y') e | yes _ =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z))
       (∈-ᴱ⁻-inj Γ (ρ , y) (ρ' , y') (∷-inj e))
  where
    ∷-inj : ∀ {A ρ₁ ρ₂} {z₁ : A ∈[ ρ₁ ] Γ} {z₂ : A ∈[ ρ₂ ] Γ}
          → _≡_ {A = Tgt (Γ ∷ B) A} (ρ₁ , Tl-∷ z₁) (ρ₂ , Tl-∷ z₂)
          → _≡_ {A = Tgt Γ A} (ρ₁ , z₁) (ρ₂ , z₂)
    ∷-inj refl = refl
∈-ᴱ⁻-inj (Γ ∷ B) (ρ , x)      (ρ' , x')      e | no _ =
  ∈-ᴱ⁻-inj Γ (ρ , x) (ρ' , x') (∷-inj e)
  where
    ∷-inj : ∀ {A ρ₁ ρ₂} {z₁ : A ∈[ ρ₁ ] Γ} {z₂ : A ∈[ ρ₂ ] Γ}
          → _≡_ {A = Tgt (Γ ∷ B) A} (ρ₁ , Tl-∷ z₁) (ρ₂ , Tl-∷ z₂)
          → _≡_ {A = Tgt Γ A} (ρ₁ , z₁) (ρ₂ , z₂)
    ∷-inj refl = refl
∈-ᴱ⁻-inj (Γ ⟨ ρ₀ ⟩) (ρ , x)   (ρ' , x')      e =
  ∈-ᴱ⁻-inj Γ (ρ , x) (ρ' , x') (⟨⟩-inj e)
  where
    ⟨⟩-inj : ∀ {A ρ₁ ρ₂} {z₁ : A ∈[ ρ₁ ] Γ} {z₂ : A ∈[ ρ₂ ] Γ}
           → _≡_ {A = Tgt (Γ ⟨ ρ₀ ⟩) A} (ρ₁ ·ᵣ ρ₀ , Tl-⟨⟩ z₁) (ρ₂ ·ᵣ ρ₀ , Tl-⟨⟩ z₂)
           → _≡_ {A = Tgt Γ A} (ρ₁ , z₁) (ρ₂ , z₂)
    ⟨⟩-inj refl = refl

-- Restricting commutes with reflection. Induction on the renaming.

restrict-tgt⁻ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → ∀ {A ρ} → (x : A ∈[ ρ ] Γ ᴱ)
              → ∈-ᴱ⁻′ Γ' (var-tgt (restrict-ren r) x)
              ≡ var-tgt′ r (∈-ᴱ⁻ Γ x)

restrict-tgt⁻ id-ren x = refl

restrict-tgt⁻ (r₂ ∘ʳ r₁) x =
  trans (restrict-tgt⁻ r₂ (proj₂ (var-tgt (restrict-ren r₁) x)))
        (cong (var-tgt′ r₂) (restrict-tgt⁻ r₁ x))

restrict-tgt⁻ (wk-ren {A = B}) x with eternal? B
... | yes _ = refl
... | no  _ = refl

restrict-tgt⁻ {Γ' = Γ'} (var-ren {A = B} p z) x with eternal? B
restrict-tgt⁻ {Γ' = Γ'} (var-ren {A = B} p z) Hd       | yes etB =
  ∈-ᴱ⁻-∈-ᴱ Γ' etB z
restrict-tgt⁻ (var-ren {A = B} p z) (Tl-∷ x) | yes _ = refl
restrict-tgt⁻ (var-ren {A = B} p z) x        | no  _ = refl

restrict-tgt⁻ ⟨⟩-η-ren     x = refl
restrict-tgt⁻ ⟨⟩-μ-ren     x = refl
restrict-tgt⁻ (⟨⟩-≤-ren _) x = refl

-- the one renaming whose source carries no lock and whose `var-rename` still
-- splits on the variable, so the reflected variable has to be exposed
restrict-tgt⁻ {Γ = Γ} ⟨⟩-η⁻¹-ren x with ∈-ᴱ⁻ Γ x
... | _ , Hd      = refl
... | _ , Tl-∷ y  = refl
... | _ , Tl-⟨⟩ y = refl

restrict-tgt⁻ (cong-∷-ren {A = B} r) x with eternal? B
restrict-tgt⁻ (cong-∷-ren {A = B} r) Hd       | yes _ = refl
restrict-tgt⁻ (cong-∷-ren {A = B} r) (Tl-∷ x) | yes _ =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (restrict-tgt⁻ r x)
restrict-tgt⁻ (cong-∷-ren {A = B} r) x        | no  _ =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (restrict-tgt⁻ r x)

restrict-tgt⁻ (cong-⟨⟩-ren {ρ = ρ₀} r) x =
  cong (λ z → proj₁ z ·ᵣ ρ₀ , Tl-⟨⟩ (proj₂ z)) (restrict-tgt⁻ r x)

restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) x with eternal? B
restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) Hd       | yes _ = refl
restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) (Tl-∷ x) | yes _ = refl
restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) x        | no ¬etB = ⊥-elim (¬etB etB)

-- the restriction drops the introduced lock, so both sides are the reflected
-- variable pushed under it
restrict-tgt⁻ (⟨⟩-ext-ctx _ _) x = refl

-- The eternal restriction respects acting alike.

restrict-ren-≐ : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'}
               → r ≐ʳ r' → restrict-ren r ≐ʳ restrict-ren r'

restrict-ren-≐ {Γ} {Γ'} {r} {r'} h = mk≐ʳ go
  where
    go : ∀ {A ρ} → (x : A ∈[ ρ ] Γ ᴱ)
       → var-tgt (restrict-ren r) x ≡ var-tgt (restrict-ren r') x
    go x =
      ∈-ᴱ⁻-inj Γ' _ _
        (trans (restrict-tgt⁻ r x)
          (trans (cong (var-tgt′ r) refl)
            (trans (at-tgt (∈-ᴱ⁻ Γ x)) (sym (restrict-tgt⁻ r' x)))))
      where
        at-tgt : ∀ {A} → (t : Tgt Γ A) → var-tgt′ r t ≡ var-tgt′ r' t
        at-tgt (_ , y) = at h y

-- Renaming a variable is the variable the renaming sends it to: `var-tgt`
-- records the position, and the grade bound it recomputes is invisible to
-- `_≐ᵛ_`. Stated at an arbitrary bound so that the caller may present the
-- result with whichever bound its own typing supplies.

var-ren-≐ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (x : A ∈[ ρ ] Γ)
          → (f  : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → proj₁ (var-tgt r x) ≾ᵣ uᵣ)
          → V-rename r (var f x) ≐ᵛ var f' (proj₂ (var-tgt r x))
var-ren-≐ r x f f' with var-rename r x
... | _ , _ , y = var-≐

-- The same with the target supplied, for callers that have computed it.

var-ren-tgt-≐ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (x : A ∈[ ρ ] Γ)
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → {t : Tgt Γ' A}
              → var-tgt r x ≡ t → (f' : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
              → V-rename r (var f x) ≐ᵛ var f' (proj₂ t)
var-ren-tgt-≐ r x f refl f' = var-ren-≐ r x f f'

------------------------------------------------------------------------
-- THE ACTION RESPECTS ACTING ALIKE
--
-- Induction on the term. At `var` the whole content is the hypothesis, the
-- grade bounds being irrelevant; the binding formers use `cong-ren-≐`, `handle`
-- uses `restrict-ren-≐`, and `unbox` stores `r ∘ʳ w`, related by `∘ʳ-≐`.
------------------------------------------------------------------------

mutual

  V-rename-≐ : ∀ {Γ Γ' A} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (V : Γ ⊢V⦂ A) → V-rename r V ≐ᵛ V-rename r' V

  V-rename-≐ {r = r} {r' = r'} h (var f x)
    with var-rename r x | var-rename r' x | at h x
  ... | _ | _ | refl = var-≐
  V-rename-≐ h (const c)  = const-≐
  V-rename-≐ h ⋆          = ⋆-≐
  V-rename-≐ h ⦉ V , W ⦊   = pair-≐ (V-rename-≐ h V) (V-rename-≐ h W)
  V-rename-≐ h (lam M)    = lam-≐ (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)

  C-rename-≐ : ∀ {Γ Γ' C} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (M : Γ ⊢C⦂ C) → C-rename r M ≐ᶜ C-rename r' M

  C-rename-≐ h (return V) = return-≐ (V-rename-≐ h V)
  C-rename-≐ h (M ⨟ N) =
    seq-≐ (C-rename-≐ h M) (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≐ h (V · W) = app-≐ (V-rename-≐ h V) (V-rename-≐ h W)
  C-rename-≐ h (match V `in M) =
    match-≐ (V-rename-≐ h V) (C-rename-≐ (cong-ren-≐ ([] ∷ _ ∷ _) h) M)
  C-rename-≐ h (absurd V) = absurd-≐ (V-rename-≐ h V)
  C-rename-≐ h (perform op V M) =
    perform-≐ (V-rename-≐ h V) (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-≐ h (delay τ M) =
    delay-≐ (C-rename-≐ (cong-ren-≐ ([] ⟨ _ ⟩) h) M)
  C-rename-≐ h (handle M `with H `in N) =
    handle-≐ (C-rename-≐ h M)
      (λ op ε'' →
         C-rename-≐ (cong-∷-ren-≐ (cong-∷-ren-≐ (restrict-ren-≐ h))) (H op ε''))
      (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≐ h (unbox w V M) =
    unbox-≐ (unbox-tgt-≐ (∘ʳ-≐ h (≐ʳ-refl {r = w})) V)
            (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)
  C-rename-≐ h (box V M) =
    box-≐ (V-rename-≐ (cong-ren-≐ ([] ⟨ _ ⟩) h) V)
          (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)
  C-rename-≐ h (coerce p M) = coerce-≐ (C-rename-≐ h M)

------------------------------------------------------------------------
-- RENAMING ALONG AN IDENTITY-LIKE RENAMING
--
-- `cong-∷-ren id-ren`, `⟨⟩-≤-ren` at equal grades and `⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-η-ren`
-- all act as the identity without being it, so the action is the identity only
-- up to the equivalence. Induction on the term, as for `C-rename-≐`.
------------------------------------------------------------------------

⟨⟩-≤-ren-id-≐ : ∀ {Γ ρ} → (p : ρ ≾ᵣ ρ) → ⟨⟩-≤-ren {Δ = Γ} p ≐ʳ id-ren
⟨⟩-≤-ren-id-≐ p = mk≐ʳ go
  where
    go : ∀ {A ρ₀} → (x : A ∈[ ρ₀ ] _) → _
    go (Tl-⟨⟩ x) = refl

cong-∷-ren-id-≐ : ∀ {Γ A} {r : Ren [] Γ Γ}
                → r ≐ʳ id-ren → cong-∷-ren {A = A} r ≐ʳ id-ren
cong-∷-ren-id-≐ h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (at h x)

cong-⟨⟩-ren-id-≐ : ∀ {Γ ρ} {r : Ren [] Γ Γ}
                 → r ≐ʳ id-ren → cong-⟨⟩-ren {ρ = ρ} r ≐ʳ id-ren
cong-⟨⟩-ren-id-≐ {ρ = ρ} h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (at h x)

cong-ren-id-≐ : ∀ {Γ} {r : Ren [] Γ Γ} → (Γ₀ : Ctx)
              → r ≐ʳ id-ren → cong-ren {Γ'' = Γ₀} r ≐ʳ id-ren
cong-ren-id-≐ []         h = h
cong-ren-id-≐ (Γ₀ ∷ A)   h = cong-∷-ren-id-≐ (cong-ren-id-≐ Γ₀ h)
cong-ren-id-≐ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-ren-id-≐ (cong-ren-id-≐ Γ₀ h)

∘ʳ-id-≐ : ∀ {Γ Γ'} {r : Ren [] Γ' Γ'} → (w : Ren [] Γ Γ')
        → r ≐ʳ id-ren → (r ∘ʳ w) ≐ʳ w
∘ʳ-id-≐ w h = mk≐ʳ (λ x → at h (proj₂ (var-tgt w x)))

∘ʳ-id-≐ʳ : ∀ {Γ Γ'} {r : Ren [] Γ Γ} → (w : Ren [] Γ Γ')
         → r ≐ʳ id-ren → (w ∘ʳ r) ≐ʳ w
∘ʳ-id-≐ʳ w h = mk≐ʳ (λ x → cong (var-tgt′ w) (at h x))

restrict-ren-id-≐ : ∀ {Γ} {r : Ren [] Γ Γ} → r ≐ʳ id-ren → restrict-ren r ≐ʳ id-ren
restrict-ren-id-≐ h = restrict-ren-≐ h

mutual

  V-rename-id-≐ : ∀ {Γ A} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (V : Γ ⊢V⦂ A) → V-rename r V ≐ᵛ V

  V-rename-id-≐ {r = r} h (var f x) with var-rename r x | at h x
  ... | _ | refl = var-≐
  V-rename-id-≐ h (const c) = const-≐
  V-rename-id-≐ h ⋆         = ⋆-≐
  V-rename-id-≐ h ⦉ V , W ⦊  = pair-≐ (V-rename-id-≐ h V) (V-rename-id-≐ h W)
  V-rename-id-≐ h (lam M)   = lam-≐ (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _) h) M)

  C-rename-id-≐ : ∀ {Γ C} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (M : Γ ⊢C⦂ C) → C-rename r M ≐ᶜ M

  C-rename-id-≐ h (return V) = return-≐ (V-rename-id-≐ h V)
  C-rename-id-≐ h (M ⨟ N) =
    seq-≐ (C-rename-id-≐ h M) (C-rename-id-≐ (cong-ren-id-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≐ h (V · W) = app-≐ (V-rename-id-≐ h V) (V-rename-id-≐ h W)
  C-rename-id-≐ h (match V `in M) =
    match-≐ (V-rename-id-≐ h V) (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _ ∷ _) h) M)
  C-rename-id-≐ h (absurd V) = absurd-≐ (V-rename-id-≐ h V)
  C-rename-id-≐ h (perform op V M) =
    perform-≐ (V-rename-id-≐ h V)
              (C-rename-id-≐ (cong-ren-id-≐ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-id-≐ h (delay τ M) =
    delay-≐ (C-rename-id-≐ (cong-ren-id-≐ ([] ⟨ _ ⟩) h) M)
  C-rename-id-≐ h (handle M `with H `in N) =
    handle-≐ (C-rename-id-≐ h M)
      (λ op ε'' →
         C-rename-id-≐ (cong-∷-ren-id-≐ (cong-∷-ren-id-≐ (restrict-ren-id-≐ h)))
                       (H op ε''))
      (C-rename-id-≐ (cong-ren-id-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≐ h (unbox w V M) =
    unbox-≐ (unbox-tgt-≐ (∘ʳ-id-≐ w h) V)
            (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _) h) M)
  C-rename-id-≐ h (box V M) =
    box-≐ (V-rename-id-≐ (cong-ren-id-≐ ([] ⟨ _ ⟩) h) V)
          (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _) h) M)
  C-rename-id-≐ h (coerce p M) = coerce-≐ (C-rename-id-≐ h M)

eq-ren-≐ : ∀ {Γ Γ'} → (e e' : Γ ≡ Γ') → eq-ren e ≐ʳ eq-ren e'
eq-ren-≐ e e' rewrite uip {p = e} {q = e'} = ≐ʳ-refl

-- Renaming along an identity-*like* renaming between contexts that are only
-- propositionally equal: the action is the transport. `eq-ren refl` is
-- `id-ren`, so this is `C-rename-id-≐` once the equality is matched.

C-rename-eq-≐ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {r : Ren [] Γ Γ'}
              → r ≐ʳ eq-ren e → (M : Γ ⊢C⦂ C)
              → C-rename r M ≐ᶜ subst (_⊢C⦂ C) e M
C-rename-eq-≐ refl h M = C-rename-id-≐ h M

-- Extending such a renaming by a suffix stays identity-like.

cong-ren-eq-ren-≐ : ∀ {Γ Γ'} → (Δ : Ctx) → (e : Γ ≡ Γ')
                  → cong-ren {Γ'' = Δ} (eq-ren e)
                  ≐ʳ eq-ren (cong (_++ᶜ Δ) e)
cong-ren-eq-ren-≐ Δ refl = cong-ren-id-≐ Δ ≐ʳ-refl

-- `eq-ren` commutes with the suffix formers. (Note `cong-ren` at nested suffixes
-- is *not* `cong-ren` at their concatenation: the contexts differ by
-- `++ᶜ-assoc`, so any such step has to be conjugated by `eq-ren`s.)

eq-ren-∷-≐ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ')
           → eq-ren (cong (_∷ A) e) ≐ʳ cong-∷-ren {A = A} (eq-ren e)
eq-ren-∷-≐ refl = ≐ʳ-sym (cong-∷-ren-id-≐ ≐ʳ-refl)

eq-ren-⟨⟩-≐ : ∀ {Γ Γ' ρ} → (e : Γ ≡ Γ')
            → eq-ren (cong (_⟨ ρ ⟩) e) ≐ʳ cong-⟨⟩-ren {ρ = ρ} (eq-ren e)
eq-ren-⟨⟩-≐ refl = ≐ʳ-sym (cong-⟨⟩-ren-id-≐ ≐ʳ-refl)

-- A context splitting is determined by its two halves: `_,_split_` recurses on
-- the right half, so its constructor is forced at each step. This is what
-- identifies the two ways `sub-wk`'s `handle` case reaches the substituted
-- variable — `split-++ʳ (∈-ᴱ-split et z₀) D` and `split-≡-++ᶜ` — without
-- computing either. (Pure `Syntax.Contexts` material; see the cleanup list.)

split-unique : ∀ {Γ Γ₁ Γ₂} → (s s' : Γ₁ , Γ₂ split Γ) → s ≡ s'
split-unique split-[]     split-[]      = refl
split-unique (split-∷ s)  (split-∷ s')  = cong split-∷ (split-unique s s')
split-unique (split-⟨⟩ s) (split-⟨⟩ s') = cong split-⟨⟩ (split-unique s s')

-- Hence the variables they name agree, once the two contexts are identified.

split→∈-subst : ∀ {Γ Γ' Γ₁ Γ₂ A} → (e : Γ ≡ Γ')
              → (s : Γ₁ ∷ A , Γ₂ split Γ)
              → split→∈ (subst (λ Γ₀ → Γ₁ ∷ A , Γ₂ split Γ₀) e s)
              ≡ subst (λ Γ₀ → A ∈[ ctx-grade Γ₂ ] Γ₀) e (split→∈ s)
split→∈-subst refl s = refl

split→∈-unique : ∀ {Γ Γ' Γ₁ Γ₂ A} → (e : Γ ≡ Γ')
               → (s : Γ₁ ∷ A , Γ₂ split Γ) → (s' : Γ₁ ∷ A , Γ₂ split Γ')
               → subst (λ Γ₀ → A ∈[ ctx-grade Γ₂ ] Γ₀) e (split→∈ s)
               ≡ split→∈ s'
split→∈-unique e s s' =
  trans (sym (split→∈-subst e s))
        (cong split→∈ (split-unique (subst (λ Γ₀ → _ , _ split Γ₀) e s) s'))

-- `cong-ren` at nested suffixes is `cong-ren` at their concatenation — but only
-- up to `++ᶜ-assoc`, so conjugated by `eq-ren`s.

cong-ren-assoc-≐ : ∀ {Γ Γ'} → (Θ D : Ctx) → (r : Ren [] Γ Γ')
                 → cong-ren {Γ'' = D} (cong-ren {Γ'' = Θ} r)
                 ≐ʳ (eq-ren (sym (++ᶜ-assoc Γ' Θ D))
                     ∘ʳ cong-ren {Γ'' = Θ ++ᶜ D} r
                     ∘ʳ eq-ren (++ᶜ-assoc Γ Θ D))

cong-ren-assoc-≐ Θ [] r =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

cong-ren-assoc-≐ {Γ} {Γ'} Θ (D ∷ A) r =
  ≐ʳ-trans (cong-∷-ren-≐ (cong-ren-assoc-≐ Θ D r))
    (≐ʳ-trans (cong-∷-ren-∘-≐ _ _)
      (≐ʳ-trans (∘ʳ-≐ (≐ʳ-trans (≐ʳ-sym (eq-ren-∷-≐ (sym (++ᶜ-assoc Γ' Θ D))))
                                (eq-ren-≐ _ _))
                      (cong-∷-ren-∘-≐ _ _))
                (∘ʳ-≐ ≐ʳ-refl
                      (∘ʳ-≐ ≐ʳ-refl
                            (≐ʳ-trans (≐ʳ-sym (eq-ren-∷-≐ (++ᶜ-assoc Γ Θ D)))
                                      (eq-ren-≐ _ _))))))

cong-ren-assoc-≐ {Γ} {Γ'} Θ (D ⟨ ρ ⟩) r =
  ≐ʳ-trans (cong-⟨⟩-ren-≐ (cong-ren-assoc-≐ Θ D r))
    (≐ʳ-trans (cong-⟨⟩-ren-∘-≐ _ _)
      (≐ʳ-trans (∘ʳ-≐ (≐ʳ-trans (≐ʳ-sym (eq-ren-⟨⟩-≐ (sym (++ᶜ-assoc Γ' Θ D))))
                                (eq-ren-≐ _ _))
                      (cong-⟨⟩-ren-∘-≐ _ _))
                (∘ʳ-≐ ≐ʳ-refl
                      (∘ʳ-≐ ≐ʳ-refl
                            (≐ʳ-trans (≐ʳ-sym (eq-ren-⟨⟩-≐ (++ᶜ-assoc Γ Θ D)))
                                      (eq-ren-≐ _ _))))))

-- Composing two `eq-ren`s.

eq-ren-∘-≐ : ∀ {Γ Γ' Γ''} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ'')
           → (eq-ren e' ∘ʳ eq-ren e) ≐ʳ eq-ren (trans e e')
eq-ren-∘-≐ refl refl = ∘ʳ-identityˡ-≐ _

-- With an *eternal* `B`, weakening by `B` weakens the eternal restriction by it
-- too: `restrict-ren` walks down to `restrict-ren wk-ren`, which at an eternal
-- type is `wk-ren`. The two contexts differ by `ᴱ`'s distribution over `_++ᶜ_`,
-- so the statement is conjugated by `eq-ren`s at arbitrary proofs of that.

restrict-wk-et-≐ : ∀ {Γ B} → (et : Eternal B) → (Δ : Ctx)
                 → (e₁ : (Γ ++ᶜ Δ) ᴱ ≡ Γ ᴱ ++ᶜ Δ ᴱ)
                 → (e₂ : ((Γ ∷ B) ++ᶜ Δ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Δ ᴱ)
                 → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (wk-ren {A = B}))
                 ≐ʳ (eq-ren (sym e₂)
                     ∘ʳ cong-ren {Γ'' = Δ ᴱ} (wk-ren {A = B}) ∘ʳ eq-ren e₁)

restrict-wk-et-≐ {Γ} {B} et [] e₁ e₂
  rewrite eternal?-yes et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

restrict-wk-et-≐ {Γ} {B} et (Δ ∷ C) e₁ e₂ with eternal? C

... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ (restrict-wk-et-≐ et Δ (∷ᶜ-injective-ctx e₁)
                                              (∷ᶜ-injective-ctx e₂)))
    (≐ʳ-trans (cong-∷-ren-∘-≐ _ _)
      (≐ʳ-trans (∘ʳ-≐ (≐ʳ-sym (eq-ren-∷-≐ (sym (∷ᶜ-injective-ctx e₂))))
                      (cong-∷-ren-∘-≐ _ _))
        (≐ʳ-trans (∘ʳ-≐ (eq-ren-≐ _ (sym e₂))
                        (∘ʳ-≐ ≐ʳ-refl
                              (≐ʳ-sym (eq-ren-∷-≐ (∷ᶜ-injective-ctx e₁)))))
                  (∘ʳ-≐ ≐ʳ-refl (∘ʳ-≐ ≐ʳ-refl (eq-ren-≐ _ e₁))))))

... | no  _ = restrict-wk-et-≐ et Δ e₁ e₂

restrict-wk-et-≐ {Γ} {B} et (Δ ⟨ ρ ⟩) e₁ e₂ = restrict-wk-et-≐ et Δ e₁ e₂

-- The form `sub-wk`'s eternal `handle` clause needs: the clause's renaming
-- `cong-ren {D} (restrict-ren (cong-ren {Θ} wk-ren))` is `cong-ren` at the
-- concatenated suffix `Θ ᴱ ++ᶜ D`, conjugated by `eq-ren`s. Assembled from
-- `restrict-wk-et-≐`, `cong-ren-∘-≐`, `cong-ren-eq-ren-≐` and
-- `cong-ren-assoc-≐`, with the `eq-ren`s fused by `eq-ren-∘-≐` and any two
-- proofs identified by `eq-ren-≐`.

restrict-wk-clause-≐ : ∀ {Γ B} → (et : Eternal B) → (Θ D : Ctx)
                     → (e₁ : (Γ ++ᶜ Θ) ᴱ ≡ Γ ᴱ ++ᶜ Θ ᴱ)
                     → (e₂ : ((Γ ∷ B) ++ᶜ Θ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Θ ᴱ)
                     → cong-ren {Γ'' = D}
                         (restrict-ren {Ξ = []} (cong-ren {Γ'' = Θ} (wk-ren {A = B})))
                     ≐ʳ (eq-ren (cong (_++ᶜ D) (sym e₂))
                         ∘ʳ (eq-ren (sym (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) D))
                             ∘ʳ cong-ren {Γ'' = Θ ᴱ ++ᶜ D} (wk-ren {A = B})
                             ∘ʳ eq-ren (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D))
                         ∘ʳ eq-ren (cong (_++ᶜ D) e₁))

restrict-wk-clause-≐ {Γ} {B} et Θ D e₁ e₂ =
  ≐ʳ-trans (cong-ren-≐ D (restrict-wk-et-≐ et Θ e₁ e₂))
    (≐ʳ-trans (cong-ren-∘-≐ D _ _)
      (∘ʳ-≐ (cong-ren-eq-ren-≐ D (sym e₂))
        (≐ʳ-trans (cong-ren-∘-≐ D _ _)
                  (∘ʳ-≐ (cong-ren-assoc-≐ (Θ ᴱ) D (wk-ren {A = B}))
                        (cong-ren-eq-ren-≐ D e₁)))))

-- With a non-eternal `B`, weakening by `B` leaves the eternal restriction
-- alone: `restrict-ren` walks `cong-ren` down to `restrict-ren wk-ren`, which at
-- a non-eternal type is `id-ren`. The two contexts are then equal only
-- propositionally, so the statement is against an arbitrary proof of that
-- equality — any two agree by `uip`.

restrict-wk-≐ : ∀ {Γ B} → (¬et : ¬ Eternal B) → (Δ : Ctx)
              → (e : (Γ ++ᶜ Δ) ᴱ ≡ ((Γ ∷ B) ++ᶜ Δ) ᴱ)
              → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (wk-ren {A = B})) ≐ʳ eq-ren e

restrict-wk-≐ {Γ} {B} ¬et [] e
  rewrite eternal?-no ¬et | uip {p = e} {q = refl} = ≐ʳ-refl

restrict-wk-≐ {Γ} {B} ¬et (Δ ∷ C) e with eternal? C
... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ (restrict-wk-≐ ¬et Δ (∷ᶜ-injective-ctx e)))
    (≐ʳ-trans (cong-ren-eq-ren-≐ ([] ∷ C) (∷ᶜ-injective-ctx e))
              (eq-ren-≐ _ e))
... | no  _ = restrict-wk-≐ ¬et Δ e

restrict-wk-≐ {Γ} {B} ¬et (Δ ⟨ ρ ⟩) e = restrict-wk-≐ ¬et Δ e

------------------------------------------------------------------------
-- FUNCTORIALITY
--
-- At the binding formers the two sides rename along `cong-ren (r₂ ∘ʳ r₁)` and
-- `cong-ren r₂ ∘ʳ cong-ren r₁`, at `unbox` along `(r₂ ∘ʳ r₁) ∘ʳ w` and
-- `r₂ ∘ʳ (r₁ ∘ʳ w)`: distinct renamings acting alike, so the statement is at
-- `_≐ᵛ_`/`_≐ᶜ_` and the proof leans on the laws above.
------------------------------------------------------------------------

mutual

  V-rename-∘ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (V : Γ ⊢V⦂ A)
             → V-rename (r₂ ∘ʳ r₁) V ≐ᵛ V-rename r₂ (V-rename r₁ V)

  V-rename-∘ r₂ r₁ (var f x) with var-rename r₁ x
  ... | _ , _ , y with var-rename r₂ y
  ...   | _ , _ , z = var-≐
  V-rename-∘ r₂ r₁ (const c) = const-≐
  V-rename-∘ r₂ r₁ ⋆         = ⋆-≐
  V-rename-∘ r₂ r₁ ⦉ V , W ⦊  = pair-≐ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  V-rename-∘ r₂ r₁ (lam M)   =
    lam-≐ (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))

  C-rename-∘ : ∀ {Γ Γ' Γ'' C} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (M : Γ ⊢C⦂ C)
             → C-rename (r₂ ∘ʳ r₁) M ≐ᶜ C-rename r₂ (C-rename r₁ M)

  C-rename-∘ r₂ r₁ (return V) = return-≐ (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (M ⨟ N) =
    seq-≐ (C-rename-∘ r₂ r₁ M)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (V · W) = app-≐ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  C-rename-∘ r₂ r₁ (match V `in M) =
    match-≐ (V-rename-∘ r₂ r₁ V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (absurd V) = absurd-≐ (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (perform op V M) =
    perform-≐ (V-rename-∘ r₂ r₁ V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (delay τ M) =
    delay-≐ (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ⟨ _ ⟩) r₂ r₁) M)
                      (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (handle M `with H `in N) =
    handle-≐ (C-rename-∘ r₂ r₁ M)
      (λ op ε'' →
         ≐ᶜ-trans
           (C-rename-≐
             (≐ʳ-trans (cong-∷-ren-≐ (cong-∷-ren-≐ (restrict-ren-∘-≐ r₂ r₁)))
                       (cong-ren-∘-≐ ([] ∷ _ ∷ _)
                                     (restrict-ren r₂) (restrict-ren r₁)))
             (H op ε''))
           (C-rename-∘ (cong-∷-ren (cong-∷-ren (restrict-ren r₂)))
                       (cong-∷-ren (cong-∷-ren (restrict-ren r₁)))
                       (H op ε'')))
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (unbox w V M) =
    unbox-≐ (unbox-tgt-≐ (∘ʳ-assoc-≐ r₂ r₁ w) V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (box V M) =
    box-≐ (≐ᵛ-trans (V-rename-≐ (cong-ren-∘-≐ ([] ⟨ _ ⟩) r₂ r₁) V)
                    (V-rename-∘ (cong-ren r₂) (cong-ren r₁) V))
          (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (coerce p M) = coerce-≐ (C-rename-∘ r₂ r₁ M)

------------------------------------------------------------------------
-- THE ACTION IS A CONGRUENCE
--
-- Renaming related terms gives related terms. Induction on the relation, not on
-- the term; `unbox` needs `∘ʳ-≐` on the stored renamings.
------------------------------------------------------------------------

mutual

  V-rename-cong : ∀ {Γ Γ' A} → (r : Ren [] Γ Γ') → {V V' : Γ ⊢V⦂ A}
                → V ≐ᵛ V' → V-rename r V ≐ᵛ V-rename r V'

  V-rename-cong r var-≐            = var-≐
  V-rename-cong r const-≐          = const-≐
  V-rename-cong r ⋆-≐              = ⋆-≐
  V-rename-cong r (pair-≐ eV eW)   =
    pair-≐ (V-rename-cong r eV) (V-rename-cong r eW)
  V-rename-cong r (lam-≐ eM)       = lam-≐ (C-rename-cong (cong-ren r) eM)

  C-rename-cong : ∀ {Γ Γ' C} → (r : Ren [] Γ Γ') → {M M' : Γ ⊢C⦂ C}
                → M ≐ᶜ M' → C-rename r M ≐ᶜ C-rename r M'

  C-rename-cong r (return-≐ eV)     = return-≐ (V-rename-cong r eV)
  C-rename-cong r (seq-≐ eM eN)     =
    seq-≐ (C-rename-cong r eM) (C-rename-cong (cong-ren r) eN)
  C-rename-cong r (app-≐ eV eW)     =
    app-≐ (V-rename-cong r eV) (V-rename-cong r eW)
  C-rename-cong r (match-≐ eV eM)   =
    match-≐ (V-rename-cong r eV) (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (absurd-≐ eV)     = absurd-≐ (V-rename-cong r eV)
  C-rename-cong r (perform-≐ eV eM) =
    perform-≐ (V-rename-cong r eV) (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (delay-≐ eM)      = delay-≐ (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (handle-≐ eM eH eN) =
    handle-≐ (C-rename-cong r eM)
             (λ op ε'' → C-rename-cong (cong-∷-ren (cong-∷-ren (restrict-ren r)))
                                       (eH op ε''))
             (C-rename-cong (cong-ren r) eN)
  C-rename-cong r (unbox-≐ {w = w} {w' = w'} {V = V} {V' = V'} hw eM) =
    unbox-≐ (trans (unbox-tgt-∘ r w V)
                   (trans (cong (var-tgt′ r) hw)
                          (sym (unbox-tgt-∘ r w' V'))))
            (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (coerce-≐ eM)     = coerce-≐ (C-rename-cong r eM)
  C-rename-cong r (box-≐ eV eM)     =
    box-≐ (V-rename-cong (cong-ren r) eV) (C-rename-cong (cong-ren r) eM)
