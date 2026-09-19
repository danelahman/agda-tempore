------------------------------------------------------------------------
-- When two renamings act alike.                                      --
--                                                                    --
-- `Ren` is a free syntactic structure: `id-ren`, `_∘ʳ_` and the       --
-- congruences are constructors, so composition is not associative     --
-- and `cong-ren` does not commute with it on the nose. What is true   --
-- is that renamings agreeing on variables act the same on terms.      --
--                                                                    --
-- `_≐ʳ_` compares renamings by where a variable of the target comes   --
-- from — grade and position, not the grade-bound proof, which is      --
-- irrelevant.                                                         --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Renamings.Equivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings  Spec
open import Syntax.Types      Spec

-- Where a renaming sends a variable, forgetting the grade bound.

Var : Ctx → VType → Set
Var Γ' A = Σ[ ρ' ∈ R ] A ∈[ ρ' ] Γ'

var-img : ∀ {Γ Γ' A ρ} → Ren [] Γ Γ' → A ∈[ ρ ] Γ' → Var Γ A
var-img r x = proj₁ (var-rename r x) , proj₂ (proj₂ (var-rename r x))

-- The same, at an already-located variable: this is what makes `var-img` of a
-- composite the composite of `var-img`s, definitionally.

var-img′ : ∀ {Γ' Γ'' A} → Ren [] Γ' Γ'' → Var Γ'' A → Var Γ' A
var-img′ r (ρ' , y) = var-img r y

-- Pushing a `Var` under one more binder, resp. one more lock. Named rather than
-- written as a lambda because `Var` is a Σ, so `cong` cannot infer the motive.

Var-∷ : ∀ {Γ A B} → Var Γ A → Var (Γ ∷ B) A
Var-∷ (σ , y) = σ , Tl-∷ y

Var-⟨⟩ : ∀ {Γ A} → (ρ : R) → Var Γ A → Var (Γ ⟨ ρ ⟩) A
Var-⟨⟩ ρ (σ , y) = σ ·ᵣ ρ , Tl-⟨⟩ y

-- Relocating a variable past a context equality that only extends it, by
-- pushing the equality inside the constructors.

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


infix 4 _≐ʳ_

-- A record, not a function type: the statements below are used at renamings
-- Agda has to *infer*, which needs the relation to be rigid.

record _≐ʳ_ {Γ Γ'} (r r' : Ren [] Γ Γ') : Set where
  constructor mk≐ʳ
  field at : ∀ {A ρ} → (x : A ∈[ ρ ] Γ') → var-img r x ≡ var-img r' x

open _≐ʳ_ public

≐ʳ-refl : ∀ {Γ Γ'} {r : Ren [] Γ Γ'} → r ≐ʳ r
≐ʳ-refl = mk≐ʳ (λ x → refl)

≐ʳ-sym : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'} → r ≐ʳ r' → r' ≐ʳ r
≐ʳ-sym h = mk≐ʳ (λ x → sym (at h x))

≐ʳ-trans : ∀ {Γ Γ'} {r r' r'' : Ren [] Γ Γ'} → r ≐ʳ r' → r' ≐ʳ r'' → r ≐ʳ r''
≐ʳ-trans h h' = mk≐ʳ (λ x → trans (at h x) (at h' x))

-- `var-rename (r₂ ∘ʳ r₁)` locates the variable with `r₂` and then with `r₁`;
-- the three laws below hold at the level of `var-img` by computation.

∘ʳ-≐ʳ : ∀ {Γ Γ' Γ''} {r₂ r₂' : Ren [] Γ' Γ''} {r₁ r₁' : Ren [] Γ Γ'}
     → r₂ ≐ʳ r₂' → r₁ ≐ʳ r₁'
     -------------------------------
     → (r₂ ∘ʳ r₁) ≐ʳ (r₂' ∘ʳ r₁')
∘ʳ-≐ʳ {r₁ = r₁} h₂ h₁ =
  mk≐ʳ (λ x → trans (cong (var-img′ r₁) (at h₂ x)) (at h₁ _))

∘ʳ-assoc-≐ʳ : ∀ {Γ Γ' Γ'' Γ'''}
           → (r₃ : Ren [] Γ'' Γ''') → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
           ----------------------------------------------------------
           → ((r₃ ∘ʳ r₂) ∘ʳ r₁) ≐ʳ (r₃ ∘ʳ (r₂ ∘ʳ r₁))
∘ʳ-assoc-≐ʳ r₃ r₂ r₁ = mk≐ʳ (λ x → refl)

∘ʳ-identityˡ-≐ʳ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (id-ren ∘ʳ r) ≐ʳ r
∘ʳ-identityˡ-≐ʳ r = mk≐ʳ (λ x → refl)

∘ʳ-identityʳ-≐ʳ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (r ∘ʳ id-ren) ≐ʳ r
∘ʳ-identityʳ-≐ʳ r = mk≐ʳ (λ x → refl)

-- `⟨⟩-≤-ren` stores a `≾ᵣ` proof, but sends a variable to itself at a grade
-- fixed by the renaming's indices; the proof is not observable.

⟨⟩-≤-ren-≐ʳ : ∀ {Γ ρ ρ'} → (p p' : ρ' ≾ᵣ ρ)
           → ⟨⟩-≤-ren {Δ = Γ} p ≐ʳ ⟨⟩-≤-ren p'
⟨⟩-≤-ren-≐ʳ p p' = mk≐ʳ go
  where
    go : ∀ {A ρ₀} → (x : A ∈[ ρ₀ ] _) → _
    go (Tl-⟨⟩ x) = refl

-- Relocating a whole `Var` along a context equality, and the pushes it commutes
-- with.

Var-cast : ∀ {Γ Γ' A} → Γ ≡ Γ' → Var Γ A → Var Γ' A
Var-cast {A = A} e (σ , y) = σ , subst (λ Γ₀ → A ∈[ σ ] Γ₀) e y

Var-cast-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (t : Var Γ A)
             → Var-cast e t ≡ Var-cast e' t
Var-cast-irr e e' t = cong (λ z → Var-cast z t) uip

Var-cast-∷ : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → (t : Var Γ A)
           → Var-cast {A = A} (cong (_∷ C) e) (Var-∷ t) ≡ Var-∷ (Var-cast e t)
Var-cast-∷ e (σ , y) = cong (λ v → σ , v) (subst-Tl-∷ e y)

Var-cast-⟨⟩ : ∀ {Γ Γ' A} → (ρ : R) → (e : Γ ≡ Γ') → (t : Var Γ A)
            → Var-cast {A = A} (cong (_⟨ ρ ⟩) e) (Var-⟨⟩ ρ t)
            ≡ Var-⟨⟩ ρ (Var-cast e t)
Var-cast-⟨⟩ ρ e (σ , y) = cong (λ v → σ ·ᵣ ρ , v) (subst-Tl-⟨⟩ e y)

-- An `eq-ren` relocates a variable and leaves its grade alone.

eq-ren-img : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
           → var-img (eq-ren e) x ≡ (ρ , subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
eq-ren-img refl x = refl

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

-- The grade depends only on the suffix, not on the variable, so it is a
-- function of its own.

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
             → Var-cast (sym (++ᶜ-assoc Γ Δ₁ Δ₂))
                 (grade-++ᶜˡ ρ (Δ₁ ++ᶜ Δ₂) , ∈-++ᶜˡ (Δ₁ ++ᶜ Δ₂) x)
             ≡ (grade-++ᶜˡ (grade-++ᶜˡ ρ Δ₁) Δ₂ , ∈-++ᶜˡ Δ₂ (∈-++ᶜˡ Δ₁ x))

∈-++ᶜˡ-assoc Δ₁ []         x = refl
∈-++ᶜˡ-assoc {Γ} Δ₁ (Δ₂ ∷ B)   x =
  trans (Var-cast-irr (sym (++ᶜ-assoc Γ Δ₁ (Δ₂ ∷ B)))
                      (cong (_∷ B) (sym (++ᶜ-assoc Γ Δ₁ Δ₂))) _)
    (trans (Var-cast-∷ (sym (++ᶜ-assoc Γ Δ₁ Δ₂)) _)
           (cong Var-∷ (∈-++ᶜˡ-assoc Δ₁ Δ₂ x)))
∈-++ᶜˡ-assoc {Γ} Δ₁ (Δ₂ ⟨ ρ' ⟩) x =
  trans (Var-cast-irr (sym (++ᶜ-assoc Γ Δ₁ (Δ₂ ⟨ ρ' ⟩)))
                      (cong (_⟨ ρ' ⟩) (sym (++ᶜ-assoc Γ Δ₁ Δ₂))) _)
    (trans (Var-cast-⟨⟩ ρ' (sym (++ᶜ-assoc Γ Δ₁ Δ₂)) _)
           (cong (Var-⟨⟩ ρ') (∈-++ᶜˡ-assoc Δ₁ Δ₂ x)))

-- A congruence renaming sends a pushed prefix variable to the push of its
-- image: the counterpart of `cong-ren-img-r`, and what makes the pushing
-- renaming family natural.

cong-ren-img-l : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (Δ : Ctx) → (y : A ∈[ ρ ] Γ')
               → var-img (cong-ren {Γ'' = Δ} r) (∈-++ᶜˡ Δ y)
               ≡ (grade-++ᶜˡ (proj₁ (var-img r y)) Δ
                 , ∈-++ᶜˡ Δ (proj₂ (var-img r y)))

cong-ren-img-l r []         y = refl
cong-ren-img-l r (Δ ∷ B)    y =
  cong (λ t → proj₁ t , Tl-∷ (proj₂ t)) (cong-ren-img-l r Δ y)
cong-ren-img-l r (Δ ⟨ ρ' ⟩) y =
  cong (λ t → proj₁ t ·ᵣ ρ' , Tl-⟨⟩ (proj₂ t)) (cong-ren-img-l r Δ y)

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
               → _≡_ {A = Var ((Γ₁ ∷ B) ++ᶜ Γ₂) B}
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
            → Var-cast (++ᶜ-assoc Γ Γ₀ Δ)
                (grade-++ᶜˡ ρ Δ , ∈-++ᶜˡ {Γ = Γ ++ᶜ Γ₀} Δ (∈-++ᶜʳ {Γ = Γ} y))
            ≡ (grade-++ᶜˡ ρ Δ , ∈-++ᶜʳ {Γ = Γ} (∈-++ᶜˡ {Γ = Γ₀} Δ y))

∈-++ᶜˡ-++ᶜʳ Γ Γ₀ []         y = refl
∈-++ᶜˡ-++ᶜʳ Γ Γ₀ (Δ ∷ B)    y =
  trans (Var-cast-∷ (++ᶜ-assoc Γ Γ₀ Δ) _)
        (cong Var-∷ (∈-++ᶜˡ-++ᶜʳ Γ Γ₀ Δ y))
∈-++ᶜˡ-++ᶜʳ Γ Γ₀ (Δ ⟨ ρ' ⟩) y =
  trans (Var-cast-⟨⟩ ρ' (++ᶜ-assoc Γ Γ₀ Δ) _)
        (cong (Var-⟨⟩ ρ') (∈-++ᶜˡ-++ᶜʳ Γ Γ₀ Δ y))

-- Reading a `Var-cast` equation in the other direction.

Var-cast-flip : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Var Γ A) → (t' : Var Γ' A)
              → Var-cast e t ≡ t' → Var-cast (sym e) t' ≡ t
Var-cast-flip refl t t' q = sym q

Var-cast-flip⁻ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Var Γ' A) → (t' : Var Γ A)
               → Var-cast (sym e) t ≡ t' → Var-cast e t' ≡ t
Var-cast-flip⁻ refl t t' q = sym q

-- The renaming that weakens a context by a whole suffix, defined only when
-- the suffix's grade is bounded by the unit: each lock is crossed by
-- `⟨⟩-≤-ren` at its own grade.

push-ren : ∀ {Γ₀} → (Δ : Ctx) → ctx-grade Δ ≾ᵣ uᵣ → Ren [] (Γ₀ ++ᶜ Δ) Γ₀
push-ren []         p = id-ren
push-ren (Δ ∷ B)    p = push-ren Δ p ∘ʳ wk-ren
push-ren (Δ ⟨ ρ' ⟩) p =
  push-ren Δ (≾ᵣ-zero-productˡ p)
    ∘ʳ (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ p))

-- It acts as `∈-++ᶜˡ`, which is what pins it down up to `_≐ʳ_`.

push-ren-img : ∀ {Γ₀ A ρ} → (Δ : Ctx) → (p : ctx-grade Δ ≾ᵣ uᵣ)
             → (y : A ∈[ ρ ] Γ₀)
             → var-img (push-ren {Γ₀} Δ p) y ≡ (grade-++ᶜˡ ρ Δ , ∈-++ᶜˡ Δ y)
push-ren-img []         p y = refl
push-ren-img (Δ ∷ B)    p y = cong Var-∷ (push-ren-img Δ p y)
push-ren-img (Δ ⟨ ρ' ⟩) p y =
  cong (Var-⟨⟩ ρ') (push-ren-img Δ (≾ᵣ-zero-productˡ p) y)

-- At a one-entry suffix it is the weakening, resp. the lock crossing — the two
-- shapes the environment's telescope zones present.

push-ren-∷ : ∀ {Γ₀ B} → (p : ctx-grade ([] ∷ B) ≾ᵣ uᵣ)
           → push-ren {Γ₀} ([] ∷ B) p ≐ʳ wk-ren
push-ren-∷ p = ∘ʳ-identityˡ-≐ʳ wk-ren

push-ren-⟨⟩ : ∀ {Γ₀ ρ} → (p : ctx-grade ([] ⟨ ρ ⟩) ≾ᵣ uᵣ) → (p' : ρ ≾ᵣ uᵣ)
            → push-ren {Γ₀} ([] ⟨ ρ ⟩) p ≐ʳ (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p')
push-ren-⟨⟩ p p' =
  ≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _) (∘ʳ-≐ʳ ≐ʳ-refl (⟨⟩-≤-ren-≐ʳ _ p'))

-- Pushing is natural: renaming the prefix and then pushing is pushing and then
-- renaming the prefix under the suffix.

push-ren-nat : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (Δ : Ctx)
             → (p : ctx-grade Δ ≾ᵣ uᵣ)
             → (push-ren Δ p ∘ʳ cong-ren {Γ'' = Δ} r) ≐ʳ (r ∘ʳ push-ren Δ p)
push-ren-nat r Δ p = mk≐ʳ go
  where
    go : ∀ {A σ} → (y : A ∈[ σ ] _) → _
    go y =
      trans (cong (var-img′ (cong-ren {Γ'' = Δ} r)) (push-ren-img Δ p y))
        (trans (cong-ren-img-l r Δ y)
               (sym (push-ren-img Δ p (proj₂ (var-img r y)))))

-- Pushing by a concatenated suffix is pushing twice, the contexts differing by
-- associativity.

push-ren-++ᶜ : ∀ {Γ₀} → (Δ₁ Δ₂ : Ctx)
             → (p : ctx-grade (Δ₁ ++ᶜ Δ₂) ≾ᵣ uᵣ)
             → (p₁ : ctx-grade Δ₁ ≾ᵣ uᵣ) → (p₂ : ctx-grade Δ₂ ≾ᵣ uᵣ)
             → (push-ren (Δ₁ ++ᶜ Δ₂) p ∘ʳ eq-ren (sym (++ᶜ-assoc Γ₀ Δ₁ Δ₂)))
             ≐ʳ (push-ren {Γ₀} Δ₁ p₁ ∘ʳ push-ren Δ₂ p₂)
push-ren-++ᶜ {Γ₀} Δ₁ Δ₂ p p₁ p₂ = mk≐ʳ go
  where
    e = sym (++ᶜ-assoc Γ₀ Δ₁ Δ₂)

    go : ∀ {A σ} → (y : A ∈[ σ ] Γ₀) → _
    go y =
      trans (cong (var-img′ (eq-ren e)) (push-ren-img (Δ₁ ++ᶜ Δ₂) p y))
        (trans (eq-ren-img e (∈-++ᶜˡ (Δ₁ ++ᶜ Δ₂) y))
          (trans (∈-++ᶜˡ-assoc Δ₁ Δ₂ y)
            (sym (trans (cong (var-img′ (push-ren Δ₂ p₂)) (push-ren-img Δ₁ p₁ y))
                        (push-ren-img Δ₂ p₂ (∈-++ᶜˡ Δ₁ y))))))

-- `cong-ren` recurses on the suffix; it respects `_≐ʳ_` and commutes with
-- composition up to it (`cong-∷-ren (r ∘ʳ r')` and `cong-∷-ren r ∘ʳ cong-∷-ren r'`
-- are distinct renamings acting alike).

cong-∷-ren-≐ʳ : ∀ {Γ Γ' A} {r r' : Ren [] Γ Γ'}
             → r ≐ʳ r' → cong-∷-ren {A = A} r ≐ʳ cong-∷-ren r'
cong-∷-ren-≐ʳ h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (at h x)

cong-⟨⟩-ren-≐ʳ : ∀ {Γ Γ' ρ} {r r' : Ren [] Γ Γ'}
              → r ≐ʳ r' → cong-⟨⟩-ren {ρ = ρ} r ≐ʳ cong-⟨⟩-ren r'
cong-⟨⟩-ren-≐ʳ {ρ = ρ} h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (at h x)

cong-ren-≐ʳ : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'} → (Γ₀ : Ctx)
           → r ≐ʳ r' → cong-ren {Γ'' = Γ₀} r ≐ʳ cong-ren r'
cong-ren-≐ʳ []         h = h
cong-ren-≐ʳ (Γ₀ ∷ A)   h = cong-∷-ren-≐ʳ (cong-ren-≐ʳ Γ₀ h)
cong-ren-≐ʳ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-ren-≐ʳ (cong-ren-≐ʳ Γ₀ h)

cong-∷-ren-∘-≐ʳ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
               → cong-∷-ren {A = A} (r₂ ∘ʳ r₁)
               ≐ʳ (cong-∷-ren r₂ ∘ʳ cong-∷-ren r₁)
cong-∷-ren-∘-≐ʳ r₂ r₁ = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = refl

cong-⟨⟩-ren-∘-≐ʳ : ∀ {Γ Γ' Γ'' ρ} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
                → cong-⟨⟩-ren {ρ = ρ} (r₂ ∘ʳ r₁)
                ≐ʳ (cong-⟨⟩-ren r₂ ∘ʳ cong-⟨⟩-ren r₁)
cong-⟨⟩-ren-∘-≐ʳ {ρ = ρ} r₂ r₁ = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = refl

-- Weakening is natural: renaming the prefix and then weakening is weakening
-- and then renaming under the new binder.

wk-ren-nat-≐ʳ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ')
             → (wk-ren ∘ʳ cong-∷-ren {A = B} r) ≐ʳ (r ∘ʳ wk-ren)
wk-ren-nat-≐ʳ r = mk≐ʳ (λ y → refl)

cong-ren-∘-≐ʳ : ∀ {Γ Γ' Γ''} → (Γ₀ : Ctx)
             → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → cong-ren {Γ'' = Γ₀} (r₂ ∘ʳ r₁)
             ≐ʳ (cong-ren {Γ'' = Γ₀} r₂ ∘ʳ cong-ren {Γ'' = Γ₀} r₁)
cong-ren-∘-≐ʳ []         r₂ r₁ = ≐ʳ-refl
cong-ren-∘-≐ʳ (Γ₀ ∷ A)   r₂ r₁ =
  ≐ʳ-trans (cong-∷-ren-≐ʳ (cong-ren-∘-≐ʳ Γ₀ r₂ r₁))
           (cong-∷-ren-∘-≐ʳ (cong-ren {Γ'' = Γ₀} r₂) (cong-ren {Γ'' = Γ₀} r₁))
cong-ren-∘-≐ʳ (Γ₀ ⟨ ρ ⟩) r₂ r₁ =
  ≐ʳ-trans (cong-⟨⟩-ren-≐ʳ (cong-ren-∘-≐ʳ Γ₀ r₂ r₁))
           (cong-⟨⟩-ren-∘-≐ʳ (cong-ren {Γ'' = Γ₀} r₂) (cong-ren {Γ'' = Γ₀} r₁))

-- Forces a `with eternal?`-defined function to reduce, by rewriting the
-- scrutinee.

eternal?-yes : ∀ {A} → (et : Eternal A) → eternal? A ≡ yes et
eternal?-yes {A} et with eternal? A
... | yes et' = cong yes (eternal-irrelevant et' et)
... | no ¬et  = ⊥-elim (¬et et)

eternal?-no : ∀ {A} → (¬et : ¬ Eternal A) → eternal? A ≡ no ¬et
eternal?-no {A} ¬et with eternal? A
... | yes et  = ⊥-elim (¬et et)
... | no ¬et' = cong no (fun-ext (λ e → ⊥-elim (¬et e)))

⟨⟩-η⁻¹-img : ∀ {Γ A σ} → (x : A ∈[ σ ] Γ)
           → var-img (⟨⟩-η⁻¹-ren {Δ = Γ}) x ≡ (σ ·ᵣ uᵣ , Tl-⟨⟩ x)
⟨⟩-η⁻¹-img Hd        = refl
⟨⟩-η⁻¹-img (Tl-∷ x)  = refl
⟨⟩-η⁻¹-img (Tl-⟨⟩ x) = refl

-- A variable of a concatenation comes from one of the two parts.

-- The grade of a variable of the *right* part is unchanged: only that part's
-- locks stand to its right.

∈-++ᶜ-split : ∀ {A ρ} → (Δ₁ Δ₂ : Ctx) → A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂)
            → (Σ[ ρ' ∈ R ] A ∈[ ρ' ] Δ₁) ⊎ (A ∈[ ρ ] Δ₂)
∈-++ᶜ-split Δ₁ []         x        = inj₁ (_ , x)
∈-++ᶜ-split Δ₁ (Δ₂ ∷ B)   Hd       = inj₂ Hd
∈-++ᶜ-split Δ₁ (Δ₂ ∷ B)   (Tl-∷ x) with ∈-++ᶜ-split Δ₁ Δ₂ x
... | inj₁ p = inj₁ p
... | inj₂ y = inj₂ (Tl-∷ y)
∈-++ᶜ-split Δ₁ (Δ₂ ⟨ ρ ⟩) (Tl-⟨⟩ x) with ∈-++ᶜ-split Δ₁ Δ₂ x
... | inj₁ p = inj₁ p
... | inj₂ y = inj₂ (Tl-⟨⟩ y)

-- What the lookup's weakening does to a variable: it is the subst-free push
-- `∈-++ᶜˡ`, at the grade the suffix's locks contribute.

wk-ren-⟨ρ⟩-ctx-img : ∀ {Γ A σ ρ} → (Γ' : Ctx) → (h : ctx-grade Γ' ≡ ρ)
                   → (x : A ∈[ σ ] Γ)
                   → var-img (wk-ren-⟨ρ⟩-ctx {Γ} {Γ'} {ρ} h) (Tl-⟨⟩ x)
                   ≡ (grade-++ᶜˡ σ Γ' , ∈-++ᶜˡ Γ' x)

wk-ren-⟨ρ⟩-ctx-img []         refl x = refl
wk-ren-⟨ρ⟩-ctx-img (Γ' ∷ B)   refl x =
  cong (λ t → proj₁ t , Tl-∷ (proj₂ t)) (wk-ren-⟨ρ⟩-ctx-img Γ' refl x)
wk-ren-⟨ρ⟩-ctx-img (Γ' ⟨ ρ' ⟩) refl x =
  cong (λ t → proj₁ t ·ᵣ ρ' , Tl-⟨⟩ (proj₂ t)) (wk-ren-⟨ρ⟩-ctx-img Γ' refl x)

