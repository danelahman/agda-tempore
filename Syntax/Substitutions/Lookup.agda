-------------------------------------------------------
-- What a parallel substitution does to a variable    --
-------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Substitutions.Lookup (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

open import Syntax.Substitutions.Base S

-- Both observations are stated at the empty ambient, which is where the action
-- lives and where `[] ⋈ᶜ Δ` reduces to `Δ`, so nothing here is transported.
-- Neither calls the term action, so both recurse on the substitution alone.

-- The grade bound is an argument, not a result: producing a value out of a
-- variable needs the `var` rule's own premise. It also pays for crossing a
-- lock, `≾ᵣ-zero-productʳ` extracting the lock's own grade from it.
--
-- The lock rule takes the eternality decision as a parameter rather than
-- matching on it.
--
-- The renaming rule reads `var-rename` off with projections rather than a
-- `with`, so the clause reduces to a `var` node at an abstract renaming.

mutual

  sub-var₀ : ∀ {Δ Δ' A ρ}
           → Sub₀ [] Δ Δ'
           → A ∈[ ρ ] Δ'
           → (¬ Eternal A → ρ ≾ᵣ uᵣ)
           ---------------------------
           → Δ ⊢V⦂ A

  sub-var₀ ⌜ r ⌝ x f =
    var (λ ¬et → ≾ᵣ-trans (proj₁ (proj₂ (var-rename r x)) ¬et) (f ¬et))
        (proj₂ (proj₂ (var-rename r x)))
  sub-var₀ (val-sub V) Hd       f = V
  sub-var₀ (val-sub V) (Tl-∷ y) f = var f y
  sub-var₀ (cong-∷-sub s) Hd       f = var f Hd
  sub-var₀ (cong-∷-sub s) (Tl-∷ y) f = V-rename wk-ren (sub-var₀ s y f)
  sub-var₀ {A = A} (cong-⟨⟩-sub s) (Tl-⟨⟩ y) f =
    sub-var₀-⟨⟩ s y f (eternal? A)

  -- Crossing a lock. An eternal-typed value is available at any grade
  -- extension; otherwise the bound splits, its right factor collapsing the
  -- lock (`⟨⟩-≤-ren` then `⟨⟩-η⁻¹-ren`) and its left factor being what the
  -- image under `s` is formed with.

  sub-var₀-⟨⟩ : ∀ {Δ Δ' A ρ ρ'}
              → Sub₀ [] Δ Δ'
              → A ∈[ ρ' ] Δ'
              → (¬ Eternal A → ρ' ·ᵣ ρ ≾ᵣ uᵣ)
              → Dec (Eternal A)
              ----------------------------------
              → Δ ⟨ ρ ⟩ ⊢V⦂ A

  sub-var₀-⟨⟩ s y f (yes et) =
    eternal-val-ext et (sub-var₀ s y (λ ¬et → ⊥-elim (¬et et)))
  sub-var₀-⟨⟩ s y f (no ¬et) =
    V-rename
      (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)))
      (sub-var₀ s y (λ ¬et' → ≾ᵣ-zero-productˡ (f ¬et')))

-- A variable of box type is what an `unbox` names. Its grade is not bounded
-- by the unit, so `sub-var₀` cannot read it as a value; its image is again a
-- variable, at a grade that drops and at a declared box type the named one
-- only bounds.
--
-- Stated with projections throughout, so every clause reduces at an abstract
-- substitution: the image is what an `unbox` node stores, and what `_≐ˢ₀_`
-- compares.

sub-tgt₀ : ∀ {Δ Δ' A ρ σ}
         → Sub₀ [] Δ Δ'
         → [ ρ ] A ∈[ σ ] Δ'
         ----------------------------------------------------
         → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Σ[ σ' ∈ R ]
             (([ ρ₀ ] A₀ ∈[ σ' ] Δ)
               × (([ ρ₀ ] A₀) <:ᵛ ([ ρ ] A)) × (σ' ≾ᵣ σ))

sub-tgt₀ {A = A} {ρ = ρ} ⌜ r ⌝ y =
    ρ , A
  , proj₁ (rvar-rename r y)
  , proj₁ (proj₂ (rvar-rename r y))
  , <:ᵛ-refl ([ ρ ] A)
  , proj₂ (proj₂ (rvar-rename r y))
-- the substituted value is of box type, hence a variable up to subsumption
sub-tgt₀ (val-sub V) Hd = grad-typ⇒var<: V
sub-tgt₀ {A = A} {ρ = ρ} (val-sub V) (Tl-∷ y) =
  ρ , A , _ , y , <:ᵛ-refl ([ ρ ] A) , ≾ᵣ-refl
sub-tgt₀ {A = A} {ρ = ρ} (cong-∷-sub s) Hd =
  ρ , A , _ , Hd , <:ᵛ-refl ([ ρ ] A) , ≾ᵣ-refl
sub-tgt₀ (cong-∷-sub s) (Tl-∷ y) =
  let (ρ₀ , A₀ , σ' , z , p , q) = sub-tgt₀ s y in
  ρ₀ , A₀ , σ' , Tl-∷ z , p , q
sub-tgt₀ (cong-⟨⟩-sub s) (Tl-⟨⟩ y) =
  let (ρ₀ , A₀ , σ' , z , p , q) = sub-tgt₀ s y in
  ρ₀ , A₀ , σ' ·ᵣ _ , Tl-⟨⟩ z , p , ·ᵣ-monoˡ-≾ᵣ q

-- Named accessors for the components of `sub-tgt₀`.

tgt-grade₀ : ∀ {Δ Δ' A ρ σ} → Sub₀ [] Δ Δ' → [ ρ ] A ∈[ σ ] Δ' → R
tgt-grade₀ s y = proj₁ (sub-tgt₀ s y)

tgt-type₀ : ∀ {Δ Δ' A ρ σ} → Sub₀ [] Δ Δ' → [ ρ ] A ∈[ σ ] Δ' → VType
tgt-type₀ s y = proj₁ (proj₂ (sub-tgt₀ s y))

tgt-elapsed₀ : ∀ {Δ Δ' A ρ σ} → Sub₀ [] Δ Δ' → [ ρ ] A ∈[ σ ] Δ' → R
tgt-elapsed₀ s y = proj₁ (proj₂ (proj₂ (sub-tgt₀ s y)))

tgt-var₀ : ∀ {Δ Δ' A ρ σ} → (s : Sub₀ [] Δ Δ') → (y : [ ρ ] A ∈[ σ ] Δ')
         → [ tgt-grade₀ s y ] tgt-type₀ s y ∈[ tgt-elapsed₀ s y ] Δ
tgt-var₀ s y = proj₁ (proj₂ (proj₂ (proj₂ (sub-tgt₀ s y))))

tgt-<:₀ : ∀ {Δ Δ' A ρ σ} → (s : Sub₀ [] Δ Δ') → (y : [ ρ ] A ∈[ σ ] Δ')
        → ([ tgt-grade₀ s y ] tgt-type₀ s y) <:ᵛ ([ ρ ] A)
tgt-<:₀ s y = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (sub-tgt₀ s y)))))

tgt-≾₀ : ∀ {Δ Δ' A ρ σ} → (s : Sub₀ [] Δ Δ') → (y : [ ρ ] A ∈[ σ ] Δ')
       → tgt-elapsed₀ s y ≾ᵣ σ
tgt-≾₀ s y = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (sub-tgt₀ s y)))))

-- The two halves of that witness, which an `unbox` node keeps apart.

tgt-grade-≾₀ : ∀ {Δ Δ' A ρ σ} → (s : Sub₀ [] Δ Δ') → (y : [ ρ ] A ∈[ σ ] Δ')
             → ρ ≾ᵣ tgt-grade₀ s y
tgt-grade-≾₀ s y = <:ᵛ-box-grade (tgt-<:₀ s y)

tgt-type-<:₀ : ∀ {Δ Δ' A ρ σ} → (s : Sub₀ [] Δ Δ') → (y : [ ρ ] A ∈[ σ ] Δ')
             → tgt-type₀ s y <:ᵛ A
tgt-type-<:₀ s y = <:ᵛ-box-type (tgt-<:₀ s y)
