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

-- A VARIABLE'S IMAGE IS A VALUE
--
-- The grade bound is an argument, not a result: producing a *value* out of a
-- variable needs the `var` rule's own premise. It is also what pays for
-- crossing a lock, `≾ᵣ-zero-productʳ` extracting the lock's own grade from it.
--
-- The lock rule takes the eternality decision as a parameter rather than
-- matching on it, so a caller deciding it reduces this too.
--
-- The renaming rule reads `var-rename` off with projections rather than a
-- `with`, so that the clause reduces to a `var` node at an abstract renaming.

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

-- A RESOURCE VARIABLE'S IMAGE IS A RESOURCE VARIABLE
--
-- A variable of box type is what an `unbox` names. Its grade is not bounded by
-- the unit — that is what `unbox` is for — so it cannot be read as a value by
-- `sub-var₀`. It does not have to be: the only values of box type are variables
-- (`grad-typ⇒var`), so its image is again a variable, at a grade that drops.
--
-- Stated with projections throughout, so that every clause reduces at an
-- abstract substitution: the image is what an `unbox` node stores, and what
-- `_≐ˢ₀_` compares.

sub-tgt₀ : ∀ {Δ Δ' A ρ σ}
         → Sub₀ [] Δ Δ'
         → [ ρ ] A ∈[ σ ] Δ'
         --------------------------------------------------
         → Σ[ σ' ∈ R ] (([ ρ ] A ∈[ σ' ] Δ) × (σ' ≾ᵣ σ))

sub-tgt₀ ⌜ r ⌝ y = rvar-rename r y
-- the substituted value is of box type, hence a variable
sub-tgt₀ (val-sub V) Hd =
    proj₁ (grad-typ⇒var V)
  , proj₁ (proj₂ (grad-typ⇒var V))
  , proj₁ (proj₂ (proj₂ (grad-typ⇒var V))) (λ ())
sub-tgt₀ (val-sub V) (Tl-∷ y) = _ , y , ≾ᵣ-refl
sub-tgt₀ (cong-∷-sub s) Hd = _ , Hd , ≾ᵣ-refl
sub-tgt₀ (cong-∷-sub s) (Tl-∷ y) =
    proj₁ (sub-tgt₀ s y)
  , Tl-∷ (proj₁ (proj₂ (sub-tgt₀ s y)))
  , proj₂ (proj₂ (sub-tgt₀ s y))
sub-tgt₀ (cong-⟨⟩-sub s) (Tl-⟨⟩ y) =
    proj₁ (sub-tgt₀ s y) ·ᵣ _
  , Tl-⟨⟩ (proj₁ (proj₂ (sub-tgt₀ s y)))
  , ·ᵣ-monoˡ-≾ᵣ (proj₂ (proj₂ (sub-tgt₀ s y)))
