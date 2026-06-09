------------------------------------------
-- Renaming actions on well-typed terms --
------------------------------------------

open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.RenActions (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts  S
open import Syntax.Language  S
open import Syntax.Renamings S
open import Syntax.Types     S

-- Useful substitution of resource annotations

var-ρ-subst : ∀ {Γ A ρ ρ'}
            → ρ ≡ ρ'
            → A ∈[ ρ ] Γ
            → A ∈[ ρ' ] Γ
            
var-ρ-subst refl x = x

-- Renaming of variables

var-rename : ∀ {Γ Γ' A ρ}
           → Ren Γ Γ'
           → A ∈[ ρ ] Γ
           → Σ[ ρ' ∈ R ] (ρ' ≾ᵣ ρ × A ∈[ ρ' ] Γ')
           
var-rename id-ren x =
  _ , ≾ᵣ-refl , x
var-rename (r₂ ∘ʳ r₁) x with var-rename r₁ x
... | ρ' , ρ'≾ρ , y with var-rename r₂ y
... | ρ'' , ρ''≾ρ' , z =
  ρ'' , ≾ᵣ-trans ρ''≾ρ' ρ'≾ρ , z
var-rename wk-ren x =
  _ , ≾ᵣ-refl , Tl-∷ x
var-rename (var-ren p y) Hd =
  _ , p , y
var-rename (var-ren p y) (Tl-∷ x) =
  var-rename id-ren x
var-rename ⟨⟩-η-ren (Tl-⟨⟩ x) =
  _ , ≾ᵣ-reflexive (sym (·ᵣ-identityʳ _)) , x
var-rename ⟨⟩-η⁻¹-ren Hd =
  uᵣ ·ᵣ uᵣ , ≾ᵣ-reflexive (·ᵣ-identityʳ uᵣ) , Tl-⟨⟩ Hd
var-rename ⟨⟩-η⁻¹-ren (Tl-∷ x) =
  _ , ≾ᵣ-reflexive (·ᵣ-identityʳ _) , Tl-⟨⟩ (Tl-∷ x)
var-rename ⟨⟩-η⁻¹-ren (Tl-⟨⟩ x) =
  _ , ≾ᵣ-reflexive (·ᵣ-identityʳ (_ ·ᵣ _)) , Tl-⟨⟩ (Tl-⟨⟩ x)
var-rename ⟨⟩-μ-ren (Tl-⟨⟩ x) =
  _ , ≾ᵣ-reflexive (·ᵣ-assoc _ _ _) , Tl-⟨⟩ (Tl-⟨⟩ x)
var-rename ⟨⟩-μ⁻¹-ren (Tl-⟨⟩ (Tl-⟨⟩ x)) =
  _ , ≾ᵣ-reflexive (sym (·ᵣ-assoc _ _ _)) , Tl-⟨⟩ x
var-rename (⟨⟩-≤-ren {ρ = ρ₁} {ρ' = ρ₂} ρ₂≾ρ₁) (Tl-⟨⟩ x) =
  _ ·ᵣ ρ₂ , ·ᵣ-monoʳ-≾ᵣ ρ₂≾ρ₁ , Tl-⟨⟩ x
var-rename (cong-∷-ren r) Hd =
  uᵣ , ≾ᵣ-refl , Hd
var-rename (cong-∷-ren r) (Tl-∷ x) with var-rename r x
... | ρ' , ρ'≾ρ , y = ρ' , ρ'≾ρ , Tl-∷ y
var-rename (cong-⟨⟩-ren r) (Tl-⟨⟩ x) with var-rename r x
... | ρ' , ρ'≾ρ , y = ρ' ·ᵣ _ , ·ᵣ-monoˡ-≾ᵣ ρ'≾ρ , Tl-⟨⟩ y

-- Recovering the earlier variable-only unboxing rule as a special case of the
-- general value-based `unbox`: a variable `x : [ ρ ] A ∈[ ρ' ] Γ` for which
-- enough time has passed (`ρ' ≾ᵣ ρ`) is unboxed by viewing it as the value
-- `var _ Hd` typed in the earlier context `split-l x ∷ [ ρ ] A`, with the
-- witnessing renaming `Ren ((split-l x ∷ [ ρ ] A) ⟨ ρ ⟩) Γ` assembled from the
-- context splitting induced by `x`. In the paper's ℕ-graded setting this is
-- exactly the renaming `wk-ren-⟨ρ⟩-ctx ∘ʳ ⟨⟩-≤-ren` realising `Γ − ρ`.

unbox-var : ∀ {Γ A C ρ ρ'}
          → (x : [ ρ ] A ∈[ ρ' ] Γ)
          → ρ' ≾ᵣ ρ
          → Γ ∷ A ⊢C⦂ C
          → Γ ⊢C⦂ C
unbox-var x rel M =
  unbox
    (eq-ren (split-≡ (split-pf x))
     ∘ʳ wk-ren-⟨ρ⟩-ctx (split-grade-≡ x)
     ∘ʳ ⟨⟩-≤-ren rel)
    (var (λ _ → ≾ᵣ-refl) Hd)
    M

-- Extracting the underlying variable (and grade bound) from a value-based
-- unboxing. As graded modal types have no value introduction form, any value
-- of type `[ ρ ] A` is a variable; transporting it through the witnessing
-- renaming yields a variable in `Γ` together with the bound `ρ' ≾ᵣ ρ`. The
-- bound follows from the variable's own usage condition (`ρ_y ≾ᵣ uᵣ`, since
-- modal types are never eternal) combined with monotonicity of `_·ᵣ_`.

unbox⇒var : ∀ {Γ A ρ Δ}
          → Ren (Δ ⟨ ρ ⟩) Γ
          → Δ ⊢V⦂ [ ρ ] A
          → Σ[ ρ' ∈ R ] (([ ρ ] A ∈[ ρ' ] Γ) × ρ' ≾ᵣ ρ)
unbox⇒var {ρ = ρ} w V with grad-typ⇒var V
... | _ , y , f , _ with var-rename w (Tl-⟨⟩ y)
... | ρ' , ρ'≾ρy·ρ , z =
  ρ' , z ,
  ≾ᵣ-trans ρ'≾ρy·ρ
    (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (f (λ ()))) (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)))

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename r (var f x) with var-rename r x
  ... | _ , ρ'≾ρ , y = var (λ p → ≾ᵣ-trans ρ'≾ρ (f p)) y
  V-rename r (const c)   = const c
  V-rename r ⋆           = ⋆
  V-rename r (⦉ V , W ⦊)  = ⦉ V-rename r V , V-rename r W ⦊
  V-rename r (lam M)     = lam (C-rename (cong-ren r) M)

  C-rename : ∀ {Γ Γ' C}
           → Ren Γ Γ'
           → Γ ⊢C⦂ C
           ------------
           → Γ' ⊢C⦂ C

  C-rename r (return V)       = return (V-rename r V)
  C-rename r (M ⨟ N)          = C-rename r M ⨟ C-rename (cong-ren r) N
  C-rename r (V · W)          = V-rename r V · V-rename r W
  C-rename r (match V `in M)  = match V-rename r V `in C-rename (cong-ren r) M
  C-rename r (absurd V)       = absurd (V-rename r V)
  C-rename r (perform op V M) = perform op (V-rename r V) (C-rename (cong-ren r) M)
  C-rename r (delay τ M)      = delay τ (C-rename (cong-ren r) M)
  C-rename r (handle M `with H `in N) =
    handle C-rename r M
    `with (λ op ε'' Γ' → C-rename (cong-ren r) (H op ε'' Γ') )
    `in (C-rename (cong-ren r) N)
  C-rename r (unbox w V M) =
    unbox (r ∘ʳ w) V (C-rename (cong-ren r) M)
  C-rename r (box V M) = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)
  C-rename r (coerce rel M) = coerce rel (C-rename r M)
