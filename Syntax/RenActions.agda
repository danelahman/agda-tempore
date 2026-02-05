{-# OPTIONS --allow-unsolved-metas #-} -- remove

------------------------------------------
-- Renaming actions on well-typed terms --
------------------------------------------

open import Syntax.Grades

module Syntax.RenActions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Extensions.Raw (Grades)

open import Syntax.Extensions (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Language (Grades)
open import Syntax.Contexts (Grades)

open import Util.Equality

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename r (var x) =
    var
    (var-ρ-subst
      (c≾ᵣuᵣ⇒c≡uᵣ (proj₁ (var-rename r x)) (proj₁ (proj₂ (var-rename r x))))
      (proj₂ (proj₂ (var-rename r x))))
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
  C-rename r (M ; N)          = C-rename r M ; C-rename (cong-ren r) N
  C-rename r (V · W)          = V-rename r V · V-rename r W
  C-rename r (match V `in M)  = match V-rename r V `in C-rename (cong-ren r) M
  C-rename r (absurd V)       = absurd (V-rename r V)
  C-rename r (perform op V M) = perform op (V-rename r V) (C-rename (cong-ren r) M)
  C-rename r (delay τ M)      = delay τ (C-rename (cong-ren r) M)
  C-rename r (handle M `with H `in N) =
    handle C-rename r M
    `with (λ op τ'' → C-rename (cong-ren r) (H op τ'') )
    `in (C-rename (cong-ren r) N)
  C-rename r (unbox {A} {C} {Γ''} {ρ} {ρ'} ex rel V M) =
    unbox {A = A} {Γ' = Γ''} {ρ = ρ} {ρ' = ρ'}
      {!!} 
      rel
      (V-rename id-ren V) -- (V-rename id-ren V)
      (C-rename (cong-ren r) M)
  {-
  C-rename r (unbox {A} {C} {Γ'} {ρ} ex relGrades rel V M) =
    unbox {A = A} {Γ' = Γ'} {ρ = ρ} 
      (r ∘ᵉʳ ex)
      (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ ρ (ctx-grade-≾ r)) relGrades)
      (≾ᵣ-trans (ctx-grade-≾ r) rel)
      (V-rename id-ren V)
      (C-rename (cong-ren r) M)
  -}
  {- Previous version:
  C-rename r (unbox {A} {C} {Γ₁} {Γ₂} {ρ} rel r' V M) =
    unbox {A = A} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ρ = ρ}
      rel
      (r ∘ʳ r')
      (V-rename id-ren V)
      (C-rename (cong-ren r) M)
  -}
  C-rename r (box V M) = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)

  -- sub-effecting
  C-rename r (coerce M relEff) = coerce (C-rename r M) relEff
