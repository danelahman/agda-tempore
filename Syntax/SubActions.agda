----------------------------------------------
-- Substitution actions on well-typed terms --
----------------------------------------------

open import Syntax.Grades

module Syntax.SubActions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

open import Relation.Nullary

open import Syntax.Extensions.Raw (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Extensions (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.RenActions (Grades)
open import Syntax.Substitutions (Grades)

-- Action of substitutions on well-typed values and computations

mutual

  V-substitute : ∀ {Γ Γ' A}
               → Sub Γ Γ'
               → Γ ⊢V⦂ A
               ------------
               → Γ' ⊢V⦂ A

  V-substitute {Γ} {Γ'} s (var x) =
    V-rename
      (proj₁ (proj₂ (proj₂ (var-sub s x))) ∘ʳ
        wk-ctx-renᵣ
          (c≾ᵣuᵣ⇒c≡uᵣ (ctx-grade (proj₁ (proj₂ (var-sub s x))))
          (proj₂ (proj₂ (proj₂ (proj₂ (var-sub s x)))))))
      (proj₁ (proj₂ (proj₂ (proj₂ (var-sub s x)))))
  V-substitute s (const c) = const c
  V-substitute s ⋆         = ⋆
  V-substitute s ⦉ V , W ⦊ = ⦉ V-substitute s V , V-substitute s W ⦊
  V-substitute s (lam M)   = lam (C-substitute (cong-sub s) M)

  C-substitute : ∀ {Γ Γ' C}
               → Sub Γ Γ'
               → Γ ⊢C⦂ C
               ------------
               → Γ' ⊢C⦂ C

  C-substitute s (return V)               = return (V-substitute s V)
  C-substitute s (M ; N)                  = C-substitute s M ; C-substitute (cong-sub s) N
  C-substitute s (V · W)                  = V-substitute s V · V-substitute s W
  C-substitute s (match V `in M)          = match V-substitute s V `in C-substitute (cong-sub s) M
  C-substitute s (absurd V)               = absurd (V-substitute s V)
  C-substitute s (perform op V M)         = perform op (V-substitute s V) (C-substitute (cong-sub s) M)
  C-substitute s (delay τ M)              = delay τ (C-substitute (cong-sub s) M)
  C-substitute s (handle M `with H `in N) =
    handle C-substitute s M
    `with (λ op τ → C-substitute (cong-sub s) (H op τ))
    `in (C-substitute (cong-sub s) N)
  C-substitute {Γ} {Γ'} s (unbox {A} {C} {Γ''} {ρ} e rel V M) =
    unbox {A = A} {C = C} {ρ = ρ}
      (id-ext (≾ᵣ-trans (ctx-grade-≾ s) rel)) --id-ext
      (≾ᵣ-trans (ctx-grade-≾ s) rel) --(c·ᵣd≾ᵣc (ctx-grade Γ') ρ)
      (V-substitute (s ∘ᵉˢ e) V)
      (C-substitute (cong-sub s) M)
  C-substitute s (box V M) = box (V-substitute (cong-sub s) V) (C-substitute (cong-sub s) M)

  -- sub-effecting
  C-substitute s (coerce M relEff) = coerce (C-substitute s M) relEff
