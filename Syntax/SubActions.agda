----------------------------------------------
-- Substitution actions on well-typed terms --
----------------------------------------------

open import Syntax.Grades

module Syntax.SubActions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

open import Syntax.Contexts (Grades)
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

  V-substitute s (var x) =
    V-rename
      (proj₁ (proj₂ (proj₂ (var-sub s x))) ∘ʳ wk-ctx-renᵣ
        (c≾ᵣuᵣ⇒c≡uᵣ (ctx-grade (proj₁ (proj₂ (var-sub s x)))) (proj₂ (proj₂ (proj₂ (proj₂ (var-sub s x)))))))
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
  C-substitute {Γ} {Γ'} s (unbox {A} {C} {Γ₁} {Γ₂} {ρ} rel r V M) =
    unbox {A = A} {C = C} {Γ₁ = Γ₁ ++ᶜ proj₁ (ren-ctx-u Γ₂)} {Γ₂ = [] ⟨ ctx-grade Γ₂ ⟩} {ρ = ρ}
      (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ (ctx-grade Γ₂))) rel)
      {!!}
      (V-substitute (id-sub ∘ʳˢ wk-ctx-renᵣ {Γ₁} {proj₁ (ren-ctx-u Γ₂)} (proj₁ (proj₂ (ren-ctx-u Γ₂)))) V)
      (C-substitute (cong-sub s) M)
  C-substitute s (box V M) = box (V-substitute (cong-sub s) V) (C-substitute (cong-sub s) M)


{-
      (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ (ctx-grade Γ₂))) rel)
      (ren
        (≾ᵣ-trans
          (ctx-grade-≾ s)
          (≾ᵣ-trans
            (ctx-grade-≾ r)
            (≾ᵣ-reflexive
              (trans
                (ctx-grade-++ᶜ Γ₁ Γ₂)
                (sym (trans
                (ctx-grade-++ᶜ (Γ₁ ++ᶜ proj₁ (ren-ctx-u Γ₂)) ([] ⟨ ctx-grade Γ₂ ⟩))
                (trans
                  (sym (·ᵣ-assoc (ctx-grade (Γ₁ ++ᶜ proj₁ (ren-ctx-u Γ₂))) uᵣ (ctx-grade Γ₂)))
                  (trans
                    (·ᵣ-assoc (ctx-grade (Γ₁ ++ᶜ proj₁ (ren-ctx-u Γ₂))) uᵣ (ctx-grade Γ₂))
                    (cong₂ _·ᵣ_
                      (trans
                        (ctx-grade-++ᶜ Γ₁ (proj₁ (ren-ctx-u Γ₂)))
                        (trans
                          (cong (_·ᵣ_ (ctx-grade Γ₁)) (proj₁ (proj₂ (ren-ctx-u Γ₂))))
                          (·ᵣ-identityʳ (ctx-grade Γ₁))))
                      (·ᵣ-identityˡ (ctx-grade Γ₂)))) ) ))))))
        (λ x → {!!} , {!!}))
      (V-substitute (id-sub ∘ʳˢ wk-ctx-renᵣ {Γ₁} {proj₁ (ren-ctx-u Γ₂)} (proj₁ (proj₂ (ren-ctx-u Γ₂)))) V)
      (C-substitute (cong-sub s) M)

-}
