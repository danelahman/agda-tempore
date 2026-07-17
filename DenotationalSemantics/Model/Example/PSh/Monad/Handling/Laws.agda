------------------------------------------------------------------------
-- Effect handling: the η / delay / op / sub-effecting algebra laws.    --
------------------------------------------------------------------------

{-# OPTIONS --lossy-unification #-}

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.Monad.Handling.Laws
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)

open import Util.Equality

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Effects S Wld GTy

open import DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ; map⇒ᵐ; exp-strᵐ; fstᵐ; sndᵐ; ⟨_,_⟩ᵐ; curryᵐ; appᵐ)

open import DenotationalSemantics.Model.Modality.BoxCoalg
  PShCat (GradeSystem.RGrade Grades) PShFut

open import DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core S Wld GTy

-- The three algebra laws (up to `_≈ᵗ_`): each side folds to the same tree
-- (returning / re-delaying / applying the clause to the rebuilt box).

T-alg-of-handlerᵀ-ηᵀ : ∀ {P A ε'} → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                     → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (ηᵀ {Tᵒ A ε'})
                     ≈ᵖ ε-substᵀ (sym (·ₑ-identityˡ ε')) ∘ᵖ sndᵐ
T-alg-of-handlerᵀ-ηᵀ bc h x = ≈ᵗ-refl _

T-alg-of-handlerᵀ-delayᵀ : ∀ {P A ε' ε''} → (τ : ℕ) → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                         → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (delayᵀ {Tᵒ A ε''} {ε'} τ)
                         ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                           ∘ᵖ delayᵀ τ
                           ∘ᵖ [ of-natʳ τ ]ᶠ (T-alg-of-handlerᵀ bc h)
                           ∘ᵖ []-monoidal
                           ∘ᵖ mapˣᵐ (BoxCoalg.necᵉ bc {of-natʳ τ}) idᵖ
T-alg-of-handlerᵀ-delayᵀ {P = P} τ bc h (pv , boxT) =
  ε-substˢ-congᵗ (sym (·ₑ-assoc (of-natᵉ τ) _ _))
    (delay-≈ (λ q → T-alg-of-handlerˢ-congᵖ bc h
                      (≈-sym P (BoxCoalg.necᵉ-≤ bc (≾ᵣ-reflexive map-of-natᵉ) pv q))
                      (fun boxT (⊑-coe map-of-natᵉ q))))

T-alg-of-handlerᵀ-≤ : ∀ {P A ε₁ ε₂ ε'} → (bc : BoxCoalg P) → (h : Handlerˢ P A) → (p : ε₁ ≾ₑ ε₂)
                    → T-alg-of-handlerᵀ {P} {A} {ε₂} {ε'} bc h ∘ᵖ mapˣᵐ idᵖ (T-≤ p)
                    ≈ᵖ T-≤ (·ₑ-monoˡ-≾ₑ p) ∘ᵖ T-alg-of-handlerᵀ {P} {A} {ε₁} {ε'} bc h
T-alg-of-handlerᵀ-≤ bc h p x = ≈ᵗ-refl _

T-alg-of-handlerᵀ-opᵀ : ∀ {P A ε' ε''} → (op : Op) → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                      → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (opᵀ {Tᵒ A ε''} {ε'} op)
                      ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε' ε''))
                        ∘ᵖ h op (ε' ·ₑ ε'')
                        ∘ᵖ ⟨ fstᵐ
                           , ⟨ fstᵐ ∘ᵖ sndᵐ
                             ,   [ mapᵉ (op-grade op) ]ᶠ
                                   (curryᵐ (T-alg-of-handlerᵀ bc h
                                     ∘ᵖ ⟨ fstᵐ ∘ᵖ fstᵐ
                                        , appᵐ ∘ᵖ ⟨ sndᵐ ∘ᵖ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ))
                               ∘ᵖ []-monoidal
                               ∘ᵖ mapˣᵐ (BoxCoalg.necᵉ bc {mapᵉ (op-grade op)}) idᵖ
                               ∘ᵖ ⟨ fstᵐ , sndᵐ ∘ᵖ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
T-alg-of-handlerᵀ-opᵀ {P = P} op bc h (pv , (v , boxk)) =
  ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) _ _))
    (app-cong (h op _)
      (≈-refl P ,
       (≈-refl ⟦ param op ⟧ᵍ ,
        (λ q p y → T-alg-of-handlerˢ-cong bc h
                     (fun-nat (app (BoxCoalg.necᵉ bc) pv) q p)
                     (fun-nat boxk q p ⊑-refl y)))))
