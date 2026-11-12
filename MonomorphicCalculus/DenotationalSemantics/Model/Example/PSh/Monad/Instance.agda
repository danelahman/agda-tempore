------------------------------------------------------------------------
-- Packaging the graded tree monad on presheaves as an instance of    --
-- the abstract `Monad` interface.                                    --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past as P
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction as A

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Instance
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Product using (_,_)

open import Language.Operations
open LanguageSpec S using (Ops)
open Operations Ops using (param)
open World Wld using (⊑-refl)
open GroundTypes GTy using (⟦_⟧ᵍ)
open B (LanguageSpec.Grades S) Wld using (app; app-cong; ≈-refl; fun-irr)
open F (LanguageSpec.Grades S) Wld using (fun; fun-nat; []-fun-irr)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Effects S Wld GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling S Wld GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.HandlerValues S Wld GTy

open import MonomorphicCalculus.DenotationalSemantics.Model.Monad S
             (B.PShCat (LanguageSpec.Grades S) Wld)
             (F.PShFut (LanguageSpec.Grades S) Wld)
             (P.PShPast (LanguageSpec.Grades S) Wld)
             (A.PShAdj (LanguageSpec.Grades S) Wld)
             GTy
           using (Monad)
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
             (B.PShCat (LanguageSpec.Grades S) Wld)
             (GradeSystem.RGrade (LanguageSpec.Grades S))
             (F.PShFut (LanguageSpec.Grades S) Wld)
             (P.PShPast (LanguageSpec.Grades S) Wld)
             (A.PShAdj (LanguageSpec.Grades S) Wld)
           using (module Eternalᵒ)

-- The two laws at an operation are proved here, against the interface's
-- statements; a lemma stated in another module would be compared with
-- them by normalising both sides to their trees. For the strength, both
-- sides build the same `op-node`, whose sub-computations are strengthened
-- with box witnesses that agree by `[]-fun-irr`; for the handler's fold,
-- both sides apply the operation's clause to arguments that agree by
-- naturality.

PShMonad : Monad
PShMonad = record
  { Tᵒ                  = Tᵒ
  ; Tᶠ                  = Tᶠ
  ; ηᵀ                  = ηᵀ
  ; μᵀ                  = μᵀ
  ; ε-substᵀ            = ε-substᵀ
  ; ε-substᵀ-refl       = ε-substᵀ-refl
  ; ε-substᵀ-trans      = ε-substᵀ-trans
  ; T-≤                 = T-≤
  ; T-idᵐ               = Tᶠ-id
  ; T-∘ᵐ                = Tᶠ-∘
  ; T-congᶠ             = T-congᶠ
  ; ηᵀ-nat              = ηᵀ-nat
  ; μᵀ-nat              = μᵀ-nat
  ; T-≤-nat             = T-≤-nat
  ; T-≤-refl            = T-≤-refl
  ; T-≤-trans           = T-≤-trans
  ; T-≤-≡               = T-≤-≡
  ; T-≤-μᵀ              = T-≤-μᵀ
  ; T-≤-μᵀⁱ             = T-≤-μᵀⁱ
  ; strᵀ-≤              = strᵀ-≤
  ; T-μ∘η≡id            = T-μ∘η≡id
  ; T-μ∘Tη≡id           = T-μ∘Tη≡id
  ; T-μ∘μ≡μ∘Tμ          = T-μ∘μ≡μ∘Tμ
  ; delayᵀ              = delayᵀ
  ; opᵀ                 = opᵀ
  ; delayᵀ-zero         = delayᵀ-zero
  ; delayᵀ-plus         = delayᵀ-plus
  ; delayᵀ-nat          = delayᵀ-nat
  ; delayᵀ-≤            = delayᵀ-≤
  ; opᵀ-nat             = opᵀ-nat
  ; opᵀ-≤               = opᵀ-≤
  ; delayᵀ-algebraicity = delayᵀ-algebraicity
  ; opᵀ-algebraicity    = opᵀ-algebraicity
  ; strᵀ                = strᵀ
  ; strᵀ-nat            = strᵀ-nat
  ; strᵀ-sndᵐ           = strᵀ-sndᵐ
  ; strᵀ-ηᵀ             = strᵀ-ηᵀ
  ; strᵀ-μᵀ             = strᵀ-μᵀ
  ; strᵀ-assoc          = strᵀ-assoc
  ; strᵀ-delayᵀ-algebraicity = strᵀ-delayᵀ-algebraicity
  ; strᵀ-opᵀ-algebraicity    = λ {A} op (a , v , boxk) →
      op-≈ (≈-refl ⟦ param op ⟧ᵍ)
        (λ q y → strˢ-congᵗ A (λ r → []-fun-irr a _ _) (fun-irr (fun boxk q) _ _ y))
  ; T-alg-of-handlerᵀ        = T-alg-of-handlerᵀ
  ; T-alg-of-handlerᵀ-ηᵀ     = T-alg-of-handlerᵀ-ηᵀ
  ; T-alg-of-handlerᵀ-delayᵀ = T-alg-of-handlerᵀ-delayᵀ
  ; T-alg-of-handlerᵀ-opᵀ    = λ {X} op bc h (pv , v , boxk) →
      sub-congᵗ
        (app-cong (clause h op _)
          (≈-refl X ,
           (≈-refl ⟦ param op ⟧ᵍ ,
            (λ q p y → T-alg-of-handlerˢ-cong bc h
                         (fun-nat (app (Eternalᵒ.necᵉ bc) pv) q p)
                         (fun-nat boxk q p ⊑-refl y)))))
  ; T-alg-of-handlerᵀ-≤      = T-alg-of-handlerᵀ-≤
  ; T-alg-of-handlerᵀ-≤ⁱ     = T-alg-of-handlerᵀ-≤ⁱ
  ; T-alg-of-handlerᵀ-μᵀ     = T-alg-of-handlerᵀ-μᵀ
  ; T-alg-of-handlerᵀ-natᴾ   = T-alg-of-handlerᵀ-natᴾ′
  ; T-alg-of-handlerᵀ-cong   = T-alg-of-handlerᵀ-cong
  ; Hᵒ                       = Hᵖ
  ; appʰ                     = appʰᵖ
  ; appʰ-nat                 = λ {A} {ε} {B} {ε'} → appʰᵖ-nat {A} {ε} {B} {ε'}
  ; curryʰ                   = curryʰᵖ
  ; curryʰ-cong              = λ {X} {A} {ε} {B} {ε'} {f} {g} →
                                 curryʰᵖ-cong {X} {A} {ε} {B} {ε'} {f} {g}
  ; curryʰ-β                 = curryʰᵖ-β
  ; curryʰ-η                 = λ h → curryʰᵖ-η h (appʰᵖ-∘-nat h)
  }
