------------------------------------------------------------------------
-- Packaging the free graded monad on discrete presheaves as an        --
-- instance of the abstract `Monad` interface.                          --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.Monad.Instance
         (S : LanguageSpec)
         (Wld : World (LanguageSpec.Grades S))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Effects S Wld GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Handling S Wld GTy

open import DenotationalSemantics.Model.Monad S
             (B.PShCat (LanguageSpec.Grades S) Wld)
             (F.PShFut (LanguageSpec.Grades S) Wld)
             GTy
           using (Monad)

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
  ; ηᵀ-nat              = ηᵀ-nat
  ; μᵀ-nat              = μᵀ-nat
  ; T-≤-nat             = T-≤-nat
  ; T-μ∘η≡id            = T-μ∘η≡id
  ; T-μ∘Tη≡id           = T-μ∘Tη≡id
  ; T-μ∘μ≡μ∘Tμ          = T-μ∘μ≡μ∘Tμ
  ; delayᵀ              = delayᵀ
  ; opᵀ                 = opᵀ
  ; delayᵀ-nat          = delayᵀ-nat
  ; opᵀ-nat             = opᵀ-nat
  ; delayᵀ-algebraicity = delayᵀ-algebraicity
  ; opᵀ-algebraicity    = opᵀ-algebraicity
  ; strᵀ                = strᵀ
  ; strᵀ-nat            = strᵀ-nat
  ; strᵀ-sndᵐ           = strᵀ-sndᵐ
  ; strᵀ-ηᵀ             = strᵀ-ηᵀ
  ; strᵀ-μᵀ             = strᵀ-μᵀ
  ; strᵀ-assoc          = strᵀ-assoc
  ; strᵀ-delayᵀ-algebraicity = strᵀ-delayᵀ-algebraicity
  ; strᵀ-opᵀ-algebraicity    = strᵀ-opᵀ-algebraicity
  ; T-alg-of-handlerᵀ        = T-alg-of-handlerᵀ
  ; T-alg-of-handlerᵀ-ηᵀ     = T-alg-of-handlerᵀ-ηᵀ
  ; T-alg-of-handlerᵀ-delayᵀ = T-alg-of-handlerᵀ-delayᵀ
  ; T-alg-of-handlerᵀ-opᵀ    = T-alg-of-handlerᵀ-opᵀ
  }
