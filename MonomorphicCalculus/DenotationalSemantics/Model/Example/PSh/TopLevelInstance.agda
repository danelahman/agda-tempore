------------------------------------------------------------------------
-- The free graded tick monad, and the implementation running the     --
-- operations, as instances of `Model.TickMonad` and                  --
-- `Model.Implementation`.                                            --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past as P
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction as Aj

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.TopLevelInstance
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.TickMonad S Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Implementation S Wld GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Instance S Wld GTy

open import MonomorphicCalculus.DenotationalSemantics.Model.TickMonad S
             (B.PShCat (LanguageSpec.Grades S) Wld)
             (F.PShFut (LanguageSpec.Grades S) Wld)
           using (TickMonad)

open import MonomorphicCalculus.DenotationalSemantics.Model.Implementation S
             (B.PShCat (LanguageSpec.Grades S) Wld)
             (F.PShFut (LanguageSpec.Grades S) Wld)
             (P.PShPast (LanguageSpec.Grades S) Wld)
             (Aj.PShAdj (LanguageSpec.Grades S) Wld)
             GTy
             PShMonad
           using (Implementation)

PShTickMonad : TickMonad
PShTickMonad = record
  { Tᵏ           = Tᵏ
  ; Tᵏᶠ          = Tᵏᶠ
  ; ηᵏ           = ηᵏ
  ; μᵏ           = μᵏ
  ; ε-substᵏ     = ε-substᵏ
  ; ε-substᵏ-refl = ε-substᵏ-refl
  ; T-≤ᵏ         = T-≤ᵏ
  ; Tᵏ-idᵐ       = Tᵏ-idᵐ
  ; Tᵏ-∘ᵐ        = Tᵏ-∘ᵐ
  ; Tᵏ-congᶠ     = Tᵏ-congᶠ
  ; ηᵏ-nat       = ηᵏ-nat
  ; μᵏ-nat       = μᵏ-nat
  ; T-≤ᵏ-nat     = T-≤ᵏ-nat
  ; T-≤ᵏ-refl    = T-≤ᵏ-refl
  ; T-≤ᵏ-trans   = T-≤ᵏ-trans
  ; T-≤ᵏ-≡       = T-≤ᵏ-≡
  ; T-≤ᵏ-μᵏ      = T-≤ᵏ-μᵏ
  ; Tᵏ-μ∘η≡id    = Tᵏ-μ∘η≡id
  ; Tᵏ-μ∘Tη≡id   = Tᵏ-μ∘Tη≡id
  ; Tᵏ-μ∘μ≡μ∘Tμ  = Tᵏ-μ∘μ≡μ∘Tμ
  ; tickᵏ        = tickᵏ
  ; tickᵏ-nat    = tickᵏ-nat
  ; tickᵏ-algebraicity = tickᵏ-algebraicity
  ; tickᵏ-≤      = tickᵏ-≤
  }

-- For any semantic implementation of the operations.

PShImplementation : OpSemᵐ → Implementation PShTickMonad
PShImplementation op-semᵐ = record
  { op-semᵐ       = op-semᵐ
  ; implᵐ         = implᵐ op-semᵐ
  ; implᵐ-ηᵀ      = implᵐ-ηᵀ op-semᵐ
  ; implᵐ-μᵀ      = implᵐ-μᵀ op-semᵐ
  ; implᵐ-nat     = implᵐ-nat op-semᵐ
  ; implᵐ-T-≤     = implᵐ-T-≤ op-semᵐ
  ; implᵐ-ε-subst = implᵐ-ε-subst op-semᵐ
  ; implᵐ-delayᵀ  = implᵐ-delayᵀ op-semᵐ
  ; implᵐ-opᵀ     = implᵐ-opᵀ op-semᵐ
  }
