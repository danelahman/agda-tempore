------------------------------------------------------------------------
-- Parametric derivations.                                             --
-- The interpretation is defined only on terms with a parametricity    --
-- certificate (`Paramᵛ`/`Paramᶜ`), which the equational theory does   --
-- not preserve in either direction.                                   --
-- `Midᵛ`/`Midᶜ` collect the certificates a derivation's endpoints     --
-- do not already determine.                                           --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module EquationalTheory.Soundness.Parametric
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Language   S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.Soundness.Fill S Cat Fut Pst Adj GTy Mon GE using (Paramᵏ)

mutual

  Midᵛ : ∀ {Γ A} {V W : Γ ⊢V⦂ A} → Γ ⊢V⦂ V == W → Set

  Midᵛ (V-sym p)                         = Midᵛ p
  Midᵛ (V-trans {W = W} p q)             = Paramᵛ W × Midᵛ p × Midᵛ q
  Midᵛ (V-subst {V = V} {W = W} p x q U) = Paramᵛ V × Paramᵛ W × Paramᵛ U × Midᵛ p
  Midᵛ (⦉⦊-cong p q)                     = Midᵛ p × Midᵛ q
  Midᵛ (succ-cong p)                     = Midᵛ p
  Midᵛ (inl-cong p)                      = Midᵛ p
  Midᵛ (inr-cong p)                      = Midᵛ p
  Midᵛ (lam-cong p)                      = Midᶜ p
  Midᵛ (subV-cong p)                     = Midᵛ p
  Midᵛ _                                 = ⊤

  Midᶜ : ∀ {Γ C} {M N : Γ ⊢C⦂ C} → Γ ⊢C⦂ M == N → Set

  Midᶜ (C-sym p)                         = Midᶜ p
  Midᶜ (C-trans {N = N} p q)             = Paramᶜ N × Midᶜ p × Midᶜ q
  Midᶜ (C-subst {M = M} {N = N} p x q V) = Paramᶜ M × Paramᶜ N × Paramᵛ V × Midᶜ p
  Midᶜ (return-cong p)                   = Midᵛ p
  Midᶜ (seq-cong p q)                    = Midᶜ p × Midᶜ q
  Midᶜ (app-cong p q)                    = Midᵛ p × Midᵛ q
  Midᶜ (match-cong p q)                  = Midᵛ p × Midᶜ q
  Midᶜ (absurd-cong p)                   = Midᵛ p
  Midᶜ (if-cong p q r)                   = Midᵛ p × Midᶜ q × Midᶜ r
  Midᶜ (caseℕ-cong p q r)                = Midᵛ p × Midᶜ q × Midᶜ r
  Midᶜ (case+-cong p q r)                = Midᵛ p × Midᶜ q × Midᶜ r
  Midᶜ (recℕ-cong p q r)                 = Midᵛ p × Midᶜ q × Midᶜ r
  Midᶜ (perform-cong p q)                = Midᵛ p × Midᶜ q
  Midᶜ (delay-cong p)                    = Midᶜ p
  Midᶜ (handle-cong p hs q)              =
    Midᶜ p × ((op : Op) → (ε'' : E) → Midᶜ (hs op ε'')) × Midᶜ q
  Midᶜ (unbox-cong q)                    = Midᶜ q
  Midᶜ (box-cong p q)                    = Midᵛ p × Midᶜ q
  Midᶜ (subC-cong p)                     = Midᶜ p
  -- The two *axioms* whose endpoints do not determine all the certificates,
  -- because each mentions its body only under a renaming or a substitution
  -- (and neither `renᶜ` nor `subᶜ` is invertible): `match-eta`'s `M` occurs
  -- substituted on both sides, and `delay-delay`'s occurs renamed on the left
  -- and under an `ε-subst` on the right.
  Midᶜ (match-eta V M)                   = Paramᶜ M
  Midᶜ (if-eta V M)                      = Paramᶜ M
  Midᶜ (caseℕ-eta V M)                   = Paramᶜ M
  Midᶜ (case+-eta V M)                   = Paramᶜ M
  Midᶜ (delay-delay M)                   = Paramᶜ M
  -- `unbox-beta` mentions `K` and `N` only inside the filled context.
  Midᶜ (unbox-beta V K p w N)            = Paramᵏ K × Paramᶜ N
  Midᶜ _                                 = ⊤
