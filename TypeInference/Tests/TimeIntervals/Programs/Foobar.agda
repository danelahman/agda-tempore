--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: `delay.tpe`'s `foobar`.                --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.Scopes

open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Programs.Foobar where

open LanguageSpec spec
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- `foobar ()`: `foo` instantiated at two delaying functions

F : ℕ → ∀ {Θ} → OVType Θ
F k = Base reading ⇒ Unit ‼ (d k ·̂ₑ ûₑ)

dl-foobar : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ _
dl-foobar =
  (foo · lam (delay 24 (return ⋆)))
  ⨟ ((#ᵛ (# 0) · lam (delay 23 (return ⋆))) ⨟ (#ᵛ (# 0) · const reading 7))
  where
    foo : ∅ᴴ ∣ ∅ᶜ ⊢V⦂ F 24 ⇒ (F 23 ⇒ (Base reading ⇒ Unit ‼
                          ((d 24 ·̂ₑ ûₑ) ·̂ₑ ((d 23 ·̂ₑ ûₑ) ·̂ₑ (d 42 ·̂ₑ ûₑ)))) ‼ ûₑ) ‼ ûₑ
    foo = lam (return (lam (return (lam
            ((#ᵛ (# 2) · #ᵛ (# 0))
              ⨟ ((#ᵛ (# 2) · #ᵛ (# 1)) ⨟ delay 42 (return ⋆)))))))

ex-dl-foobar : Outcome dl-foobar
ex-dl-foobar = ok (scope 48 0 38 , Unit ‼ d 89 , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
