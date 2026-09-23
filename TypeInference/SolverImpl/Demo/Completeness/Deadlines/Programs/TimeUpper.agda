--------------------------------------------------------------------------------
-- Completeness checks at deadlines: `time_upper.tpe`.                        --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs.TimeUpper where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   specᵈ
open import TypeInference.OpenSyntax.Types    specᵈ
open import TypeInference.OpenSyntax.Contexts specᵈ
open import TypeInference.OpenSyntax.Hyps     specᵈ
open import TypeInference.OpenSyntax.Language specᵈ

open M

-- `time_upper.tpe`, `foo1`: two delays spend the three ticks the box
-- allows

tu-foo1 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
tu-foo1 = box (rconst (of-natʳ 3)) (const reading 1)
            (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd))))

ex-tu-foo1 : Verdict tu-foo1
ex-tu-foo1 = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!

-- `foo2`: two of the three ticks

tu-foo2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
tu-foo2 = box (rconst (of-natʳ 3)) (const reading 1)
            (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 1)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd)))

ex-tu-foo2 : Verdict tu-foo2
ex-tu-foo2 = ok (Base reading) (econst (of-natᵉ 2)) refl ≤!
