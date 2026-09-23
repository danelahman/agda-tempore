--------------------------------------------------------------------------------
-- Completeness checks at timed traces: what these grades see.                --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Operations using (read; write; ⌈_⌉; _∙_)
open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
  using (within_; ⟅_⟆)

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec)

open import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Permit where

open LanguageSpec spec
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- B × P × U: a permit naming a reading and then a store, opened once
-- both are done

permit : R
permit = within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆

logged : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ _
logged = box (rconst permit) true
           (perform read ⋆
             (perform write (v Hd)
               (unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd)))))

ex-logged : Verdict logged
ex-logged = ok Bool (econst (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)) refl ≤!
