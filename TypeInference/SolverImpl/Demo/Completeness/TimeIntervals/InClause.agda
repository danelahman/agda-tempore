--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: a handler inside a       --
-- clause, by a family choosing per operation.                                --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (write)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.InClause where

open LanguageSpec spec
open Operations Ops

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- H × H inside a clause: `write` handled by a clause that itself handles

h-in-clause : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst (op-grade write) ·̂ₑ ûₑ) ·̂ₑ ûₑ)
h-in-clause = handle perform write (const reading 0) (return ⋆)
              `with at writeNests ∅ᴴ ∅ᶜ `in (return ⋆)

ex-h-in-clause : Verdict h-in-clause
ex-h-in-clause = ok Unit (econst (op-grade write)) refl ≤!
