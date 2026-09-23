--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: `operations.tpe`.        --
--------------------------------------------------------------------------------

open import Data.Nat using (z≤n; s≤s)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read; write)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.Operations where

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- `operations.tpe`, `foo`

ops-foo : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
ops-foo = perform read ⋆
            (perform write (const reading 42)
              (perform read ⋆ (return ⦉ v Hd , v Hd ⦊)))

ex-ops-foo : Verdict ops-foo
ex-ops-foo = ok (Base reading |×| Base reading) (econst [ 4 , ↑ 5 , s≤s (s≤s (s≤s (s≤s z≤n))) ]) refl ≤!
