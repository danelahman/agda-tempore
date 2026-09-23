--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: `operations.tpe`.                      --
--------------------------------------------------------------------------------

open import Data.Nat using (z≤n; s≤s)
open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read; write)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Programs.Operations where

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

ex-ops-foo : Outcome ops-foo
ex-ops-foo = ok (scope 2 0 4 ,
                 (Base reading |×| Base reading) ‼ econst [ 4 , ↑ 5 , s≤s (s≤s (s≤s (s≤s z≤n))) ] ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
