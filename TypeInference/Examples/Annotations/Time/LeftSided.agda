------------------------------------------------------------------
-- Annotated programs at left-sided intervals                    --
--                                                                --
-- Every scheme is the one written in `Annotations`.            --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)
open import Data.Unit using (tt)

open import Relation.Nullary.Decidable using (True; False)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-LeftSided)

module TypeInference.Examples.Annotations.Time.LeftSided where

open Time-LeftSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Examples.Annotations spec enum
open import TypeInference.Raw.SufficientlyAnnotated spec
  using (sufficientlyAnnotated?)

id-bool-reported : report (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : report (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : report (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl

-- Sufficient annotation, decided

twice-insufficient : False (sufficientlyAnnotated? enum twice)
twice-insufficient = tt

twiceᵃ-sufficient : True (sufficientlyAnnotated? enum twiceᵃ)
twiceᵃ-sufficient = tt
