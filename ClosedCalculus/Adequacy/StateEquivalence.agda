------------------------------------------------------------------------
-- States up to the term equivalence.                                 --
--                                                                    --
-- Reduction is a bisimulation for `_≐ˢ_`: related states run to       --
-- related states. The four parts below are the relation itself, the   --
-- shape of state extensions, the bisimulation rule by rule, and       --
-- replaying an extension across the equivalence.                      --
------------------------------------------------------------------------

open import Language.Spec

module ClosedCalculus.Adequacy.StateEquivalence (Spec : LanguageSpec) where

open import ClosedCalculus.Adequacy.StateEquivalence.Core         Spec public
open import ClosedCalculus.Adequacy.StateEquivalence.Extensions   Spec public
open import ClosedCalculus.Adequacy.StateEquivalence.Bisimulation Spec public
open import ClosedCalculus.Adequacy.StateEquivalence.Replay       Spec public
