------------------------------------------------------------------------
-- States up to the term equivalence.                                 --
--                                                                    --
-- Reduction is a bisimulation for `_≐ˢ_`: related states run to       --
-- related states. The four parts below are the relation itself, the   --
-- shape of state extensions, the bisimulation rule by rule, and       --
-- replaying an extension across the equivalence.                      --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

module OperationalSemantics.Adequacy.StateEquivalence (Spec : LanguageSpec) where

open import OperationalSemantics.Adequacy.StateEquivalence.Core         Spec public
open import OperationalSemantics.Adequacy.StateEquivalence.Extensions   Spec public
open import OperationalSemantics.Adequacy.StateEquivalence.Bisimulation Spec public
open import OperationalSemantics.Adequacy.StateEquivalence.Replay       Spec public
