------------------------------------------------------------------------
-- States up to the term equivalence.                                 --
--                                                                    --
-- Reduction is a bisimulation for `_≐ˢ_`: related states run to       --
-- related states. The four parts below are the relation itself, the   --
-- shape of state extensions, the bisimulation rule by rule, and       --
-- replaying an extension across the equivalence.                      --
------------------------------------------------------------------------

open import Language.Spec

module MonomorphicCalculus.OperationalSemantics.StateEquivalence (Spec : LanguageSpec) where

open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Core         Spec public
open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Extensions   Spec public
open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Bisimulation Spec public
open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Replay       Spec public
