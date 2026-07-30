------------------------------------------------------------------------
-- Two adjacent prefix substitutions commute.                         --
--                                                                    --
-- Replacing the outer entry (its value weakened past the inner one)   --
-- and then the inner one agrees with replacing the inner entry, the   --
-- outer one riding in the suffix, and then the outer one.             --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

module Syntax.Substitutions.Swap (Spec : LanguageSpec) where

-- Substituting at the prefix boundary, and the former laws.

open import Syntax.Substitutions.Swap.Base      Spec public

-- The swap on a variable, and on the resource variable an `unbox` names.

open import Syntax.Substitutions.Swap.Variables Spec public

-- The clause cases, and the swap theorem.

open import Syntax.Substitutions.Swap.Clauses   Spec public
