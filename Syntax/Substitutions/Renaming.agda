------------------------------------------------------------------------
-- Renaming commutes with substitution.                               --
--                                                                    --
-- Renaming a prefix and substituting at the variable just past it are --
-- independent, so they may be done in either order — the value        --
-- substituted picking up the renaming when it goes second.            --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

module Syntax.Substitutions.Renaming (Spec : LanguageSpec) where

-- Renaming against substitution on variables and cells.

open import Syntax.Substitutions.Renaming.Variables Spec public

-- Restriction, conjugated decompositions, and the clause renamings.

open import Syntax.Substitutions.Renaming.Clauses   Spec public

-- The commutation theorem itself.

open import Syntax.Substitutions.Renaming.Core      Spec public
