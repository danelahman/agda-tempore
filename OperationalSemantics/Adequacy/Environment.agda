------------------------------------------------------------------------
-- Closing environments over a state.                                 --
--                                                                    --
-- `Syntax.Substitutions` substitutes at a context's prefix boundary: --
-- the replacement is typed in the context left of the variable it    --
-- replaces, which the substitution removes. A closing environment is --
-- therefore not a `Sub` but a description of how a context is built  --
-- from a state, realised by iterated boundary substitutions.         --
--                                                                    --
-- The zones a context of the fundamental lemma has:                  --
--                                                                    --
--   * `⌊ St ⌋`  — the state: locks and cells, closed by the store;   --
--   * `_∷ᵉ_`/`_⟨_⟩ᵉ` — the binder telescope: each variable           --
--                 instantiated by a value, each lock matched by a    --
--                 graded reach into a state far enough ahead.        --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

module OperationalSemantics.Adequacy.Environment (Spec : LanguageSpec) where

-- `Env` and its reducibility predicate.

open import OperationalSemantics.Adequacy.Environment.Core      Spec public

-- The action on terms, and its commutation with every former.

open import OperationalSemantics.Adequacy.Environment.Action    Spec public

-- The action on a variable, and its respect for the term equivalence.

open import OperationalSemantics.Adequacy.Environment.Variables Spec public

-- The action on the cell an `unbox` names.

open import OperationalSemantics.Adequacy.Environment.Cell      Spec public
