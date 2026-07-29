------------------------------------------------------------------------
-- Closing environments over a state.                                 --
--                                                                    --
-- `Syntax.Substitutions` provides single-variable substitution whose --
-- replacement is *prefix-typed*: typed in the context left of the    --
-- variable it replaces, which the substitution removes. A closing    --
-- environment is therefore not a `Sub` but a description of how a    --
-- context is built from a state, realised by iterated single         --
-- substitutions.                                                     --
--                                                                    --
-- The zones a context of the fundamental lemma has:                  --
--                                                                    --
--   * `⌊ St ⌋`  — the state: locks and cells, closed by the store;   --
--   * `_∷ᵉ_`/`_⟨_⟩ᵉ` — the binder telescope: each variable           --
--                 instantiated by a value, each lock matched by a    --
--                 slice into a state far enough ahead;               --
--   * `eternalˡ` — an eternal prefix: handler clauses close over     --
--                 `Γ ᴱ` and fire at `Γ' := toCtx St` (`HANDLE-OP`);  --
--                 `toCtx St ᴱ ≡ []`, so eternal values are closed.   --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

module OperationalSemantics.Adequacy.Environment (Spec : LanguageSpec) where

-- Lock-free contexts, `Env`, and its reducibility predicates.

open import OperationalSemantics.Adequacy.Environment.Core      Spec public

-- The action on terms, and its commutation with every former.

open import OperationalSemantics.Adequacy.Environment.Action    Spec public

-- The action on a variable, and its respect for the term equivalence.

open import OperationalSemantics.Adequacy.Environment.Variables Spec public

-- The clause action against the clause environment.

open import OperationalSemantics.Adequacy.Environment.Clauses   Spec public

-- The action on the cell an `unbox` names.

open import OperationalSemantics.Adequacy.Environment.Cell      Spec public
