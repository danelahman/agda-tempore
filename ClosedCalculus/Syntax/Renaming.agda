-----------------------
-- Context renamings --
-----------------------

open import Language.Spec

module ClosedCalculus.Syntax.Renaming (S : LanguageSpec) where

-- The generating calculus: eternal contexts, the `Ren` datatype, and the
-- renamings derived from it.

open import ClosedCalculus.Syntax.Renaming.Base  S public
