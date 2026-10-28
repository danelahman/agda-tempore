-----------------------
-- Context renamings --
-----------------------

open import Language.Spec

module ClosedCalculus.Syntax.Renamings (S : LanguageSpec) where

-- The generating calculus: eternal contexts, the `Ren` datatype, and the
-- renamings derived from it.

open import ClosedCalculus.Syntax.Renamings.Base S public
