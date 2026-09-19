-----------------------
-- Context renamings --
-----------------------

open import Syntax.LanguageSpec

module Syntax.Renamings (S : LanguageSpec) where

-- The generating calculus: eternal contexts, the `Ren` datatype, and the
-- renamings derived from it.

open import Syntax.Renamings.Base S public
