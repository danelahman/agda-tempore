-----------------------
-- Context renamings --
-----------------------

open import Language.Spec

module MonomorphicCalculus.Syntax.Renaming (S : LanguageSpec) where

-- The generating calculus: eternal contexts, the `Ren` datatype, and the
-- renamings derived from it.

open import MonomorphicCalculus.Syntax.Renaming.Base  S public
