-----------------------
-- Context renamings --
-----------------------

open import Syntax.LanguageSpec

module Syntax.Renamings (S : LanguageSpec) where

-- The generating calculus: eternal contexts, the `Ren` datatype, and the
-- renamings derived from it without reference to the eternal restriction.

open import Syntax.Renamings.Base S public

-- The eternal restriction's action on renamings, and the two renamings that
-- relate `Δ ᴱ` to `Δ`.

open import Syntax.Renamings.Eternal S public
