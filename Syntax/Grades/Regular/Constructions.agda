------------------------------------------------------------------------
-- The constructions of `Operations` are lawful automata, and each    --
-- recognises the language it is named for.                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

module Syntax.Grades.Regular.Constructions (k : ℕ) where

open import Syntax.Grades.Regular.Constructions.Basic k public
  using ( lawful-table; accepts-table
        ; lawful-word; reduced-word; accepts-word
        ; lawful-everything; reduced-everything; accepts-everything
        ; lawful-product )
open import Syntax.Grades.Regular.Constructions.Concatenation k public
  using (lawful-concatenation; accepts-concatenation)
open import Syntax.Grades.Regular.Constructions.Iteration k public
  using (_∈*_; none; more; lawful-iteration; accepts-iteration)
