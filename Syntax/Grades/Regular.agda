------------------------------------------------------------------------
-- Regular languages over a finite alphabet, and the grade they form. --
--                                                                    --
-- A language is held as its canonical table: the minimal complete    --
-- DFA, states numbered breadth-first. This module is only an index.  --
------------------------------------------------------------------------

module Syntax.Grades.Regular where

import Syntax.Grades.Regular.Automaton     -- automata, tables, exploration
import Syntax.Grades.Regular.Basics        -- shared lemmas
import Syntax.Grades.Regular.Canonical     -- Moore refinement, canonical tables
import Syntax.Grades.Regular.Operations    -- word, Σ*, ∪, ·, * automata
import Syntax.Grades.Regular.Inclusion     -- counterexample search, _⊆ᵇ_
import Syntax.Grades.Regular.Explore       -- exploration is correct
import Syntax.Grades.Regular.Moore         -- refinement is correct
import Syntax.Grades.Regular.Canonicity    -- canonicity
import Syntax.Grades.Regular.Constructions -- constructions lawful and correct
import Syntax.Grades.Regular.Decide        -- inclusion decided
import Syntax.Grades.Regular.Properties    -- operations correct
import Syntax.Grades.Regular.Boolean       -- ∩, complement, single letters
import Syntax.Grades.Regular.Expression    -- extended regular expressions
import Syntax.Grades.Regular.Grade         -- the Grade instance
import Syntax.Grades.Regular.Literal       -- grade literals
import Syntax.Grades.Regular.Plus          -- Kleene's plus
import Syntax.Grades.Regular.Closure       -- downward closure under a letter order
import Syntax.Grades.Regular.Closed        -- the sub-grade of closed languages
