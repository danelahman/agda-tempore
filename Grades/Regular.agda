------------------------------------------------------------------------
-- Regular languages over a finite alphabet, and the grade they form. --
--                                                                    --
-- A language is held as its canonical table: the minimal complete    --
-- DFA, states numbered breadth-first. This module is only an index.  --
------------------------------------------------------------------------

module Grades.Regular where

import Grades.Regular.Automaton     -- automata, tables, exploration
import Grades.Regular.Basics        -- shared lemmas
import Grades.Regular.Canonical     -- Moore refinement, canonical tables
import Grades.Regular.Operations    -- word, Σ*, ∪, ·, * automata
import Grades.Regular.Inclusion     -- counterexample search, _⊆ᵇ_
import Grades.Regular.Explore       -- exploration is correct
import Grades.Regular.Moore         -- refinement is correct
import Grades.Regular.Canonicity    -- canonicity
import Grades.Regular.Constructions -- constructions lawful and correct
import Grades.Regular.Decide        -- inclusion decided
import Grades.Regular.Properties    -- operations correct
import Grades.Regular.Boolean       -- ∩, complement, single letters
import Grades.Regular.Expression    -- extended regular expressions
import Grades.Regular.Plus          -- Kleene's plus of a language
import Grades.Regular.Grade         -- the Grade instance
import Grades.Regular.Literal       -- grade literals
import Grades.Regular.Closure       -- downward closure under a letter order
import Grades.Regular.Closed        -- the sub-grade of closed languages
import Grades.Regular.Determinise   -- automata with silent moves, determinised
import Grades.Regular.Coding        -- expressions over any letters, coded
import Grades.Regular.Meet          -- whether two languages meet
import Grades.Regular.Reach         -- whether a state reaches an accepting one
