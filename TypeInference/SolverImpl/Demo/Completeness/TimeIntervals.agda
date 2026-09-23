--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows.                          --
--                                                                            --
-- Inference checked against open derivations of pairs of constructs, and     --
-- of `tempore-lang`'s example programs, at `Worked.Spec`: two-sided          --
-- windows as effect grades, lower bounds as resource grades.                 --
--                                                                            --
--       P      Hf     Hr     Hd     B      U      λ      I      S      D     --
--   P   ok     ok     ok     —      ok     ok     ok     ok     ok     ok    --
--   Hf         ok     ok     —      ok     ok     ok     ok     ok     ok    --
--   Hr                ok     —      ok     ok     ok     ok     ok     ok    --
--   Hd                       —      —      —      —      —      —      —     --
--   B                               ok     ok     ok     ok     ok     ok    --
--   U                                      ·      ok     ok     ok     ok    --
--   λ                                             ·      ok     ok     ok    --
--   I                                                    ·      ok     ok    --
--   S                                                           ·      ok    --
--   D                                                                  ·     --
--                                                                            --
-- P perform; Hf, Hr, Hd handle with a forwarding, resuming or discarding     --
-- clause family; B box; U unbox; λ lam and application; I if; S              --
-- sequencing; D delay. `ok` inferred, at least as good as declared;          --
-- `ref` refused; `worse` inferred, worse than declared; `—` not              --
-- derivable; `·` no entry.                                                   --
--                                                                            --
-- This module is an index.                                                   --
--------------------------------------------------------------------------------

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals where

-- `Generic` at these windows, and the clause families

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

-- Pairs without a handler

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Pairs

-- Pairs with a handler

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Handled

-- Hr × S across the resumption

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Kept

-- A handler returning a box, or the handled answer

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Boxed

-- Hf, Hr × Hf, Hr: a handler inside another

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Nested

-- A handler inside a clause

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.InClause

-- The prototype's `time-lower-bound` and `time-interval` programs

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs
