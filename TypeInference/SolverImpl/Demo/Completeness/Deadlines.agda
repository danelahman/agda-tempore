--------------------------------------------------------------------------------
-- Completeness checks at deadlines.                                          --
--                                                                            --
-- Inference checked against open derivations of pairs of constructs, and     --
-- of `tempore-lang`'s example programs, at `Demo.TimeIntervals`'             --
-- deadlines: right-sided intervals as both grades, both units least.         --
--                                                                            --
--       P      Hf     Hr     Hd     B      U      λ      I      S      D     --
--   P   ok     ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hf         ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hr                ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hd                       ok     ok     ok     ok     ok     ok     ok    --
--   B                               worse  ok     ok     ok     ok     ok    --
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
-- B × B is `b-g`, a box whose grade nothing bounds.                          --
--                                                                            --
-- This module is an index.                                                   --
--------------------------------------------------------------------------------

module TypeInference.SolverImpl.Demo.Completeness.Deadlines where

-- `Generic` at these deadlines, and the clause families

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

-- Pairs without a handler

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Pairs

-- Pairs with a handler

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Handled

-- Hr × S across the resumption

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Kept

-- A handler returning a box, or the handled answer

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Boxed

-- Hf, Hr, Hd × Hf, Hr, Hd: a handler inside another

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Nested

-- The prototype's `time-upper-bound` programs

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs

-- The refusals of `Kept` and `et-h`, as a constraint

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Constraints
