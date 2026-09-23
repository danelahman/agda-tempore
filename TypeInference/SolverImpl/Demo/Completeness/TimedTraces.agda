--------------------------------------------------------------------------------
-- Completeness checks at timed traces.                                       --
--                                                                            --
-- Inference checked against open derivations of pairs of constructs at       --
-- `Demo.TimedTraces`' grades: finite sets of timed runs, read as             --
-- allowances, over an identity grade system; both units least.               --
--                                                                            --
--       P      Hf     Hr     Hd     B      U      λ      I      S      D     --
--   P   ok     ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hf         ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hr                ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hd                       ok     ok     ok     ok     ok     ok     ok    --
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

module TypeInference.SolverImpl.Demo.Completeness.TimedTraces where

-- `Generic` at these grades, and the clause families

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Setup

-- Pairs without a handler

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Pairs

-- Pairs with a handler

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Handled

-- Hr × S across the resumption

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Kept

-- A handler returning a box, or the handled answer

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Boxed

-- Hf, Hr, Hd × Hf, Hr, Hd: a handler inside another

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Nested

-- What these grades see: B × P × U under a permit

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces.Permit
