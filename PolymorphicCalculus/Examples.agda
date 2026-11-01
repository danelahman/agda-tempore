------------------------------------------------------------------------
-- The type-inference examples                                        --
--                                                                    --
-- Programs run through type inference at concrete grades, and solver --
-- stages run on hand-written constraints, in sets by what they test. --
-- Each answer is checked by `refl`: a scheme against the one         --
-- expected, a refusal against `untypable`.                           --
--                                                                    --
-- The examples run the solver and take minutes in total to check, so --
-- the top-level `Everything.agda` file checks them and               --
-- `PolymorphicCalculus/Everything.agda` does not.                    --
--                                                                    --
-- Check them alone with `agda PolymorphicCalculus/Examples.agda`, or --
-- one set with `agda PolymorphicCalculus/Examples/<Set>/All.agda`,   --
-- whose header comment names the solver parts it exercises.          --
------------------------------------------------------------------------

module PolymorphicCalculus.Examples where

-- What a scheme is, and notation for writing one

import PolymorphicCalculus.Examples.Scheme
import PolymorphicCalculus.Examples.Variables

-- The languages the examples run in

import PolymorphicCalculus.Examples.Specs

-- Tempore's standard library

import PolymorphicCalculus.Examples.Stdlib.All

-- Annotations

import PolymorphicCalculus.Examples.Annotations.All

-- Handlers

import PolymorphicCalculus.Examples.Handlers.All

-- Boxes

import PolymorphicCalculus.Examples.Boxes.All

-- A grade of two components

import PolymorphicCalculus.Examples.Product.All

-- Report simplification

import PolymorphicCalculus.Examples.Reports.All

-- Durations other than ticks

import PolymorphicCalculus.Examples.Durations.All

-- Solver stages on hand-written constraints

import PolymorphicCalculus.Examples.Stages.All

-- Satisfiability at definitions and establishment at runs

import PolymorphicCalculus.Examples.Runs.All

-- Natural numbers

import PolymorphicCalculus.Examples.Data.All

-- Primitive recursion

import PolymorphicCalculus.Examples.Recursion.All

-- Comparisons

import PolymorphicCalculus.Examples.Compare.All

-- Programs of several definitions

import PolymorphicCalculus.Examples.Programs.All
