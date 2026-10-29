------------------------------------------------------------------------
-- The type-inference examples, in sets by what they test. Each set's
-- index `OpenCalculus.Examples.<Set>.All` names the solver parts it
-- exercises and can be checked alone.
------------------------------------------------------------------------

module OpenCalculus.Examples where

-- What a scheme is, and notation for writing one

import OpenCalculus.Examples.Scheme
import OpenCalculus.Examples.Variables

-- The languages the examples run in

import OpenCalculus.Examples.Specs

-- The standard library: the generic module and its instances

import OpenCalculus.Examples.Stdlib.All

-- Annotations: the generic module and its instances

import OpenCalculus.Examples.Annotations.All

-- Handlers: the generic module and its instances

import OpenCalculus.Examples.Handlers.All

-- Boxes: the generic module and its instances

import OpenCalculus.Examples.Boxes.All

-- A grade of two components: the generic module and its instances

import OpenCalculus.Examples.Product.All

-- Report simplification: the generic module and its instances

import OpenCalculus.Examples.Reports.All

-- Durations other than ticks: the generic module and its instances

import OpenCalculus.Examples.Durations.All

-- Solver stages on hand-written constraints

import OpenCalculus.Examples.Stages.All

-- Satisfiability at definitions and establishment at runs

import OpenCalculus.Examples.Runs.All

-- Natural numbers: the generic module and its instances

import OpenCalculus.Examples.Data.All

-- Primitive recursion: the generic module and its instances

import OpenCalculus.Examples.Recursion.All

-- Comparisons: the generic module and its instances

import OpenCalculus.Examples.Compare.All

-- Programs of several definitions: the generic module and its instances

import OpenCalculus.Examples.Programs.All
