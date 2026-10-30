------------------------------------------------------------------------
-- The type-inference examples, in sets by what they test. Each set's
-- index `PolymorphicCalculus.Examples.<Set>.All` names the solver parts
-- it exercises and can be checked alone.
------------------------------------------------------------------------

module PolymorphicCalculus.Examples where

-- What a scheme is, and notation for writing one

import PolymorphicCalculus.Examples.Scheme
import PolymorphicCalculus.Examples.Variables

-- The languages the examples run in

import PolymorphicCalculus.Examples.Specs

-- The standard library: the generic module and its instances

import PolymorphicCalculus.Examples.Stdlib.All

-- Annotations: the generic module and its instances

import PolymorphicCalculus.Examples.Annotations.All

-- Handlers: the generic module and its instances

import PolymorphicCalculus.Examples.Handlers.All

-- Boxes: the generic module and its instances

import PolymorphicCalculus.Examples.Boxes.All

-- A grade of two components: the generic module and its instances

import PolymorphicCalculus.Examples.Product.All

-- Report simplification: the generic module and its instances

import PolymorphicCalculus.Examples.Reports.All

-- Durations other than ticks: the generic module and its instances

import PolymorphicCalculus.Examples.Durations.All

-- Solver stages on hand-written constraints

import PolymorphicCalculus.Examples.Stages.All

-- Satisfiability at definitions and establishment at runs

import PolymorphicCalculus.Examples.Runs.All

-- Natural numbers: the generic module and its instances

import PolymorphicCalculus.Examples.Data.All

-- Primitive recursion: the generic module and its instances

import PolymorphicCalculus.Examples.Recursion.All

-- Comparisons: the generic module and its instances

import PolymorphicCalculus.Examples.Compare.All

-- Programs of several definitions: the generic module and its instances

import PolymorphicCalculus.Examples.Programs.All
