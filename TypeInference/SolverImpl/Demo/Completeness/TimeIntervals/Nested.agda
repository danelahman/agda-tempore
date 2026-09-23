--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: a handler inside         --
-- another, for each pair of forwarding and resuming families.                --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Nested where

open LanguageSpec spec
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

module FF = Nesting forward forward
module FR = Nesting forward resume
module RF = Nesting resume forward
module RR = Nesting resume resume

ex-fwd-in-fwd : Verdict FF.nest
ex-fwd-in-fwd = ok Unit (econst (op-grade read)) refl ≤!

ex-fwd-in-res : Verdict FR.nest
ex-fwd-in-res = ok Unit (econst (op-grade read)) refl ≤!

ex-res-in-fwd : Verdict RF.nest
ex-res-in-fwd = ok Unit (econst (op-grade read)) refl ≤!

ex-res-in-res : Verdict RR.nest
ex-res-in-res = ok Unit (econst (op-grade read)) refl ≤!
