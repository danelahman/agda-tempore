------------------------------------------------------------------------
-- Typed example computations, one grade at a time.                   --
--                                                                    --
-- The subtree fixes a language over the alphabet of the sensor node  --
-- and types example computations in it, each at a value type and an  --
-- effect grade.                                                      --
--                                                                    --
-- Most instances use an identity grade system, with effect and       --
-- resource grades the same monoid and `∣-∣ᵉ` the identity, so `∣_∣ᵉ` --
-- disappears: the lock a computation places on the context is its    --
-- effect grade, and the premise of `unbox` compares what a           --
-- computation did with the grade of the box. These instances differ  --
-- only in the monoid. The last group uses a genuine grade system,    --
-- whose locks are the time `∣_∣ᵉ` measures of an effect grade.       --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding. Read downwards, they give the context at any      --
-- point, and the locks between the binding of a box and its `unbox`  --
-- are the elapsed grade that the premise compares with the grade of  --
-- the box.                                                           --
--                                                                    --
-- Each instance writes its programs out in full at its own grades,   --
-- every side condition discharged where the rule imposes it by the   --
-- decision procedure of the grade. In place of a program that the    --
-- grade refuses stands a refutation of the bound it requires.        --
-- `Typing/System.agda` contains the calculus over the language       --
-- (`Language.Examples.SensorNode`), the three ways of meeting the    --
-- bound of `var`, and the operation clauses passed to `handle`.      --
--                                                                    --
-- Two rules place the unit on opposite sides of the order, and each  --
-- instance settles both by a proof or a refutation: whether a        --
-- non-eternal variable goes stale, which is the bound `ρ ≾ᵣ 𝟏ᵣ` of   --
-- `var`, and whether a handler clause may discard its continuation.  --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing where

-- The calculus over the language the examples are written in,
-- parameterised by the grade and by what it gives each operation.

import MonomorphicCalculus.Examples.Typing.System
import MonomorphicCalculus.Examples.Typing.Core

------------------------------------------------------------------------
-- Grades that measure time

-- "at least `n` time steps": a box is a resource that becomes
-- available, and nothing goes stale

import MonomorphicCalculus.Examples.Typing.Time.LeftSided

-- "at most `n` time steps": a box is a lease that expires, and a
-- reading goes stale as soon as anything happens

import MonomorphicCalculus.Examples.Typing.Time.RightSided

-- both bounds at once: a box has a window, and a claim can be made too
-- early or too late

import MonomorphicCalculus.Examples.Typing.Time.TwoSided

-- "at most `q` units" of dense time: the operations measured to the
-- half tick, and a lease spent to the half tick

import MonomorphicCalculus.Examples.Typing.Time.Dense.RightSided

------------------------------------------------------------------------
-- Grades that record which runs there were
--
-- The same programs against grades that see which operations ran and
-- where, at the three cost-sensitive orders and at the subset order.

-- sets of traces at the coverage order: a box asks for work to have
-- been done, and time cannot stand in for it

import MonomorphicCalculus.Examples.Typing.Traces.Timed.LeftSided

-- at the allowance order: a box permits particular runs, so a claim can
-- be refused over which operations were performed and where

import MonomorphicCalculus.Examples.Typing.Traces.Timed.RightSided

-- at both: a box asks for work and caps what may have happened since

import MonomorphicCalculus.Examples.Typing.Traces.Timed.TwoSided

-- the subset order as a cap: a box names the runs it covers outright,
-- nothing paying for anything else

import MonomorphicCalculus.Examples.Typing.Traces.Subsets.RightSided

-- a guarantee and a bound over interval letters: a box opened after an
-- undisturbed wait, and refused after operations fill it

import MonomorphicCalculus.Examples.Typing.Traces.Rigid.Regular.TwoSided

-- the same over finite expressions in dense time: a box opened after an
-- undisturbed wait, and refused after an operation fills it

import MonomorphicCalculus.Examples.Typing.Traces.Rigid.Finite.TwoSided

-- the same over expressions with iteration: a box opened after repeated
-- readings and waits, and refused after a transmission

import MonomorphicCalculus.Examples.Typing.Traces.Rigid.Rational.TwoSided

------------------------------------------------------------------------
-- Grades that pair time with something else
--
-- What each operation touches and draws is fixed in
-- `Operations.Footprint`.

-- lower bounds on time with a security level: a box is an embargoed
-- report, refused when claimed too early or after a transmission

import MonomorphicCalculus.Examples.Typing.Product.LeftSidedTimeLevel

-- upper bounds on time with an energy budget: a box is a calibration
-- that drifts with time and with use, idling drawing nothing

import MonomorphicCalculus.Examples.Typing.Product.RightSidedTimeEnergy

------------------------------------------------------------------------
-- Grades that count operations

-- quotas: a rate limit on transmissions, and a box is a licence that
-- idling does not spend

import MonomorphicCalculus.Examples.Typing.Counts.AtMost

-- certain counts: a box is a token earned by work, which idling cannot
-- stand in for

import MonomorphicCalculus.Examples.Typing.Counts.AtLeast
import MonomorphicCalculus.Examples.Typing.Counts.UpperBound
import MonomorphicCalculus.Examples.Typing.SemiDirect.FlowLevels
import MonomorphicCalculus.Examples.Typing.SemiDirect.WindowedSchedules
import MonomorphicCalculus.Examples.Typing.SemiDirect.ResourceLevels
import MonomorphicCalculus.Examples.Typing.SemiDirect.ModeSwitchCosts
import MonomorphicCalculus.Examples.Typing.SemiDirect.ModeTimes

------------------------------------------------------------------------
-- Grade systems that measure effects by time

-- the rigid finite-expression grades as effects, time intervals as
-- resources, their duration hull between: a box opened once enough time
-- has passed, and refused too soon or too late

import MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Finite.RightSided
import MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Finite.LeftSided
import MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Finite.TwoSided

-- the same over the rigid regular-expression grades

import MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Rational.RightSided
import MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Rational.LeftSided
import MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Rational.TwoSided
