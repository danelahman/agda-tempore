------------------------------------------------------------------------
-- The trace grade of upper bounds over the time-strict allowance      --
-- order.                                                              --
--                                                                     --
-- `Worked.Traces.Allowance` is about what a bound says; this module is --
-- about *where* it says it. A bound's delays are budget, and the       --
-- time-strict order makes that budget local: the work a run does       --
-- between two operations the bound names is paid for only out of what  --
-- the bound offers between the same two.                              --
--                                                                     --
-- So a bound can prescribe when its spare time is available. Two       --
-- bounds differing only in where six ticks sit, and two runs           --
-- differing only in where the store falls -- all four traces performing --
-- a read, a store and a transmission, all taking ten ticks under       --
-- `cost` -- give the table this module checks:                        --
--                                                                     --
--                            ⌈read⌉∙⟨6⟩∙⌈send⌉   ⌈read⌉∙⌈send⌉∙⟨3⟩    --
--   ⌈read⌉∙⌈write⌉∙⌈send⌉    both columns        neither              --
--   ⌈read⌉∙⌈send⌉∙⌈write⌉    leniently only      both columns         --
--                                                                     --
-- The interesting cell is the third: a run that stores after           --
-- transmitting is within a bound that budgets six ticks *before* the   --
-- transmission if budget may travel, and is not if it may not. No      --
-- measure of elapsed time separates these runs, and neither does the   --
-- lenient order; only where the time falls does.                      --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.AllowanceTimed where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Example.Traces.AllowanceTimed.RightSided
  Op _≟ₒ_ cost cost-pos
  using () renaming (_≾_ to _≾ᵗ_; _≾?_ to _≾ᵗ?_)
open import Syntax.Grades.Example.Traces.Allowance.RightSided
  Op _≟ₒ_ cost cost-pos
  using () renaming (_≾_ to _≾_; _≾?_ to _≾?_)

holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
holds {p = p} = toWitness p

fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
fails {p = p} = toWitnessFalse p

holdsᵗ : {P Q : NeTraces} {p : True (P ≾ᵗ? Q)} → P ≾ᵗ Q
holdsᵗ {p = p} = toWitness p

failsᵗ : {P Q : NeTraces} {p : False (P ≾ᵗ? Q)} → ¬ (P ≾ᵗ Q)
failsᵗ {p = p} = toWitnessFalse p

------------------------------------------------------------------------
-- Budget before the transmission
--
-- The bound names a read and a transmission and offers six ticks
-- between them. A run that stores in that window is within it under
-- either order; one that stores afterwards is within it only if the
-- budget may travel past the transmission.

storing-in-the-window :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
storing-in-the-window = holdsᵗ

storing-afterwards :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
storing-afterwards = holds

storing-afterwards-not-timed :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆)
storing-afterwards-not-timed = failsᵗ

------------------------------------------------------------------------
-- Budget after the transmission
--
-- Moving the three ticks the store needs to the far side of the
-- transmission exchanges which run is permitted, in either column.

storing-afterwards-fits :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
storing-afterwards-fits = holdsᵗ

storing-in-the-window-does-not :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
     ≾ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆)
storing-in-the-window-does-not = fails

------------------------------------------------------------------------
-- As an effect grade: a coercion the axis costs
--
-- The exact grade of the run that stores after transmitting weakens to
-- the budget-before bound leniently, and not time-strictly: `coerce`
-- has one fewer move available in this column.

weakening-to-the-window :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
weakening-to-the-window = holds

weakening-to-the-window-not-timed :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆)
weakening-to-the-window-not-timed = failsᵗ

-- what does travel is the weakening to a bound offering its budget
-- where the run spends it

weakening-to-the-right-window :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
weakening-to-the-right-window = holdsᵗ

-- and every time-strict coercion is a lenient one: this column is the
-- finer of the two, never the other way round

timed-implies-lenient :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
timed-implies-lenient = holds

------------------------------------------------------------------------
-- As a resource grade: a permit that says when its slack is available
--
-- `unbox`'s premise `ρ' ≾ᵣ ρ` asks what elapsed to be within what the
-- box allows. Here the box allows six ticks of housekeeping before the
-- transmission, and a computation that does its housekeeping after it
-- opens the box in one column and not the other -- both runs taking
-- ten ticks, so nothing about elapsed time decides it.

housekeeping-in-the-window-opens-it :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
housekeeping-in-the-window-opens-it = holdsᵗ

housekeeping-afterwards-opens-it-leniently :
  ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
housekeeping-afterwards-opens-it-leniently = holds

housekeeping-afterwards-does-not-timed :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆)
housekeeping-afterwards-does-not-timed = failsᵗ

-- the condition is universal in what elapsed, so a computation that may
-- do either keeps the box open only if both of its runs stay within it

either-way-not-timed :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆)
either-way-not-timed = failsᵗ

either-way-leniently :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆
either-way-leniently = holds

------------------------------------------------------------------------
-- Alternatives at both ends
--
-- What the box has to do instead is offer both windows, and then each
-- run stays within the one that budgets where it spends -- with every
-- endpoint listing alternatives, and time-strictly.

both-windows :
  ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
  ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆
both-windows = holdsᵗ

-- and neither bound would do on its own

neither-alone-before :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⟨ 6 ⟩ ∙ ⌈ send ⌉ ⟆)
neither-alone-before = failsᵗ

neither-alone-after :
  ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ∣ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
     ≾ᵗ ⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⟨ 3 ⟩ ⟆)
neither-alone-after = failsᵗ
