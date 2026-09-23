--------------------------------------------------------------------------------
-- Tests at deadlines.                                                        --
--                                                                            --
-- Inference checked against open derivations of pairs of constructs, and     --
-- of `tempore-lang`'s example programs, at `Demo.TimeIntervals`' deadlines:  --
-- right-sided intervals as both grades, both units least. Every test is      --
-- reported by inference; none is refused.                                    --
--                                                                            --
-- Pairs without a handler, in `Pairs`:                                       --
--                                                                            --
--   Perform an operation, with                                               --
--     another operation        ex-p-S  two operations in sequence            --
--     function and application ex-p-λ  a function that performs, applied     --
--     conditional              ex-p-I  one arm performs, the other returns   --
--     sequencing               ex-p-S  two operations in sequence            --
--     delay                    ex-p-D  idling, then performing               --
--     box a value              ex-p-B  the answer boxed                      --
--     unbox                    ex-p-U  a box opened after the operation      --
--   Box a value, with                                                        --
--     another box              ex-b-g  a box nothing bounds                  --
--     unbox                    ex-b-U  a box opened at once                  --
--     function and application ex-b-λ  a function boxing its argument        --
--     conditional              ex-b-I  both arms box                         --
--     sequencing               ex-b-S  a box returned, bound and opened      --
--     delay                    ex-b-D  boxing after idling                   --
--   Unbox, with                                                              --
--     function and application ex-u-λ  a function unboxing its argument      --
--     conditional              ex-u-I  one arm unboxes                       --
--     sequencing               ex-b-S  a box returned, bound and opened      --
--     delay                    ex-u-D  a box opened after idling for it      --
--   Function and application, with                                           --
--     conditional              ex-λ-I  a function branching on its argument  --
--     sequencing               ex-λ-S  a function bound, then applied        --
--     delay                    ex-λ-D  an argument used after idling         --
--   Conditional, with                                                        --
--     sequencing               ex-s-I  a branch, then an operation           --
--     delay                    ex-i-D  arms idling for different times       --
--   Sequencing, with                                                         --
--     delay                    ex-s-D  a value carried across two delays     --
--                                                                            --
-- Pairs with a handler, in `Handled`: a handler that forwards                --
-- (`Forwarding`), resumes at once (`Resuming`), resumes after a tick         --
-- (`ResumingAfter`) or discards the continuation (`Discarding`), handling    --
--                                                                            --
--     an operation             ex-h-P  the handled part performs             --
--     sequencing               ex-h-S  it performs twice                     --
--     function and application ex-h-λ  a function handling a call            --
--     conditional              ex-h-I  the handled part branches             --
--     delay                    ex-h-D  the handled part idles                --
--     box a value              ex-h-B  a box opened by the continuation      --
--     unbox                    ex-h-U  a box opened by the handled part      --
--                                                                            --
-- and further:                                                               --
--                                                                            --
--     ex-fwd-U                a forwarding clause opens a box                --
--     Chosen.ex-h-P           a branch forwards or discards                  --
--     Kept.ex-h-keep          a value kept across the resumption             --
--     Kept.ex-h-keep-after    the same, resuming after a tick                --
--     Boxed.*.ex-h-box        the continuation returns a box                 --
--     Boxed.*.ex-h-ans        the handled answer is returned                 --
--     Nested.ex-*-in-*        a handler inside another, every pair           --
--                             of kinds                                       --
--                                                                            --
-- Not tested: unbox, function and application, conditional, sequencing       --
-- and delay each paired with itself.                                         --
--                                                                            --
-- This module is an index.                                                   --
--------------------------------------------------------------------------------

module TypeInference.Tests.Deadlines where

-- `Generic` at these deadlines, and the clause families

import TypeInference.Tests.Deadlines.Setup

-- Pairs without a handler

import TypeInference.Tests.Deadlines.Pairs

-- Pairs with a handler

import TypeInference.Tests.Deadlines.Handled

-- A value kept across the resumption

import TypeInference.Tests.Deadlines.Kept

-- A handler returning a box, or the handled answer

import TypeInference.Tests.Deadlines.Boxed

-- A handler inside another

import TypeInference.Tests.Deadlines.Nested

-- The prototype's `time-upper-bound` programs

import TypeInference.Tests.Deadlines.Programs

-- The var-rule disjunction `Kept` and `et-h` leave, as a constraint

import TypeInference.Tests.Deadlines.Constraints
