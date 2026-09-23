--------------------------------------------------------------------------------
-- Tests at timed traces: a handler inside another, for each                  --
-- pair of forwarding, resuming and discarding families.                      --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)

open import TypeInference.SolverImpl.Demo.TimedTraces using (spec)

open import TypeInference.Tests.TimedTraces.Setup

module TypeInference.Tests.TimedTraces.Nested where

open LanguageSpec spec
open Operations Ops using (op-grade)

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

ex-fwd-in-fwd : Outcome (Nesting.nest forward forward)
ex-fwd-in-fwd = ok (scope 20 0 24 , Unit ‼ econst (op-grade read) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-fwd-in-res : Outcome (Nesting.nest forward resume)
ex-fwd-in-res = ok (scope 20 0 21 , Unit ‼ econst (op-grade read) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-fwd-in-drop : Outcome (Nesting.nest forward drop)
ex-fwd-in-drop = ok (scope 11 0 15 , Unit ‼ econst (op-grade read) ,
                     []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-res-in-fwd : Outcome (Nesting.nest resume forward)
ex-res-in-fwd = ok (scope 20 0 21 , Unit ‼ econst (op-grade read) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-res-in-res : Outcome (Nesting.nest resume resume)
ex-res-in-res = ok (scope 20 0 18 , Unit ‼ econst (op-grade read) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-res-in-drop : Outcome (Nesting.nest resume drop)
ex-res-in-drop = ok (scope 11 0 12 , Unit ‼ econst (op-grade read) ,
                     []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-drop-in-fwd : Outcome (Nesting.nest drop forward)
ex-drop-in-fwd = ok (scope 11 0 15 , Unit ‼ econst (op-grade read) ,
                     []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-drop-in-res : Outcome (Nesting.nest drop resume)
ex-drop-in-res = ok (scope 11 0 12 , Unit ‼ econst (op-grade read) ,
                     []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-drop-in-drop : Outcome (Nesting.nest drop drop)
ex-drop-in-drop = ok (scope 2 0 6 , Unit ‼ econst (op-grade read) ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
