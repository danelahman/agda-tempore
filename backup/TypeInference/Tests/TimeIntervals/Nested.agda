--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: a handler inside                       --
-- another, for each pair of forwarding and resuming families.                --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Nested where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

module FF = Nesting forward forward
module FR = Nesting forward resume
module RF = Nesting resume forward
module RR = Nesting resume resume

ex-fwd-in-fwd : Outcome FF.nest
ex-fwd-in-fwd = ok (scope 20 0 24 , Unit ‼ econst (of-natᵉ 1) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-fwd-in-res : Outcome FR.nest
ex-fwd-in-res = ok (scope 20 0 24 , Unit ‼ econst (of-natᵉ 1) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-res-in-fwd : Outcome RF.nest
ex-res-in-fwd = ok (scope 20 0 24 , Unit ‼ econst (of-natᵉ 1) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-res-in-res : Outcome RR.nest
ex-res-in-res = ok (scope 20 0 24 , Unit ‼ econst (of-natᵉ 1) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
