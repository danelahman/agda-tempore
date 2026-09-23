--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: pairs with a handler.                  --
--                                                                            --
-- Each clause family handling each construct, a forwarding clause opening a  --
-- box, and a family chosen per operation.                                    --
--------------------------------------------------------------------------------

open import Data.Nat using (z≤n)
open import Data.Unit using (tt)

open import Data.Fin using (#_)
open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Handled where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

-- no discarding clause is derivable: the unit is below no operation's
-- window

module Hf = Handling forward
module Hr = Handling resume

module Forwarding where

  open Hf

  ex-h-P : Outcome h-P
  ex-h-P = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-S : Outcome h-S
  ex-h-S = ok (scope 10 0 16 , Unit ‼ econst (of-natᵉ 2) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-λ : Outcome h-λ
  ex-h-λ = ok (scope 20 0 17 ,
               ((Unit ⇒ (tvar (# 11) ‼ evar (# 10))) ⇒ (Unit ‼ evar (# 10))) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-I : Outcome h-I
  ex-h-I = ok (scope 10 0 13 , Unit ‼ econst [ 0 , ↑ 1 , z≤n ] ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-D : Outcome h-D
  ex-h-D = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-B : Outcome h-B
  ex-h-B = ok (scope 12 1 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-U : Outcome h-U
  ex-h-U = ok (scope 12 1 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-fwd-U : Outcome fwd-U
  ex-fwd-U = ok (scope 13 1 13 , Unit ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module Resuming where

  open Hr

  ex-h-P : Outcome h-P
  ex-h-P = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-S : Outcome h-S
  ex-h-S = ok (scope 10 0 16 , Unit ‼ econst (of-natᵉ 2) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-λ : Outcome h-λ
  ex-h-λ = ok (scope 20 0 17 ,
               ((Unit ⇒ (tvar (# 11) ‼ evar (# 10))) ⇒ (Unit ‼ evar (# 10))) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-I : Outcome h-I
  ex-h-I = ok (scope 10 0 13 , Unit ‼ econst [ 0 , ↑ 1 , z≤n ] ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-D : Outcome h-D
  ex-h-D = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-B : Outcome h-B
  ex-h-B = ok (scope 12 1 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-U : Outcome h-U
  ex-h-U = ok (scope 12 1 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module Chosen where

  open M.Handling (choose forward resume)

  ex-h-P : Outcome h-P
  ex-h-P = ok (scope 19 0 22 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
