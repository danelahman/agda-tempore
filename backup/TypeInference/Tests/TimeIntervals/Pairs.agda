--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: pairs without a handler.               --
--------------------------------------------------------------------------------

open import Data.Nat using (z≤n; s≤s)
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
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Pairs where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades spec
open import TypeInference.OpenSyntax.Types  spec

open M

ex-p-λ : Outcome p-λ
ex-p-λ = ok (scope 4 0 4 , Base reading ‼ econst (of-natᵉ 1) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-p-I : Outcome p-I
ex-p-I = ok (scope 0 0 2 , Unit ‼ econst [ 0 , ↑ 1 , z≤n ] ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-p-S : Outcome p-S
ex-p-S = ok (scope 1 0 5 , Unit ‼ econst (of-natᵉ 2) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-p-D : Outcome p-D
ex-p-D = ok (scope 0 0 3 , Unit ‼ econst (of-natᵉ 2) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-p-B : Outcome p-B
ex-p-B = ok (scope 2 2 2 , ([ rvar (# 0) ] Base reading) ‼ econst (of-natᵉ 1) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-p-U : Outcome p-U
ex-p-U = ok (scope 2 1 2 , Unit ‼ econst (of-natᵉ 1) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-λ-I : Outcome λ-I
ex-λ-I = ok (scope 4 0 4 , (Bool ⇒ (Unit ‼ econst [ 0 , ↑ 1 , z≤n ])) ‼ ûₑ ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-λ-S : Outcome λ-S
ex-λ-S = ok (scope 6 0 7 , Unit ‼ econst (of-natᵉ 1) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-λ-D : Outcome λ-D
ex-λ-D = ok (scope 4 0 4 , Bool ‼ econst (of-natᵉ 1) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-s-I : Outcome s-I
ex-s-I = ok (scope 0 0 5 , Unit ‼ econst [ 1 , ↑ 2 , s≤s z≤n ] ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-s-D : Outcome s-D
ex-s-D = ok (scope 1 0 5 , Bool ‼ econst (of-natᵉ 3) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-i-D : Outcome i-D
ex-i-D = ok (scope 0 0 3 , Unit ‼ econst [ 1 , ↑ 2 , s≤s z≤n ] ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-b-λ : Outcome b-λ
ex-b-λ = ok (scope 8 3 3 ,
             (tvar (# 4) ⇒ (([ rvar (# 1) ] tvar (# 4)) ‼ ûₑ)) ‼ ûₑ ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-b-g : Outcome b-g
ex-b-g = ok (scope 1 2 1 , ([ rvar (# 0) ] Unit) ‼ ûₑ ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-u-λ : Outcome u-λ
ex-u-λ = ok (scope 7 3 3 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-b-I : Outcome b-I
ex-b-I = ok (scope 1 3 1 , ([ rvar (# 1) ] Unit) ‼ ûₑ ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-u-I : Outcome u-I
ex-u-I = ok (scope 2 1 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-b-S : Outcome b-S
ex-b-S = ok (scope 3 2 3 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-b-D : Outcome b-D
ex-b-D = ok (scope 1 2 2 , ([ rvar (# 0) ] Unit) ‼ econst (of-natᵉ 1) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-u-D : Outcome u-D
ex-u-D = ok (scope 2 1 2 , Unit ‼ econst (of-natᵉ 1) ,
             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-b-U : Outcome b-U
ex-b-U = ok (scope 2 1 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
