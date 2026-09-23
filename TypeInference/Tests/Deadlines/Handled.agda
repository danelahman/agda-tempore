--------------------------------------------------------------------------------
-- Tests at deadlines: pairs with a handler.                                  --
--                                                                            --
-- Each clause family handling each construct, a forwarding clause opening a  --
-- box, and a family chosen per operation.                                    --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Fin using (#_)
open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ)

open import TypeInference.Tests.Deadlines.Setup

module TypeInference.Tests.Deadlines.Handled where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades specᵈ
open import TypeInference.OpenSyntax.Types  specᵈ

open M

module Hf = Handling forward
module Hr = Handling resume
module Hr₁ = Handling resume₁
module Hd = Handling drop

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
               ((Unit ⇒ tvar (# 11) ‼ evar (# 10)) ⇒ Unit ‼ evar (# 10)) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-I : Outcome h-I
  ex-h-I = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
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

module Resuming where

  open Hr

  ex-h-P : Outcome h-P
  ex-h-P = ok (scope 10 0 10 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-S : Outcome h-S
  ex-h-S = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 2) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-λ : Outcome h-λ
  ex-h-λ = ok (scope 20 0 14 ,
               ((Unit ⇒ tvar (# 11) ‼ evar (# 7)) ⇒ Unit ‼ evar (# 7)) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-I : Outcome h-I
  ex-h-I = ok (scope 10 0 10 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-D : Outcome h-D
  ex-h-D = ok (scope 10 0 10 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-B : Outcome h-B
  ex-h-B = ok (scope 12 1 10 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-U : Outcome h-U
  ex-h-U = ok (scope 12 1 10 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module ResumingAfter where

  open Hr₁

  ex-h-P : Outcome h-P
  ex-h-P = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-S : Outcome h-S
  ex-h-S = ok (scope 10 0 16 , Unit ‼ econst (of-natᵉ 2) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-λ : Outcome h-λ
  ex-h-λ = ok (scope 20 0 17 ,
               ((Unit ⇒ tvar (# 11) ‼ evar (# 10)) ⇒ Unit ‼ evar (# 10)) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-I : Outcome h-I
  ex-h-I = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
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

module Discarding where

  open Hd

  ex-h-P : Outcome h-P
  ex-h-P = ok (scope 1 0 4 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-S : Outcome h-S
  ex-h-S = ok (scope 1 0 7 , Unit ‼ econst (of-natᵉ 2) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-λ : Outcome h-λ
  ex-h-λ = ok (scope 11 0 8 ,
               ((Unit ⇒ tvar (# 2) ‼ evar (# 1)) ⇒ Unit ‼ evar (# 1)) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-I : Outcome h-I
  ex-h-I = ok (scope 1 0 4 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-D : Outcome h-D
  ex-h-D = ok (scope 1 0 4 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-B : Outcome h-B
  ex-h-B = ok (scope 3 1 4 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

  ex-h-U : Outcome h-U
  ex-h-U = ok (scope 3 1 4 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ex-fwd-U : Outcome fwd-U
ex-fwd-U = ok (scope 13 1 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

module Chosen where

  open M.Handling (choose forward drop)

  ex-h-P : Outcome h-P
  ex-h-P = ok (scope 10 0 13 , Unit ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
