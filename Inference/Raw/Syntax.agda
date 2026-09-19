------------------------------------------------------------------
-- Raw (well-scoped, untyped) syntax of the language              --
--                                                                --
-- The terms that inference takes as input: one former per former --
-- of `Inference.Open.Language`, minus `coerce` (invisible), and  --
-- with the type, grade and entailment data of the mirrored       --
-- judgement dropped. Variables are de Bruijn indices into the    --
-- full context, `Fin n`.                                         --
--                                                                --
-- The only annotations left are the ones inference cannot guess: --
-- the base type of a constant, the operation of a `perform`, the --
-- duration of a `delay`, and the variable of an `unbox`. In      --
-- particular `box` carries no grade (inference binds it          --
-- existentially), and handlers carry no capture annotation:      --
-- their clauses are scoped over the FULL context, `RawC (2 + n)`,--
-- the clause barrier being an ordinary lock.                     --
------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

module Inference.Raw.Syntax (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- Only the base-type signature is needed; the type formers of the closed
-- language play no role in raw terms.

open import Syntax.Types S using (BaseType; BaseConstants)

--------------------------------------------------------------
-- Raw terms (values and computations)                       --
--------------------------------------------------------------

mutual

  data RawV (n : ℕ) : Set where

    -- variables

    var     : Fin n
              -------
            → RawV n

    -- base-typed constants

    const   : (B : BaseType)
            → BaseConstants B
            -----------------
            → RawV n

    -- unit type

    ⋆       :
              -------
              RawV n

    -- booleans

    true    :
              -------
              RawV n

    false   :
              -------
              RawV n

    -- pairing

    ⦉_,_⦊    : RawV n
            → RawV n
            ---------
            → RawV n

    -- lambda abstraction

    lam     : RawC (suc n)
              ------------
            → RawV n


  data RawC (n : ℕ) : Set where

    -- returning a value

    return  : RawV n
              -------
            → RawC n

    -- sequential composition

    _⨟_     : RawC n              -- NOTE: use \;2 to get this unicode semicolon
            → RawC (suc n)
            --------------
            → RawC n

    -- function application

    _·_     : RawV n
            → RawV n
            ---------
            → RawC n

    -- pattern-matching

    match_`in_ : RawV n
               → RawC (suc (suc n))
               --------------------
               → RawC n

    -- empty type elimination

    absurd  : RawV n
              -------
            → RawC n

    -- boolean elimination

    if_`then_`else_
            : RawV n
            → RawC n
            → RawC n
            ---------
            → RawC n

    -- performing algebraic operations

    perform : (op : Op)
            → RawV n
            → RawC (suc n)
            --------------
            → RawC n

    -- explicit delaying of a computation

    delay   : ℕ
            → RawC n
            ---------
            → RawC n

    -- effect handling

    -- The clause family is indexed by the operation symbol, matching the
    -- mirrored rule; each clause is scoped over the ambient context extended
    -- by the operation's parameter and the boxed continuation.

    handle_`with_`in
            : RawC n
            → (Op → RawC (suc (suc n)))
            → RawC (suc n)
            ---------------------------
            → RawC n

    -- unboxing a boxed variable

    unbox   : Fin n
            → RawC (suc n)
            --------------
            → RawC n

    -- boxing up a value

    -- The grade of the box is *not* annotated: it is only lower-bounded by the
    -- typing rule, so inference binds it existentially.

    box     : RawV n
            → RawC (suc n)
            --------------
            → RawC n
