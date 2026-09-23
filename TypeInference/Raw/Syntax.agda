------------------------------------------------------------------
-- Raw (well-scoped, untyped) syntax of the language              --
--                                                                --
-- The terms that inference takes as input: one former per former --
-- of `TypeInference.OpenSyntax.Language`, minus `coerce`, with   --
-- the mirrored judgement's data dropped except the annotations   --
-- below. `RawV Θ n` and `RawC Θ n` are scoped by the grade and   --
-- type variables `Θ` of the context and by `n` term variables,   --
-- de Bruijn indices into the full context.                       --
--                                                                --
-- The annotations are the base type of a constant, the operation --
-- of a `perform`, the duration of a `delay`, the variable of an  --
-- `unbox` and the grade of a `box`, an expression over `Θ`. A    --
-- handler's clauses are scoped over `Θ +e`, binding the clause's --
-- continuation grade, and over the full context, `2 + n`.        --
------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

module TypeInference.Raw.Syntax (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- Only the base-type signature is needed; the type formers of the closed
-- language play no role in raw terms.

open import Syntax.Types S using (BaseType; BaseConstants)

open import TypeInference.Scopes
open import TypeInference.OpenSyntax.Grades S using (RExp)

mutual

  data RawV (Θ : Scope) (n : ℕ) : Set where

    -- variables

    var     : Fin n
              -------
            → RawV Θ n

    -- base-typed constants

    const   : (B : BaseType)
            → BaseConstants B
            -----------------
            → RawV Θ n

    -- unit type

    ⋆       :
              -------
              RawV Θ n

    -- booleans

    true    :
              -------
              RawV Θ n

    false   :
              -------
              RawV Θ n

    -- pairing

    ⦉_,_⦊    : RawV Θ n
            → RawV Θ n
            ---------
            → RawV Θ n

    -- lambda abstraction

    lam     : RawC Θ (suc n)
              ------------
            → RawV Θ n


  data RawC (Θ : Scope) (n : ℕ) : Set where

    -- returning a value

    return  : RawV Θ n
              -------
            → RawC Θ n

    -- sequential composition

    _⨟_     : RawC Θ n              -- NOTE: use \;2 to get this unicode semicolon
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- function application

    _·_     : RawV Θ n
            → RawV Θ n
            ---------
            → RawC Θ n

    -- pattern-matching

    match_`in_ : RawV Θ n
               → RawC Θ (suc (suc n))
               --------------------
               → RawC Θ n

    -- empty type elimination

    absurd  : RawV Θ n
              -------
            → RawC Θ n

    -- boolean elimination

    if_`then_`else_
            : RawV Θ n
            → RawC Θ n
            → RawC Θ n
            ---------
            → RawC Θ n

    -- performing algebraic operations

    perform : (op : Op)
            → RawV Θ n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- explicit delaying of a computation

    delay   : ℕ
            → RawC Θ n
            ---------
            → RawC Θ n

    -- effect handling

    -- The clause family is indexed by the operation symbol, matching the
    -- mirrored rule; each clause is scoped over `Θ +e`, whose new variable
    -- is the continuation grade, and over the ambient context extended by
    -- the operation's parameter and the boxed continuation.

    handle_`with_`in
            : RawC Θ n
            → (Op → RawC (Θ +e) (suc (suc n)))
            → RawC Θ (suc n)
            ---------------------------
            → RawC Θ n

    -- unboxing a boxed variable

    unbox   : Fin n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- boxing up a value

    -- The grade says when the boxed value becomes usable.

    box     : RExp Θ
            → RawV Θ n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n
