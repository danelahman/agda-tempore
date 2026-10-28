------------------------------------------------------------------
-- Raw (well-scoped, untyped) syntax                            --
--                                                              --
-- The input of inference: one former for each former of        --
-- `OpenCalculus.Typing` except `coerce`, without               --
-- the typing data except the annotations below. `RawV Θ n` and --
-- `RawC Θ n` are scoped by the grade and type variables `Θ` of --
-- the context and by `n` term variables, de Bruijn indices     --
-- into the full context.                                       --
--                                                              --
-- The annotations are the base type of a constant, the         --
-- operation of a `perform`, the duration of a `delay`, the     --
-- variable of an `unbox`, the grade of a `box`, an expression  --
-- over `Θ`, and the optional type annotations of a value and   --
-- of a computation, open types over `Θ`.                       --
-- A handler's clauses are scoped over `Θ +e`, binding the      --
-- clause's continuation grade, and over the full context,      --
-- `2 + n`.                                                     --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import Grades.Base
open import Language.Spec
open import Language.Operations

module OpenCalculus.Syntax.Raw (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- Only the base-type signature is needed; the type formers of the closed
-- language play no role in raw terms.

open import Language.Types S using (BaseType; BaseConstants)

open import OpenCalculus.Syntax.Scopes
open import Language.Comparisons using (Cmp)
open import OpenCalculus.Syntax.Grades S using (RExp)
open import OpenCalculus.Syntax.Types  S using (OVType; OCType)

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

    -- natural numbers

    zero    :
              -------
              RawV Θ n

    succ    : RawV Θ n
              -------
            → RawV Θ n

    -- pairing

    ⦉_,_⦊    : RawV Θ n
            → RawV Θ n
            ---------
            → RawV Θ n

    -- injections into a sum

    inl     : RawV Θ n
              -------
            → RawV Θ n

    inr     : RawV Θ n
              -------
            → RawV Θ n

    -- lists

    nil     :
              --------
              RawV Θ n

    cons    : RawV Θ n
            → RawV Θ n
              -------
            → RawV Θ n

    -- lambda abstraction

    lam     : RawC Θ (suc n)
              ------------
            → RawV Θ n

    -- type annotation

    -- The annotation is an open type over `Θ`: it fixes a shape, and its
    -- type variables stay flexible.

    _⦂ᵛ_    : RawV Θ n
            → OVType Θ
            ---------
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

    -- comparison of two values by one of the relations of `Cmp`

    cmp     : Cmp
            → RawV Θ n
            → RawV Θ n
            ---------
            → RawC Θ n

    -- natural-number elimination, the successor branch binding the
    -- predecessor

    caseℕ_`zero_`succ_
            : RawV Θ n
            → RawC Θ n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- sum elimination, each branch binding the injected value

    case+_`inl_`inr_
            : RawV Θ n
            → RawC Θ (suc n)
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- list elimination, the `cons` branch binding the head and the tail

    caseL_`nil_`cons_
            : RawV Θ n
            → RawC Θ n
            → RawC Θ (suc (suc n))
            --------------------
            → RawC Θ n

    -- primitive recursion on natural numbers, the step binding the
    -- predecessor and the result of the recursive call

    recℕ    : RawV Θ n
            → RawC Θ n
            → RawC Θ (suc (suc n))
            --------------------
            → RawC Θ n

    -- primitive recursion on lists, the step binding the head, the tail
    -- and the result of the recursive call

    recL    : RawV Θ n
            → RawC Θ n
            → RawC Θ (suc (suc (suc n)))
            --------------------------
            → RawC Θ n

    -- performing algebraic operations

    perform : (op : Op)
            → RawV Θ n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- explicit delaying of a computation

    delay   : 𝔻
            → RawC Θ n
            ---------
            → RawC Θ n

    -- effect handling

    -- The clause family is indexed by the operation symbol, matching the
    -- open rule; each clause is scoped over `Θ +e`, whose new variable
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

    -- type annotation

    -- As for values, the annotation fixes a shape.

    _⦂ᶜ_    : RawC Θ n
            → OCType Θ
            ---------
            → RawC Θ n

infix 5 _⦂ᵛ_ _⦂ᶜ_

-- Numerals

numeral : ∀ {Θ n} → ℕ → RawV Θ n
numeral 0       = zero
numeral (suc k) = succ (numeral k)

-- A term with no handler

mutual

  HandlerFreeᵛ : ∀ {Θ n} → RawV Θ n → Set
  HandlerFreeᵛ (succ V)     = HandlerFreeᵛ V
  HandlerFreeᵛ ⦉ V , W ⦊     = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᵛ (inl V)      = HandlerFreeᵛ V
  HandlerFreeᵛ (inr V)      = HandlerFreeᵛ V
  HandlerFreeᵛ (cons V W)   = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᵛ (lam M)      = HandlerFreeᶜ M
  HandlerFreeᵛ (V ⦂ᵛ A)     = HandlerFreeᵛ V
  HandlerFreeᵛ _            = ⊤

  HandlerFreeᶜ : ∀ {Θ n} → RawC Θ n → Set
  HandlerFreeᶜ (return V)               = HandlerFreeᵛ V
  HandlerFreeᶜ (M ⨟ N)                  = HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (V · W)                  = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᶜ (match V `in M)          = HandlerFreeᵛ V × HandlerFreeᶜ M
  HandlerFreeᶜ (absurd V)               = HandlerFreeᵛ V
  HandlerFreeᶜ (if V `then M `else N)   = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (cmp ⋈ V W)               = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᶜ (caseℕ V `zero M `succ N) = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (case+ V `inl M `inr N)   = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (recℕ V M N)              = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (caseL V `nil M `cons N)  = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (recL V M N)              = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (perform op V M)         = HandlerFreeᵛ V × HandlerFreeᶜ M
  HandlerFreeᶜ (delay τ M)              = HandlerFreeᶜ M
  HandlerFreeᶜ (handle M `with H `in N) = ⊥
  HandlerFreeᶜ (unbox i N)              = HandlerFreeᶜ N
  HandlerFreeᶜ (box ρ V N)              = HandlerFreeᵛ V × HandlerFreeᶜ N
  HandlerFreeᶜ (M ⦂ᶜ C)                 = HandlerFreeᶜ M
