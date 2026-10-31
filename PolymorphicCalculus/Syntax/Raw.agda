------------------------------------------------------------------
-- Raw (well-scoped, untyped) syntax of values and computations --
--                                                              --
-- The input of inference: the formers of the typing rules but  --
-- subsumption, keeping only the annotations (a constant's base --
-- type, the operation of a `perform`, the duration of a        --
-- `delay`, the grade of a `box`, optional type annotations).   --
-- `RawV Θ n` and `RawC Θ n` are scoped by `Θ` and `n` term     --
-- variables, de Bruijn indices into the full context; a        --
-- definition is its position in the program context, from the  --
-- first. Handler clauses are scoped over `Θ +e` and `2 + n`    --
-- variables.                                                   --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import Grades.Base
open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec
open import Language.Operations

module PolymorphicCalculus.Syntax.Raw (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open BaseTypes BTs using (BaseType; BaseConstants)

open import PolymorphicCalculus.Syntax.Scopes
open import Language.Comparisons using (Cmp)
open import PolymorphicCalculus.Syntax.Grades S using (RExp)
open import PolymorphicCalculus.Syntax.Types  S using (OVType; OCType)

mutual

  data RawV (Θ : Scope) (n : ℕ) : Set where

    -- variables

    var     : Fin n
              -------
            → RawV Θ n

    -- uses of definitions

    usedef  : ℕ
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

    -- comparison of two values by one of the relations of `Cmp`

    cmp     : Cmp
            → RawV Θ n
            → RawV Θ n
            ---------
            → RawV Θ n

    -- lambda abstraction

    lam     : RawC Θ (suc n)
              ------------
            → RawV Θ n

    -- handlers; an operation clause binds the parameter and the boxed
    -- continuation

    handler : RawC Θ (suc n)
            → (Op → RawC (Θ +e) (suc (suc n)))
            ---------------------------------
            → RawV Θ n

    -- type annotation: it fixes a shape, its type variables flexible

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

    _⨟_     : RawC Θ n              -- input: \;2
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

    -- natural-number elimination

    caseℕ_`zero_`succ_
            : RawV Θ n
            → RawC Θ n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- sum elimination

    case+_`inl_`inr_
            : RawV Θ n
            → RawC Θ (suc n)
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- list elimination

    caseL_`nil_`cons_
            : RawV Θ n
            → RawC Θ n
            → RawC Θ (suc (suc n))
            --------------------
            → RawC Θ n

    -- primitive recursion on natural numbers, the step binding the
    -- predecessor, then the result of the recursive call

    recℕ    : RawV Θ n
            → RawC Θ n
            → RawC Θ (suc (suc n))
            --------------------
            → RawC Θ n

    -- primitive recursion on lists, as `recℕ` with the head and tail

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

    handle_`with_
            : RawC Θ n
            → RawV Θ n
            ---------
            → RawC Θ n

    -- unboxing a resource, typable only as a variable under annotations

    unbox   : RawV Θ n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- boxing up a value, usable after the grade

    box     : RExp Θ
            → RawV Θ n
            → RawC Θ (suc n)
            --------------
            → RawC Θ n

    -- type annotation

    _⦂ᶜ_    : RawC Θ n
            → OCType Θ
            ---------
            → RawC Θ n

infix 5 _⦂ᵛ_ _⦂ᶜ_

-- Numerals

numeral : ∀ {Θ n} → ℕ → RawV Θ n
numeral 0       = zero
numeral (suc k) = succ (numeral k)

mutual

  HandlerFreeᵛ : ∀ {Θ n} → RawV Θ n → Set
  HandlerFreeᵛ (succ V)     = HandlerFreeᵛ V
  HandlerFreeᵛ ⦉ V , W ⦊     = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᵛ (inl V)      = HandlerFreeᵛ V
  HandlerFreeᵛ (inr V)      = HandlerFreeᵛ V
  HandlerFreeᵛ (cons V W)   = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᵛ (cmp ⋈ V W)  = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᵛ (lam M)      = HandlerFreeᶜ M
  HandlerFreeᵛ (handler N H) = ⊥
  HandlerFreeᵛ (V ⦂ᵛ A)     = HandlerFreeᵛ V
  HandlerFreeᵛ _            = ⊤

  HandlerFreeᶜ : ∀ {Θ n} → RawC Θ n → Set
  HandlerFreeᶜ (return V)               = HandlerFreeᵛ V
  HandlerFreeᶜ (M ⨟ N)                  = HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (V · W)                  = HandlerFreeᵛ V × HandlerFreeᵛ W
  HandlerFreeᶜ (match V `in M)          = HandlerFreeᵛ V × HandlerFreeᶜ M
  HandlerFreeᶜ (absurd V)               = HandlerFreeᵛ V
  HandlerFreeᶜ (if V `then M `else N)   = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (caseℕ V `zero M `succ N) = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (case+ V `inl M `inr N)   = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (recℕ V M N)              = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (caseL V `nil M `cons N)  = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (recL V M N)              = HandlerFreeᵛ V × HandlerFreeᶜ M × HandlerFreeᶜ N
  HandlerFreeᶜ (perform op V M)         = HandlerFreeᵛ V × HandlerFreeᶜ M
  HandlerFreeᶜ (delay τ M)              = HandlerFreeᶜ M
  HandlerFreeᶜ (handle M `with V)      = HandlerFreeᶜ M × HandlerFreeᵛ V
  HandlerFreeᶜ (unbox V N)              = HandlerFreeᵛ V × HandlerFreeᶜ N
  HandlerFreeᶜ (box ρ V N)              = HandlerFreeᵛ V × HandlerFreeᶜ N
  HandlerFreeᶜ (M ⦂ᶜ C)                 = HandlerFreeᶜ M
