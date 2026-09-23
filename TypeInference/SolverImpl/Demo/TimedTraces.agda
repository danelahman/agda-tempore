------------------------------------------------------------------
-- The solver at the sensor node's timed traces.                  --
--                                                                --
-- `Worked.Typing.Core` over `Worked.Traces.Timed.RightSided`     --
-- grades both effects and resources by finite sets of timed      --
-- runs, read as allowances: a computation is graded by a set     --
-- when each of its runs stays within one of its bounds, a        --
-- bound's operations being permissions and its delays a budget.  --
-- The grade system is the identity, so `mapᵉ` reduces away and   --
-- `unbox`'s resource bound is weighed against the very sets that --
-- grade effects.                                                 --
--                                                                --
-- Five sections: the plumbing; one example per raw-term former;  --
-- what these grades do; what the solver does with them; and the  --
-- library benchmark.                                             --
--                                                                --
-- What this grade sees that `Demo.TimeIntervals`' windows cannot --
-- is *which* operations a run performed and *where*. A branch's  --
-- grade is the union of its arms' runs rather than a window      --
-- spanning them, a sequence's grade is the run it makes, and a   --
-- claim on a boxed resource can fail for doing the right things  --
-- in the wrong order. The unit runs the other way too: it is the --
-- *least* grade here, where the node's windows leave it only     --
-- minimal, so a non-resuming handler clause -- refused there --  --
-- is inferred here.                                              --
--                                                                --
-- Every example is discharged by `refl`, so what is inferred is  --
-- checked by computation, not asserted; every program refused    --
-- for a closed ordering is paired with that ordering's           --
-- refutation, decided by the grade's own procedure.              --
------------------------------------------------------------------

open import Data.List.Base using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero; suc; #_)
open import Data.Bool.Base using (true)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costʰⁱ; costʰⁱ-pos;
         ε; _∙_; ⌈_⌉; ⟨_⟩)

open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided
  using (right-sided; Bounds; within_; unbounded; holds; fails;
         Antichain; ≾-⊥; ⟅_⟆; ⟅_∣_⟆; ⟅_∣_∣_⟆)

import Syntax.Grades.Example.Worked.Typing.Core

import Syntax.Types
import TypeInference.SolverImpl.Demo.Generic

open import TypeInference.Scopes

module TypeInference.SolverImpl.Demo.TimedTraces where

------------------------------------------------------------------------
-- 1. Setup
--
-- The specification is `Worked.Typing.Core`'s -- the sensor node's
-- three operations over an identity grade system -- at the grade of
-- trace allowances, each operation graded by the one-event run that
-- performs it. The solver is parametric in an enumeration of the
-- operations and in the two optional proofs that a unit is least, the
-- grades deciding their own orders; instantiating it here, and
-- `Demo.Generic` with it, fixes the wrappers the rest of the module
-- runs.

opTime₀ : Op → Antichain
opTime₀ o = ⟅ ⌈ o ⌉ ⟆

opTime : Op → Bounds
opTime o = within (opTime₀ o)

module TC = Syntax.Grades.Example.Worked.Typing.Core right-sided opTime

spec : LanguageSpec
spec = TC.spec

-- the node's two base types: a sensor reading, and the node's own
-- identifier, which is eternal

open TC using (reading; nodeid)

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops using (op-grade)

import Syntax.Types spec as T

open import Syntax.Contexts spec using ([])

open import TypeInference.OpenSyntax.Grades         spec
open import TypeInference.OpenSyntax.Types          spec
open import TypeInference.OpenSyntax.Contexts       spec using (OCtx; _∷_)

open import TypeInference.Raw.Syntax spec

open import TypeInference.SolverImpl.Enum spec using (OpEnum)

-- The order is decided by the grade's own procedure, so an ordering
-- between two written-out sets is settled by computation.
--
-- Both units are least: the unit is `{ ε }`, and the empty run stays
-- within every bound and within `unbounded`. So both options are taken,
-- where `Demo.TimeIntervals` declines both.

uᵇ-least : (P : Bounds) → uₑ ≾ₑ P
uᵇ-least = ≾-⊥

-- the node has three operations

ops₃ : OpEnum
ops₃ = record { ops = read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ ; complete = c }
  where
    c : (op : Op) → op ∈ (read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ)
    c read  = here refl
    c write = there (here refl)
    c send  = there (there (here refl))

-- `read`'s parameter is the unit type, so `⋆` is what the performing
-- shapes pass it

module G = TypeInference.SolverImpl.Demo.Generic
             spec ops₃ (just uᵇ-least) (just uᵇ-least) read ⋆

open G

------------------------------------------------------------------------
-- 2. The language, former by former
--
-- One small program per raw-term former, as coverage. What the grades
-- themselves do is left to section 3.

-- the unit value

ex-unit : reportOf Γ∅ (return ⋆)
        ≡ just (scope 0 0 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unit = refl

-- a boolean

ex-bool : reportOf Γ∅ (return true)
        ≡ just (scope 0 0 1 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-bool = refl

-- a base-typed constant: a reading is a number

ex-const : reportOf Γ∅ (return (const reading 0))
         ≡ just (scope 0 0 1 ,
                 Base reading ‼ ûₑ ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-const = refl

-- a variable's type is looked up

ex-var : reportOf (Γ∅ ∷ Bool) (return (var zero))
       ≡ just (scope 1 0 1 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-var = refl

-- a pair

ex-pair : reportOf Γ∅ (return ⦉ ⋆ , true ⦊)
        ≡ just (scope 0 0 1 ,
                (Unit |×| Bool) ‼ ûₑ ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-pair = refl

-- a lambda: none of `α₁ ⇒ (α₂ ‼ e)` is fixed in advance

ex-lam : reportOf Γ∅ (return (lam (return true)))
       ≡ just (scope 4 0 3 ,
               (tvar (# 1) ⇒ (Bool ‼ ûₑ)) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-lam = refl

-- an application: the argument type and the latent effect both come
-- from the function's type

ex-app : reportOf (Γ∅ ∷ (Bool ⇒ (Bool ‼ ûₑ))) (var zero · true)
       ≡ just (scope 3 0 2 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-app = refl

-- a `let`: the two effects are multiplied, which here is the language
-- product of the two sets of runs

ex-seq : reportOf Γ∅ (return true ⨟ return (var zero))
       ≡ just (scope 1 0 3 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-seq = refl

-- a boolean elimination: the branch's grade is the union of the arms',
-- and two arms that do nothing between them make one run, the empty one

ex-if : reportOf Γ∅ (if true `then return ⋆ `else return ⋆)
      ≡ just (scope 0 0 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-if = refl

-- pattern-matching a pair

ex-match : reportOf Γ∅ (match ⦉ ⋆ , true ⦊ `in return (var zero))
         ≡ just (scope 1 0 1 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-match = refl

-- eliminating the empty type: the result type and the effect are
-- unconstrained, and stay variables

ex-absurd : reportOf (Γ∅ ∷ Empty) (absurd (var zero))
          ≡ just (scope 1 0 1 ,
                  tvar (# 0) ‼ evar (# 0) ,
                  []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-absurd = refl

-- performing an operation: the result type is the operation's arity
-- and the effect is the one-event run that performs it, multiplied by
-- the continuation's

ex-perform : reportOf Γ∅ (perform read ⋆ (return (var zero)))
           ≡ just (scope 1 0 2 ,
                   Base reading ‼ econst (op-grade read) ,
                   []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-perform = refl

-- delaying: the declared duration becomes a delay in the run

ex-delay : reportOf Γ∅ (delay 2 (return ⋆))
         ≡ just (scope 0 0 2 ,
                 Unit ‼ econst (of-natᵉ 2) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-delay = refl

-- boxing: the box's grade is not annotated, and nothing constrains it,
-- so it stays a variable

ex-box : reportOf Γ∅ (box ⋆ (return (var zero)))
       ≡ just (scope 1 2 1 ,
               ([ rvar (# 0) ] Unit) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-box = refl

-- unboxing a boxed variable, at the unit allowance, which permits
-- nothing but the empty run -- and nothing has elapsed

ex-unbox : reportOf (Γ∅ ∷ [ ûᵣ ] Bool) (unbox zero (return (var zero)))
         ≡ just (scope 2 0 1 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unbox = refl

-- `handle` is inferred here. A clause that drops its continuation runs
-- in the unit effect, and the unit -- the empty run -- stays within
-- every allowance, so the clause's grade side condition holds. The
-- same program is refused in `Demo.TimeIntervals`, where a window
-- containing only `0` sits below no operation's.

ex-handle : reportOf Γ∅ (handle (return ⋆) `with (λ op → return ⋆) `in (return ⋆))
          ≡ just (scope 1 0 3 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-handle = refl

-- Clauses that use their continuation. Its effect is the clause's rigid
-- `e''`, and the unknowns bounded below by it alone, or by the unit,
-- are sent to those bounds before the clause's scope closes. `forward`
-- is `Worked.Typing.Core`'s `forwarding` clause.

ex-forward : reportOf Γ∅ forward
           ≡ just (scope 10 0 12 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-forward = refl

ex-unboxing : reportOf Γ∅ unboxing
            ≡ just (scope 4 0 6 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unboxing = refl

ex-performing : reportOf Γ∅ performing
              ≡ just (scope 1 0 6 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-performing = refl

-- the declarative derivation, with `forwarding` itself as the clause

forward-typed : [] TC.⊢C⦂ T.Unit TC.‼ (uₑ ·ₑ uₑ)
forward-typed = TC.handle_`with_`in (TC.return TC.⋆)
                  (λ op ε'' → TC.forwarding op ε'') (TC.return TC.⋆)

-- Resuming twice is refused, as the source system refuses it: the
-- second resumption uses a continuation that is not eternal across the
-- lock `∣ e'' ∣` the first one leaves, and the clause's effect would be
-- `op-grade op · (e'' · e'')`, a run that repeats what `e''` permits.

ex-resumingTwice : reportOf Γ∅ resumingTwice ≡ nothing
ex-resumingTwice = refl

------------------------------------------------------------------------
-- 3. What these grades do
--
-- Effect grades and resource grades are the same monoid -- finite sets
-- of timed traces, read as the bounds a run must stay within -- and the
-- projection between them is the identity.

-- `mapᵉ` is the identity, so the lock a computation puts on the context
-- *is* its effect grade, and `unbox`'s premise weighs a run against the
-- very sets that grade effects. Nothing is forgotten in between.

ex-same-carrier : R ≡ E
ex-same-carrier = refl

ex-mapᵉ : (ε₀ : E) → mapᵉ ε₀ ≡ ε₀
ex-mapᵉ _ = refl

-- Sequencing is the language product, so at singleton grades a
-- computation's grade is the run it makes, one event at a time.

store : RawC 0
store = perform read ⋆ (perform write (var zero) (return ⋆))

ex-store : reportOf Γ∅ store
         ≡ just (scope 0 0 3 ,
                 Unit ‼ econst (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-store = refl

-- A union of bounds is a join, so a branch's grade simply lists what
-- each arm does. A set names its members and nothing else: the order
-- the closer folded the arms' bounds in is not recorded, so writing the
-- same two bounds either way round is writing the same grade.

ex-⊔ₑ : op-grade read ⊔ₑ op-grade write ≡ within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆
ex-⊔ₑ = refl

ex-union-order : within ⟅ ⌈ write ⌉ ∣ ⌈ read ⌉ ⟆ ≡ within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆
ex-union-order = refl

branch-ops : RawC 0
branch-ops = if true `then perform read ⋆ (return ⋆)
                     `else perform write (const reading 0) (return ⋆)

-- `Demo.TimeIntervals` infers `[ 1 , ↑ 3 ]` for this shape: a window
-- wide enough for both arms, which no longer says which operation
-- either arm performed. Here the join is the list of the two runs.

ex-branch-ops : reportOf Γ∅ branch-ops
              ≡ just (scope 0 0 3 ,
                      Unit ‼ econst (within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆) ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-ops = refl

-- An arm that returns bounds the branch's effect unknown by the unit,
-- which is least here, so the closer discharges that bound instead of
-- folding it in and the other arm's run stands alone. The interval
-- spec, whose unit is only minimal, has to keep both and reports the
-- widened window `[ 0 , ↑ 1 ]`.

branch-ret : RawC 0
branch-ret = if true `then perform read ⋆ (return ⋆) `else return ⋆

ex-branch-ret : reportOf Γ∅ branch-ret
              ≡ just (scope 0 0 2 ,
                      Unit ‼ econst (op-grade read) ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-ret = refl

-- three arms, three bounds: nesting a branch inside a branch puts
-- three lower bounds on one effect unknown, and the fold lists all
-- three, where a window can only keep the extreme endpoints of the
-- three durations

branch-ops³ : RawC 0
branch-ops³ = if true `then perform read ⋆ (return ⋆)
                      `else (if true `then perform write (const reading 0) (return ⋆)
                                     `else perform send (const reading 0) (return ⋆))

ex-branch-ops³ : reportOf Γ∅ branch-ops³
               ≡ just (scope 0 0 4 ,
                       Unit ‼ econst (within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆) ,
                       []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-ops³ = refl

-- The effect unit is least: the empty run stays within every allowance.
-- That is what a non-resuming handler clause needs, and what the
-- interval spec's windows lack -- there `uₑ ≾ₑ op-grade read ·ₑ uₑ`
-- reads `1 ≤ 0`.

ex-uₑ-least : (ε₀ : E) → uₑ ≾ₑ ε₀
ex-uₑ-least = uᵇ-least

ex-uₑ-below-read : uₑ ≾ₑ op-grade read ·ₑ uₑ
ex-uₑ-below-read = holds

-- The resource unit is least too, where the interval spec's is
-- greatest: `uᵣ` permits nothing but the empty run, so no operation
-- fits inside it, and the greatest grade is `unbounded`.

ex-uᵣ-not-greatest : ¬ (op-grade read ≾ᵣ uᵣ)
ex-uᵣ-not-greatest = fails

ex-⊤ᵣ : (ρ : R) → ρ ≾ᵣ ⊤ᵣ
ex-⊤ᵣ = ≾-⊤ᵣ

ex-⊤ᵣ-is-unbounded : ⊤ᵣ ≡ unbounded
ex-⊤ᵣ-is-unbounded = refl

-- That is what makes a reading go stale. `var` asks for `ρ ≾ᵣ uᵣ`
-- unless the type is eternal, `ρ` being the run made since the
-- variable was bound, and the unit permits nothing but the empty run:
-- so a reading is usable only where nothing at all has elapsed. A
-- reading carried across an operation leaves the closed ordering
-- `op-grade read ≾ᵣ uᵣ` over, which `reading-stale` refutes, and is
-- refused.

reading-stale : ¬ (uᵣ ·ᵣ op-grade read ≾ᵣ uᵣ)
reading-stale = fails

Γᵣ Γₙ : OCtx ∅ˢ 1
Γᵣ = Γ∅ ∷ Base reading
Γₙ = Γ∅ ∷ Base nodeid

carry-over : RawC 1
carry-over = perform read ⋆ (return (var (suc zero)))

ex-reading-stale : reportOf Γᵣ carry-over ≡ nothing
ex-reading-stale = refl

-- the node's identifier is eternal, so `var` does not ask, and it
-- crosses the operation's lock

ex-nodeid-carries : reportOf Γₙ carry-over
                  ≡ just (scope 1 0 2 ,
                          Base nodeid ‼ econst (op-grade read) ,
                          []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-nodeid-carries = refl

------------------------------------------------------------------------
-- Temporal resources at these grades
--
-- `unbox`'s premise is `ρ' ≾ᵣ ρ₀`, `ρ'` the product of the locks
-- standing to the variable's right. A resource grade is an allowance --
-- an upper bound -- so a claim is refused for having spent too much,
-- where the interval spec's lower bounds refuse one for having waited
-- too little. What is spent is a run, not a number: the permit below
-- names a reading and budgets three ticks for whatever else happens.

permit : R
permit = within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ⟆

Γₚ : OCtx ∅ˢ 1
Γₚ = Γ∅ ∷ [ rconst permit ] Bool

-- the reading the permit names keeps it open

unbox-after-read : RawC 1
unbox-after-read = perform read ⋆ (unbox (suc zero) (return (var zero)))

ex-unbox-after-read : reportOf Γₚ unbox-after-read
                    ≡ just (scope 2 0 2 ,
                            Bool ‼ econst (op-grade read) ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unbox-after-read = refl

-- idling draws on the same budget as working, so three ticks of it
-- discharge the claim as well

unbox-after-delay : RawC 1
unbox-after-delay = delay 3 (unbox zero (return (var zero)))

ex-unbox-after-delay : reportOf Γₚ unbox-after-delay
                     ≡ just (scope 2 0 2 ,
                             Bool ‼ econst (of-natᵉ 3) ,
                             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unbox-after-delay = refl

-- and a store, which the budget covers at `costʰⁱ write = 3`

unbox-after-write : RawC 1
unbox-after-write =
  perform write (const reading 0) (unbox (suc zero) (return (var zero)))

ex-unbox-after-write : reportOf Γₚ unbox-after-write
                     ≡ just (scope 2 0 2 ,
                             Bool ‼ econst (op-grade write) ,
                             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unbox-after-write = refl

-- One tick too many and the budget is overspent. A `delay τ` locks the
-- context by `of-natʳ τ` and a `perform op` by the operation's own
-- grade, neither of which a coercion reaches, so `ρ'` is fixed by the
-- term: the premise is closed, `budget-overspent` refutes it, and the
-- program is refused.

budget-overspent : ¬ (uᵣ ·ᵣ of-natʳ 4 ≾ᵣ permit)
budget-overspent = fails

unbox-too-late : RawC 1
unbox-too-late = delay 4 (unbox zero (return (var zero)))

ex-unbox-too-late : reportOf Γₚ unbox-too-late ≡ nothing
ex-unbox-too-late = refl

-- a transmission costs six, which the three ticks do not buy, and the
-- permit does not name it: the premise is refuted, and the program
-- refused

transmitting-closes-it : ¬ (uᵣ ·ᵣ op-grade send ≾ᵣ permit)
transmitting-closes-it = fails

unbox-after-send : RawC 1
unbox-after-send =
  perform send (const reading 0) (unbox (suc zero) (return (var zero)))

ex-unbox-after-send : reportOf Γₚ unbox-after-send ≡ nothing
ex-unbox-after-send = refl

------------------------------------------------------------------------
-- Where the budget sits
--
-- A bound's slack pays only for what the run does between the two
-- operations it names, so a permit prescribes *when* its spare time is
-- available. The two runs below perform the same three operations and
-- take the same time; they differ in the order, and the permit tells
-- them apart. No interval grade can.

scheduled : R
scheduled = within ⟅ ⌈ read ⌉ ∙ ⟨ 3 ⟩ ∙ ⌈ send ⌉ ⟆

Γₛ : OCtx ∅ˢ 1
Γₛ = Γ∅ ∷ [ rconst scheduled ] Bool

-- the store falls inside the window the permit budgets for it

in-order : RawC 1
in-order =
  perform read ⋆
    (perform write (var zero)
      (perform send (const reading 0)
        (unbox (suc (suc (suc zero))) (return (var zero)))))

ex-in-order : reportOf Γₛ in-order
            ≡ just (scope 2 0 4 ,
                    Bool ‼ econst (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆) ,
                    []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-in-order = refl

-- the same three operations with the store after the transmission
-- overrun the permit: budget does not cross an operation the bound
-- names, and the premise it leaves is refuted: the program is refused

out-of-order-closes-it :
  ¬ (uᵣ ·ᵣ op-grade read ·ᵣ op-grade send ·ᵣ op-grade write ≾ᵣ scheduled)
out-of-order-closes-it = fails

out-of-order : RawC 1
out-of-order =
  perform read ⋆
    (perform send (var zero)
      (perform write (const reading 0)
        (unbox (suc (suc (suc zero))) (return (var zero)))))

ex-out-of-order : reportOf Γₛ out-of-order ≡ nothing
ex-out-of-order = refl

------------------------------------------------------------------------
-- 4. What the solver does
--
-- The passes, each on a program that isolates it.

-- The slack pass. Both arms bound the branch's effect unknown from
-- below and the closer folds the two bounds into their join -- the
-- union of the two lists -- which the sequencing then multiplies by
-- the unit.

fold-then-mul : RawC 0
fold-then-mul = branch-ops ⨟ return ⋆

ex-fold-then-mul : reportOf Γ∅ fold-then-mul
                 ≡ just (scope 0 0 5 ,
                         Unit ‼ econst (within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆) ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-fold-then-mul = refl

-- The join takes in every bound, an arm's slack included, and is
-- computed once that slack is settled, so three arms land on one
-- constant rather than on a product with an arm's slack. A set records
-- which runs are permitted, not how many arms asked for each, so three
-- arms performing the same operation leave that one run permitted.

branch-ops³-flat : RawC 0
branch-ops³-flat = if true `then perform read ⋆ (return ⋆)
                           `else (if true `then perform read ⋆ (return ⋆)
                                          `else perform read ⋆ (return ⋆))

ex-branch-ops³-flat : reportOf Γ∅ branch-ops³-flat
                    ≡ just (scope 0 0 4 ,
                            Unit ‼ econst (op-grade read) ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-ops³-flat = refl

ex-trimming : within ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∣ ⌈ read ⌉ ⟆ ≡ within ⟅ ⌈ read ⌉ ⟆
ex-trimming = refl

-- The slack variable of a sequencing's first component is resolved
-- before the composite effect is built.

ex-seq-op : reportOf Γ∅ (perform read ⋆ (return (var zero)) ⨟ return ⋆)
          ≡ just (scope 1 0 4 ,
                  Unit ‼ econst (op-grade read) ,
                  []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-seq-op = refl

-- A box grade bounded by an annotation. Subtyping is contravariant in
-- a box's grade, so the result type's fresh grade variable is bounded
-- above by the annotation and never below; the report keeps the
-- variable, qualified by the permit.

ex-box-grade : reportOf (Γ∅ ∷ [ rconst permit ] Bool) (return (var zero))
             ≡ just (scope 1 1 1 ,
                     ([ rvar (# 0) ] Bool) ‼ ûₑ ,
                     []ᴸ , []ᴸ , (rvar (# 0) , rconst permit) ∷ᴸ []ᴸ ,
                     []ᴸ , []ᴸ)
ex-box-grade = refl

-- The identity function constrains its argument type from neither
-- side, and is reported at `α ⇒ α`.

ex-default : reportOf Γ∅ (return (lam (return (var zero))))
           ≡ just (scope 5 0 3 ,
                   (tvar (# 1) ⇒ (tvar (# 1) ‼ ûₑ)) ‼ ûₑ ,
                   []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-default = refl

-- The escape check, on the two binder orders of `Demo.Generic`.

ex-escape : solveOn escC ≡ nothing
ex-escape = refl

ex-escape-ok : is-just (solveOn okC) ≡ true
ex-escape-ok = refl

-- Rigid scopes. An unknown local to the scope and bounded below by the
-- rigid alone is sent to it; an outer unknown bounded above by an
-- expression in the rigid is bounded by that expression at the least
-- rigid, the unit; a local unknown bounded below by a product with
-- itself is left alone, and the constraint declined.

ex-local : is-just (solveOn localC) ≡ true
ex-local = refl

ex-strip : is-just (solveOn stripC) ≡ true
ex-strip = refl

ex-top : is-just (solveOn topC) ≡ true
ex-top = refl

ex-strip-top : is-just (solveOn stripTopC) ≡ true
ex-strip-top = refl

ex-cyc : solveOn cycC ≡ nothing
ex-cyc = refl

------------------------------------------------------------------------
-- 5. The library benchmark
--
-- The eight shapes of `Demo.Generic`, each stated twice: the full
-- report and its hypothesis counts by sort.
--
-- Seven of the eight come out at exactly the scopes, shapes and counts
-- `Demo.TimeIntervals` reports, the grade constants inside being each
-- spec's own: none of the seven decides an ordering between two
-- written-out grades, so what survives is the same whatever the grades
-- are. `wrap` is the eighth, and the one the grades settle -- declined
-- there, reported here with nothing left over, since a clause that
-- drops its continuation needs the effect unit to be least.

module Library where

  -- `return ⋆`

  ex-unit-report : reportOf Γ∅ unit
                 ≡ just (scope 0 0 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-unit-report = refl

  ex-unit-size : sizeOf Γ∅ unit ≡ just (0 , 0 , 0 , 0 , 0)
  ex-unit-size = refl

  -- `compose`, with one qualifier: the lock that the capture of `g`
  -- crosses

  ex-compose-report : reportOf Γ∅ compose
                    ≡ just (scope 34 0 19 ,
                            ((tvar (# 18) ⇒ tvar (# 10) ‼ evar (# 5))
                              ⇒ ((tvar (# 10) ⇒ tvar (# 2) ‼ evar (# 1))
                                  ⇒ (tvar (# 18)
                                      ⇒ tvar (# 2) ‼ (evar (# 5) ·̂ₑ evar (# 1)))
                                    ‼ ûₑ)
                                ‼ ûₑ)
                              ‼ ûₑ ,
                            []ᴸ , []ᴸ ,
                            (∣ evar (# 5) ∣̂ᵉ , ûᵣ) ∷ᴸ []ᴸ ,
                            []ᴸ , []ᴸ)
  ex-compose-report = refl

  ex-compose-size : sizeOf Γ∅ compose ≡ just (0 , 0 , 1 , 0 , 0)
  ex-compose-size = refl

  -- `twice`: the two uses of `f` leave two subtyping atoms, and the
  -- lock leaves one qualifier

  ex-twice-report : reportOf Γ∅ twice
                  ≡ just (scope 20 0 12 ,
                          ((tvar (# 3) ⇒ tvar (# 4) ‼ evar (# 2))
                            ⇒ (tvar (# 12)
                                ⇒ tvar (# 4) ‼ (evar (# 2) ·̂ₑ evar (# 2)))
                              ‼ ûₑ)
                            ‼ ûₑ ,
                          []ᴸ ,
                          (# 4 , # 3) ∷ᴸ (# 12 , # 3) ∷ᴸ []ᴸ ,
                          (∣ evar (# 2) ∣̂ᵉ , ûᵣ) ∷ᴸ []ᴸ ,
                          []ᴸ , []ᴸ)
  ex-twice-report = refl

  ex-twice-size : sizeOf Γ∅ twice ≡ just (0 , 2 , 1 , 0 , 0)
  ex-twice-size = refl

  -- `branch`: one subtyping atom per arm, and no grade ordering at all

  ex-branch-report : reportOf Γ∅ branch
                   ≡ just (scope 19 0 10 ,
                           (Bool ⇒ (tvar (# 11)
                                     ⇒ (tvar (# 3) ⇒ tvar (# 6) ‼ ûₑ) ‼ ûₑ)
                                   ‼ ûₑ)
                             ‼ ûₑ ,
                           []ᴸ ,
                           (# 3 , # 6) ∷ᴸ (# 11 , # 6) ∷ᴸ []ᴸ ,
                           []ᴸ , []ᴸ , []ᴸ)
  ex-branch-report = refl

  ex-branch-size : sizeOf Γ∅ branch ≡ just (0 , 2 , 0 , 0 , 0)
  ex-branch-size = refl

  -- `branchE`: the arms carry different effects, so both bound the
  -- result's effect unknown from below, and the report carries their
  -- join rather than a residual ordering

  ex-branchE-report : reportOf Γ∅ branchE
                    ≡ just (scope 15 0 10 ,
                            ((Unit ⇒ Unit ‼ evar (# 1))
                              ⇒ (Bool
                                  ⇒ Unit ‼ (econst (op-grade read)
                                             ⊔̂ₑ evar (# 1)))
                                ‼ ûₑ)
                              ‼ ûₑ ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-branchE-report = refl

  ex-branchE-size : sizeOf Γ∅ branchE ≡ just (0 , 0 , 0 , 0 , 0)
  ex-branchE-size = refl

  -- `seqBranch`: the same join, standing underneath a product. The
  -- product is distributed over it, and the arm that carries two
  -- constants has them multiplied into one.

  ex-seqBranch-report : reportOf Γ∅ seqBranch
                      ≡ just (scope 15 0 13 ,
                              ((Unit ⇒ Unit ‼ evar (# 2))
                                ⇒ (Bool
                                    ⇒ Unit
                                       ‼ (econst (op-grade read ·ₑ op-grade read)
                                           ⊔̂ₑ (evar (# 2)
                                                ·̂ₑ econst (op-grade read))))
                                  ‼ ûₑ)
                                ‼ ûₑ ,
                              []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-seqBranch-report = refl

  ex-seqBranch-size : sizeOf Γ∅ seqBranch ≡ just (0 , 0 , 0 , 0 , 0)
  ex-seqBranch-size = refl

  -- `keep`: the box grade stays a variable, and the one var-rule
  -- disjunction on it is all that is left

  ex-keep-report : reportOf Γ∅ keep
                 ≡ just (scope 8 3 3 ,
                         (tvar (# 4) ⇒ [ rvar (# 1) ] tvar (# 4) ‼ ûₑ) ‼ ûₑ ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ ,
                         (tvar (# 4) , rvar (# 1)) ∷ᴸ []ᴸ)
  ex-keep-report = refl

  ex-keep-size : sizeOf Γ∅ keep ≡ just (0 , 0 , 0 , 0 , 1)
  ex-keep-size = refl

  -- `wrap` is reported here, where `Demo.TimeIntervals` declines it:
  -- the clause's slack needs the effect unit to be least, and the
  -- empty run is

  ex-wrap-report : reportOf Γ∅ wrap
                 ≡ just (scope 11 0 8 ,
                         ((Unit ⇒ Unit ‼ evar (# 1)) ⇒ Unit ‼ evar (# 1))
                           ‼ ûₑ ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-wrap-report = refl

  ex-wrap-size : sizeOf Γ∅ wrap ≡ just (0 , 0 , 0 , 0 , 0)
  ex-wrap-size = refl
