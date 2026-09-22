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
-- claim on a boxed resource can be refused for doing the right   --
-- things in the wrong order. The unit runs the other way too: it --
-- is the *least* grade here, where the node's windows leave it   --
-- only minimal, so a non-resuming handler clause -- refused      --
-- there -- is inferred here.                                     --
--                                                                --
-- Every example is discharged by `refl`, so what is inferred is  --
-- checked by computation, not asserted; every refusal is paired  --
-- with the side condition that fails, decided by the grade's own --
-- procedure.                                                     --
------------------------------------------------------------------

open import Data.List.Base using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero; suc; #_)
open import Data.Maybe using (just; nothing)
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

open import Syntax.Contexts spec using (Ctx; []; _∷_)

open import TypeInference.OpenSyntax.Grades         spec
open import TypeInference.OpenSyntax.Types          spec
open import TypeInference.OpenSyntax.ClosedContexts spec using (skel)

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

ex-unit : infer! [] (return ⋆) ≡ just (Unit , ûₑ)
ex-unit = refl

-- a boolean

ex-bool : infer! [] (return true) ≡ just (Bool , ûₑ)
ex-bool = refl

-- a base-typed constant: a reading is a number

ex-const : infer! [] (return (const reading 0)) ≡ just (Base reading , ûₑ)
ex-const = refl

-- a variable's type is looked up

ex-var : infer! ([] ∷ T.Bool) (return (var zero)) ≡ just (Bool , ûₑ)
ex-var = refl

-- a pair

ex-pair : infer! [] (return ⦉ ⋆ , true ⦊) ≡ just (Unit |×| Bool , ûₑ)
ex-pair = refl

-- a lambda: none of `α₁ ⇒ (α₂ ‼ e)` is fixed in advance

ex-lam : infer! [] (return (lam (return true)))
       ≡ just (Unit ⇒ (Bool ‼ ûₑ) , ûₑ)
ex-lam = refl

-- an application: the argument type and the latent effect both come
-- from the function's type

ex-app : infer! ([] ∷ (T.Bool T.⇒ (T.Bool T.‼ uₑ))) (var zero · true)
       ≡ just (Bool , ûₑ)
ex-app = refl

-- a `let`: the two effects are multiplied, which here is the language
-- product of the two sets of runs

ex-seq : infer! [] (return true ⨟ return (var zero))
       ≡ just (Bool , ûₑ)
ex-seq = refl

-- a boolean elimination: the branch's grade is the union of the arms',
-- and two arms that do nothing between them make one run, the empty one

ex-if : infer! [] (if true `then return ⋆ `else return ⋆)
      ≡ just (Unit , ûₑ)
ex-if = refl

-- pattern-matching a pair

ex-match : infer! [] (match ⦉ ⋆ , true ⦊ `in return (var zero))
         ≡ just (Bool , ûₑ)
ex-match = refl

-- eliminating the empty type: the result type is unconstrained, and
-- defaulted

ex-absurd : infer! ([] ∷ T.Empty) (absurd (var zero)) ≡ just (Unit , ûₑ)
ex-absurd = refl

-- performing an operation: the result type is the operation's arity
-- and the effect is the one-event run that performs it, multiplied by
-- the continuation's

ex-perform : infer! [] (perform read ⋆ (return (var zero)))
           ≡ just (Base reading , econst (op-grade read))
ex-perform = refl

-- delaying: the declared duration becomes a delay in the run

ex-delay : infer! [] (delay 2 (return ⋆))
         ≡ just (Unit , econst (of-natᵉ 2))
ex-delay = refl

-- boxing: the box's grade is not annotated, and nothing constrains it,
-- so polarity defaults it to the unit -- here the allowance permitting
-- only the empty run

ex-box : infer! [] (box ⋆ (return (var zero)))
       ≡ just ([ ûᵣ ] Unit , ûₑ)
ex-box = refl

-- unboxing a boxed variable, at the unit allowance, which permits
-- nothing but the empty run -- and nothing has elapsed

ex-unbox : infer! ([] ∷ (T.[ uᵣ ] T.Bool)) (unbox zero (return (var zero)))
         ≡ just (Bool , ûₑ)
ex-unbox = refl

-- `handle` is inferred here. A clause that drops its continuation runs
-- in the unit effect, and the unit -- the empty run -- stays within
-- every allowance, so the clause's grade side condition holds. The
-- same program is refused in `Demo.TimeIntervals`, where a window
-- containing only `0` sits below no operation's.

ex-handle : infer! [] (handle (return ⋆) `with (λ op → return ⋆) `in (return ⋆))
          ≡ just (Unit , ûₑ)
ex-handle = refl

-- and its derivation in the source system, the clause's slack read off
-- `minₑ`

ex-handle-pipeline :
  typeOf (inferImpl [] (handle (return ⋆) `with (λ op → return ⋆) `in (return ⋆)))
  ≡ just (T.Unit , uₑ)
ex-handle-pipeline = refl

-- Clauses that use their continuation. Its effect is the clause's rigid
-- `e''`, and the unknowns bounded below by it alone, or by the unit,
-- are sent to those bounds before the clause's scope closes. `forward`
-- is `Worked.Typing.Core`'s `forwarding` clause.

ex-forward : infer! [] forward ≡ just (Unit , ûₑ)
ex-forward = refl

ex-unboxing : infer! [] unboxing ≡ just (Unit , ûₑ)
ex-unboxing = refl

ex-performing : infer! [] performing ≡ just (Unit , ûₑ)
ex-performing = refl

-- the declarative derivation, with `forwarding` itself as the clause,
-- and the pipeline's, at the same grade

forward-typed : [] TC.⊢C⦂ T.Unit TC.‼ (uₑ ·ₑ uₑ)
forward-typed = TC.handle_`with_`in (TC.return TC.⋆)
                  (λ op ε'' → TC.forwarding op ε'') (TC.return TC.⋆)

ex-forward-pipeline : typeOf (inferImpl [] forward) ≡ just (T.Unit , uₑ ·ₑ uₑ)
ex-forward-pipeline = refl

-- Resuming twice is refused, as the source system refuses it: the
-- second resumption uses a continuation that is not eternal across the
-- lock `∣ e'' ∣` the first one leaves, and the clause's effect would be
-- `op-grade op · (e'' · e'')`, a run that repeats what `e''` permits.

ex-resumingTwice : infer! [] resumingTwice ≡ nothing
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

ex-store : infer! [] store
         ≡ just (Unit , econst (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆))
ex-store = refl

ex-store-pipeline : typeOf (inferImpl [] store)
                  ≡ just (T.Unit , within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆)
ex-store-pipeline = refl

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

ex-branch-ops : infer! [] branch-ops
              ≡ just (Unit , econst (within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆))
ex-branch-ops = refl

ex-branch-ops-pipeline : typeOf (inferImpl [] branch-ops)
                       ≡ just (T.Unit , within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆)
ex-branch-ops-pipeline = refl

-- An arm that returns bounds the branch's effect unknown by the unit,
-- which is least here, so the closer discharges that bound instead of
-- folding it in and the other arm's run stands alone. The interval
-- spec, whose unit is only minimal, has to keep both and reports the
-- widened window `[ 0 , ↑ 1 ]`.

branch-ret : RawC 0
branch-ret = if true `then perform read ⋆ (return ⋆) `else return ⋆

ex-branch-ret : infer! [] branch-ret
              ≡ just (Unit , econst (op-grade read))
ex-branch-ret = refl

-- three arms, three bounds: nesting a branch inside a branch puts
-- three lower bounds on one effect unknown, and the fold lists all
-- three, where a window can only keep the extreme endpoints of the
-- three durations

branch-ops³ : RawC 0
branch-ops³ = if true `then perform read ⋆ (return ⋆)
                      `else (if true `then perform write (const reading 0) (return ⋆)
                                     `else perform send (const reading 0) (return ⋆))

ex-branch-ops³ : infer! [] branch-ops³
               ≡ just (Unit , econst (within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ∣ ⌈ send ⌉ ⟆))
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
-- so a reading is usable only where nothing at all has elapsed.

reading-stale : ¬ (uᵣ ·ᵣ op-grade read ≾ᵣ uᵣ)
reading-stale = fails

Γᵣ Γₙ : Ctx
Γᵣ = [] ∷ T.Base reading
Γₙ = [] ∷ T.Base nodeid

carry-over : RawC 1
carry-over = perform read ⋆ (return (var (suc zero)))

ex-reading-stale : infer! Γᵣ carry-over ≡ nothing
ex-reading-stale = refl

-- the node's identifier is eternal, so `var` does not ask, and it
-- crosses the operation's lock

ex-nodeid-carries : infer! Γₙ carry-over
                  ≡ just (Base nodeid , econst (op-grade read))
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

Γₚ : Ctx
Γₚ = [] ∷ (T.[ permit ] T.Bool)

-- the reading the permit names keeps it open

unbox-after-read : RawC (skel Γₚ)
unbox-after-read = perform read ⋆ (unbox (suc zero) (return (var zero)))

ex-unbox-after-read : infer! Γₚ unbox-after-read
                    ≡ just (Bool , econst (op-grade read))
ex-unbox-after-read = refl

ex-unbox-after-read-pipeline : typeOf (inferImpl Γₚ unbox-after-read)
                             ≡ just (T.Bool , op-grade read ·ₑ uₑ)
ex-unbox-after-read-pipeline = refl

-- idling draws on the same budget as working, so three ticks of it
-- discharge the claim as well

unbox-after-delay : RawC (skel Γₚ)
unbox-after-delay = delay 3 (unbox zero (return (var zero)))

ex-unbox-after-delay : infer! Γₚ unbox-after-delay
                     ≡ just (Bool , econst (of-natᵉ 3))
ex-unbox-after-delay = refl

-- and a store, which the budget covers at `costʰⁱ write = 3`

unbox-after-write : RawC (skel Γₚ)
unbox-after-write =
  perform write (const reading 0) (unbox (suc zero) (return (var zero)))

ex-unbox-after-write : infer! Γₚ unbox-after-write
                     ≡ just (Bool , econst (op-grade write))
ex-unbox-after-write = refl

-- One tick too many and the budget is overspent. A `delay τ` locks the
-- context by `of-natʳ τ` and a `perform op` by the operation's own
-- grade, neither of which a coercion reaches, so `ρ'` is fixed by the
-- term and the refuted premise below is the whole of the reason.

budget-overspent : ¬ (uᵣ ·ᵣ of-natʳ 4 ≾ᵣ permit)
budget-overspent = fails

unbox-too-late : RawC (skel Γₚ)
unbox-too-late = delay 4 (unbox zero (return (var zero)))

ex-unbox-too-late : infer! Γₚ unbox-too-late ≡ nothing
ex-unbox-too-late = refl

-- a transmission costs six, which the three ticks do not buy, and the
-- permit does not name it

transmitting-closes-it : ¬ (uᵣ ·ᵣ op-grade send ≾ᵣ permit)
transmitting-closes-it = fails

unbox-after-send : RawC (skel Γₚ)
unbox-after-send =
  perform send (const reading 0) (unbox (suc zero) (return (var zero)))

ex-unbox-after-send : infer! Γₚ unbox-after-send ≡ nothing
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

Γₛ : Ctx
Γₛ = [] ∷ (T.[ scheduled ] T.Bool)

-- the store falls inside the window the permit budgets for it

in-order : RawC (skel Γₛ)
in-order =
  perform read ⋆
    (perform write (var zero)
      (perform send (const reading 0)
        (unbox (suc (suc (suc zero))) (return (var zero)))))

ex-in-order : infer! Γₛ in-order
            ≡ just (Bool , econst (within ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆))
ex-in-order = refl

-- the same three operations with the store after the transmission
-- overrun the permit: budget does not cross an operation the bound
-- names

out-of-order-closes-it :
  ¬ (uᵣ ·ᵣ op-grade read ·ᵣ op-grade send ·ᵣ op-grade write ≾ᵣ scheduled)
out-of-order-closes-it = fails

out-of-order : RawC (skel Γₛ)
out-of-order =
  perform read ⋆
    (perform send (var zero)
      (perform write (const reading 0)
        (unbox (suc (suc (suc zero))) (return (var zero)))))

ex-out-of-order : infer! Γₛ out-of-order ≡ nothing
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

ex-fold-then-mul : infer! [] fold-then-mul
                 ≡ just (Unit , econst (within ⟅ ⌈ read ⌉ ∣ ⌈ write ⌉ ⟆))
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

ex-branch-ops³-flat : infer! [] branch-ops³-flat
                    ≡ just (Unit , econst (op-grade read))
ex-branch-ops³-flat = refl

ex-trimming : within ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∣ ⌈ read ⌉ ⟆ ≡ within ⟅ ⌈ read ⌉ ⟆
ex-trimming = refl

-- The slack variable of a sequencing's first component is resolved
-- before the composite effect is built.

ex-seq-op : infer! [] (perform read ⋆ (return (var zero)) ⨟ return ⋆)
          ≡ just (Unit , econst (op-grade read))
ex-seq-op = refl

-- The tightening pass. Subtyping is contravariant in a box's grade, so
-- the result type's fresh grade variable is bounded above by the
-- annotation and never below: tightening sends it there, and the permit
-- is reported rather than coarsened.

ex-box-grade : infer! ([] ∷ (T.[ permit ] T.Bool)) (return (var zero))
             ≡ just ([ rconst permit ] Bool , ûₑ)
ex-box-grade = refl

-- Polarity defaults. The identity function constrains its argument
-- type from neither side, so it is defaulted, and the latent effect
-- stays slack.

ex-default : infer! [] (return (lam (return (var zero))))
           ≡ just (Unit ⇒ (Unit ‼ ûₑ) , ûₑ)
ex-default = refl

-- The escape check, on the two binder orders of `Demo.Generic`.

ex-escape : solved? (gsolveImpl escC) ≡ nothing
ex-escape = refl

ex-escape-ok : solved? (gsolveImpl okC) ≡ just tt
ex-escape-ok = refl

-- Rigid scopes. An unknown local to the scope and bounded below by the
-- rigid alone is sent to it; an outer unknown bounded above by an
-- expression in the rigid is bounded by that expression at the least
-- rigid, the unit; a local unknown bounded below by a product with
-- itself is left alone, and the constraint declined.

ex-local : solved? (gsolveImpl localC) ≡ just tt
ex-local = refl

ex-strip : solved? (gsolveImpl stripC) ≡ just tt
ex-strip = refl

ex-cyc : solved? (gsolveImpl cycC) ≡ nothing
ex-cyc = refl

-- The pipeline, end to end.

ex-pipeline : typeOf (inferImpl [] (return true)) ≡ just (T.Bool , uₑ)
ex-pipeline = refl

ex-pipeline-op : typeOf (inferImpl [] (perform read ⋆ (return (var zero))))
               ≡ just (T.Base reading , op-grade read ·ₑ uₑ)
ex-pipeline-op = refl

------------------------------------------------------------------------
-- 5. The library benchmark
--
-- The eight shapes of `Demo.Generic` go through `reportOn`, the open
-- path, which hands back a qualified type rather than a ground
-- solution. Each is stated twice, the full report and its hypothesis
-- counts by sort. The two whose arms carry different effects,
-- `branchE` and `seqBranch`, are stated on the ground path as well.
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

  ex-unit-report : reportOf unit
                 ≡ just (scope 0 0 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-unit-report = refl

  ex-unit-size : sizeOf unit ≡ just (0 , 0 , 0 , 0 , 0)
  ex-unit-size = refl

  -- `compose`, with one qualifier: the lock that the capture of `g`
  -- crosses

  ex-compose-report : reportOf compose
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

  ex-compose-size : sizeOf compose ≡ just (0 , 0 , 1 , 0 , 0)
  ex-compose-size = refl

  -- `twice`: the two uses of `f` leave two subtyping atoms, and the
  -- lock leaves one qualifier

  ex-twice-report : reportOf twice
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

  ex-twice-size : sizeOf twice ≡ just (0 , 2 , 1 , 0 , 0)
  ex-twice-size = refl

  -- `branch`: one subtyping atom per arm, and no grade ordering at all

  ex-branch-report : reportOf branch
                   ≡ just (scope 19 0 10 ,
                           (Bool ⇒ (tvar (# 11)
                                     ⇒ (tvar (# 3) ⇒ tvar (# 6) ‼ ûₑ) ‼ ûₑ)
                                   ‼ ûₑ)
                             ‼ ûₑ ,
                           []ᴸ ,
                           (# 3 , # 6) ∷ᴸ (# 11 , # 6) ∷ᴸ []ᴸ ,
                           []ᴸ , []ᴸ , []ᴸ)
  ex-branch-report = refl

  ex-branch-size : sizeOf branch ≡ just (0 , 2 , 0 , 0 , 0)
  ex-branch-size = refl

  -- `branchE`: the arms carry different effects, so both bound the
  -- result's effect unknown from below, and the report carries their
  -- join rather than a residual ordering

  ex-branchE-report : reportOf branchE
                    ≡ just (scope 15 0 10 ,
                            ((Unit ⇒ Unit ‼ evar (# 1))
                              ⇒ (Bool
                                  ⇒ Unit ‼ (econst (op-grade read)
                                             ⊔̂ₑ evar (# 1)))
                                ‼ ûₑ)
                              ‼ ûₑ ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-branchE-report = refl

  ex-branchE-size : sizeOf branchE ≡ just (0 , 0 , 0 , 0 , 0)
  ex-branchE-size = refl

  -- the ground path takes `f`'s latent effect to be the unit, and the
  -- join of the two arms is then a constant

  ex-branchE : infer! [] branchE
             ≡ just ((Unit ⇒ (Unit ‼ ûₑ))
                       ⇒ ((Bool ⇒ (Unit ‼ econst (op-grade read))) ‼ ûₑ) , ûₑ)
  ex-branchE = refl

  -- `seqBranch`: the same join, standing underneath a product. The
  -- product is distributed over it, and the arm that carries two
  -- constants has them multiplied into one.

  ex-seqBranch-report : reportOf seqBranch
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

  ex-seqBranch-size : sizeOf seqBranch ≡ just (0 , 0 , 0 , 0 , 0)
  ex-seqBranch-size = refl

  -- and here both alternatives of the join are constants, so it is
  -- one too

  ex-seqBranch : infer! [] seqBranch
               ≡ just ((Unit ⇒ (Unit ‼ ûₑ))
                         ⇒ ((Bool ⇒ (Unit ‼ econst (op-grade read ·ₑ op-grade read
                                                    ⊔ₑ op-grade read)))
                             ‼ ûₑ) , ûₑ)
  ex-seqBranch = refl

  -- `keep`: the box grade stays a variable, and the one var-rule
  -- disjunction on it is all that is left

  ex-keep-report : reportOf keep
                 ≡ just (scope 8 3 3 ,
                         (tvar (# 4) ⇒ [ rvar (# 1) ] tvar (# 4) ‼ ûₑ) ‼ ûₑ ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ ,
                         (tvar (# 4) , rvar (# 1)) ∷ᴸ []ᴸ)
  ex-keep-report = refl

  ex-keep-size : sizeOf keep ≡ just (0 , 0 , 0 , 0 , 1)
  ex-keep-size = refl

  -- `wrap` is reported here, where `Demo.TimeIntervals` declines it:
  -- the clause's slack needs the effect unit to be least, and the
  -- empty run is

  ex-wrap-report : reportOf wrap
                 ≡ just (scope 11 0 8 ,
                         ((Unit ⇒ Unit ‼ evar (# 1)) ⇒ Unit ‼ evar (# 1))
                           ‼ ûₑ ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-wrap-report = refl

  ex-wrap-size : sizeOf wrap ≡ just (0 , 0 , 0 , 0 , 0)
  ex-wrap-size = refl
