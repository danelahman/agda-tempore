------------------------------------------------------------------
-- The solver at the sensor node's time intervals.                --
--                                                                --
-- `Syntax.Grades.Example.Worked.Spec` grades a computation by a  --
-- two-sided window of elapsed time and a resource by a lower     --
-- bound on it, the projection between them keeping the window's  --
-- lower endpoint. It satisfies the solver's assumption, an       --
-- enumeration of the operations, but not the optional one that   --
-- the effect unit is least.                                      --
--                                                                --
-- Five sections: the plumbing; one example per raw-term former;  --
-- what these grades do, which is what the calculus is for; what  --
-- the solver does with them; and a second specification, whose   --
-- unit *is* least, with the library benchmark over both.         --
--                                                                --
-- Every example is discharged by `refl`, so what is inferred is  --
-- checked by computation, not asserted.                          --
------------------------------------------------------------------

open import Data.List.Base using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero; suc; #_)
open import Data.Bool.Base using (true)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩)
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_,_])
open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (spec; baseTypes; reading)

open import Syntax.Grades.Example.Time.RightSided
  using (𝕀ᵣ; [0,_]; ↑_; ∞; right-sided-intervals) renaming (_≾ₒ_ to _≾ᵈ_)
open import Syntax.Grades.Example.System.Identity using (identityGradeSystem)

import Syntax.GroundTypes

import TypeInference.OpenSyntax.Grades
import TypeInference.OpenSyntax.Types
import TypeInference.OpenSyntax.Contexts
import TypeInference.OpenSyntax.Hyps
import TypeInference.OpenSyntax.Subst
import TypeInference.Raw.Syntax
import TypeInference.Constraints.Syntax
import TypeInference.Constraints.Satisfaction
import TypeInference.SolverImpl.Enum
import TypeInference.SolverImpl.Restricted
import TypeInference.SolverImpl.Demo.Generic

open import TypeInference.Scopes

module TypeInference.SolverImpl.Demo.TimeIntervals where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops


open import TypeInference.OpenSyntax.Grades         spec
open import TypeInference.OpenSyntax.Types          spec
open import TypeInference.OpenSyntax.Contexts       spec using (OCtx; _∷_)

open import TypeInference.Raw.Syntax spec

open import TypeInference.SolverImpl.Enum spec using (OpEnum)

------------------------------------------------------------------------
-- 1. Setup
--
-- The solver is parametric in an enumeration of the operations and in
-- the two optional proofs that a unit is least; the grades decide their
-- own orders. Instantiating it here, and `Demo.Generic` with it,
-- fixes what the rest of the module runs: `reportOf`, a program's
-- principal report, and `solveOn`, the solver on a constraint.

-- the node has three operations

ops₃ : OpEnum
ops₃ = record { ops = read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ ; complete = c }
  where
    c : (op : Op) → op ∈ (read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ)
    c read  = here refl
    c write = there (here refl)
    c send  = there (there (here refl))

-- neither unit is least here, so both options are declined; `read`
-- takes no argument, so it is what the performing shapes perform

module G = TypeInference.SolverImpl.Demo.Generic
             spec ops₃ nothing nothing read ⋆

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

-- a base-typed constant, at the node's one base type

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
                Unit |×| Bool ‼ ûₑ ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-pair = refl

-- a lambda: none of `α₁ ⇒ (α₂ ‼ e)` is fixed in advance

ex-lam : reportOf Γ∅ (return (lam (return true)))
       ≡ just (scope 4 0 3 ,
               (tvar (# 1) ⇒ Bool ‼ ûₑ) ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-lam = refl

-- an application: the argument type and the latent effect both come
-- from the function's type

ex-app : reportOf (Γ∅ ∷ (Bool ⇒ (Bool ‼ ûₑ))) (var zero · true)
       ≡ just (scope 3 0 2 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-app = refl

-- a `let`: the two effects are multiplied

ex-seq : reportOf Γ∅ (return true ⨟ return (var zero))
       ≡ just (scope 1 0 3 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-seq = refl

-- a boolean elimination

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
-- and the effect is its execution window, multiplied by the
-- continuation's

ex-perform : reportOf Γ∅ (perform read ⋆ (return (var zero)))
           ≡ just (scope 1 0 2 ,
                   Base reading ‼ econst (op-grade read) ,
                   []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-perform = refl

-- delaying: the declared duration is charged to the effect

ex-delay : reportOf Γ∅ (delay 2 (return ⋆))
         ≡ just (scope 0 0 2 ,
                 Unit ‼ econst (of-natᵉ 2) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-delay = refl

-- boxing: the box's grade is not annotated, and stays a variable

ex-box : reportOf Γ∅ (box ⋆ (return (var zero)))
       ≡ just (scope 1 2 1 ,
               [ rvar (# 0) ] Unit ‼ ûₑ ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-box = refl

-- unboxing a boxed variable, at the unit grade, which demands nothing

ex-unbox : reportOf (Γ∅ ∷ [ ûᵣ ] Bool) (unbox zero (return (var zero)))
         ≡ just (scope 2 0 1 , Bool ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unbox = refl

-- `handle` is refused at these grades: a clause that does not resume
-- runs in the unit effect, which these windows do not put below an
-- operation's. Section 5 runs the same program over grades whose unit
-- is least.

ex-handle : reportOf Γ∅ (handle (return ⋆) `with (λ op → return ⋆) `in (return ⋆)) ≡ nothing
ex-handle = refl

-- A clause that resumes is inferred all the same. Its continuation's
-- effect is the clause's rigid `e''`, the unknowns bounded below by it
-- alone are sent to it before the clause's scope closes, and nothing is
-- left to ask of the unit. `forward` is `Worked.Typing.Core`'s
-- `forwarding` clause.

ex-handle-forward : reportOf Γ∅ forward
                  ≡ just (scope 10 0 12 ,
                          Unit ‼ ûₑ ,
                          []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-handle-forward = refl

-- A clause that unboxes its continuation, or performs, and then drops
-- it ends in the unit effect, and is refused as `ex-handle` is.

ex-handle-unboxing : reportOf Γ∅ unboxing ≡ nothing
ex-handle-unboxing = refl

ex-handle-performing : reportOf Γ∅ performing ≡ nothing
ex-handle-performing = refl

------------------------------------------------------------------------
-- 3. What these grades do
--
-- Effect grades are two-sided windows `[ n , m ]` ordered by
-- containment; resource grades are lower bounds `[ n ,+∞⟩` ordered by
-- `_≤_` reversed; and `mapᵉ` carries a window to the bound it licenses
-- by keeping its lower endpoint. Each of those turns into an
-- inference below.

-- Sequencing adds windows; a branch takes the smallest window
-- containing both arms'.

ex-⊔ₑ : op-grade read ⊔ₑ op-grade write ≡ [ 1 , ↑ 3 , s≤s z≤n ]
ex-⊔ₑ = refl

-- The effect unit is minimal, not least: it sits below no operation's
-- window, which is why a non-resuming handler clause is refused.

ex-uₑ-not-least : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
ex-uₑ-not-least (() , _)

-- The resource unit is greatest: weakening a resource grade lowers the
-- guarantee, and `[ 0 ,+∞⟩` guarantees nothing.

ex-uᵣ-greatest : (ρ : R) → ρ ≾ᵣ uᵣ
ex-uᵣ-greatest = ≾-⊤ᵣ

ex-≾ᵣ-down : [ 2 ,+∞⟩ ≾ᵣ [ 1 ,+∞⟩
ex-≾ᵣ-down = s≤s z≤n

ex-≾ᵣ-not-up : ¬ ([ 1 ,+∞⟩ ≾ᵣ [ 2 ,+∞⟩)
ex-≾ᵣ-not-up (s≤s ())

-- The grade morphism keeps the lower endpoint: a `write`, whose
-- execution time falls in `[ 2 , 3 ]`, licenses `[ 2 ,+∞⟩` of elapsed
-- resource -- all that is certain to have passed.

ex-mapᵉ : mapᵉ (op-grade write) ≡ [ 2 ,+∞⟩
ex-mapᵉ = refl

-- Two operations in the arms of a branch: the inferred effect is the
-- smallest window containing `[ 1 , 1 ]` and `[ 2 , 3 ]`.

branch-ops : RawC 0
branch-ops = if true `then perform read ⋆ (return ⋆)
                     `else perform write (const reading 0) (return ⋆)

ex-branch-ops : reportOf Γ∅ branch-ops
              ≡ just (scope 0 0 3 ,
                      Unit ‼ econst [ 1 , ↑ 3 , s≤s z≤n ] ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-ops = refl

-- An arm that returns instead contributes the unit window, so the
-- containing window reaches down to `0`.

branch-ret : RawC 0
branch-ret = if true `then perform read ⋆ (return ⋆) `else return ⋆

ex-branch-ret : reportOf Γ∅ branch-ret
              ≡ just (scope 0 0 2 ,
                      Unit ‼ econst [ 0 , ↑ 1 , z≤n ] ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-ret = refl

-- Two delays: `delay n` contributes `of-natᵉ n`, and the join spans
-- both durations.

branch-delay : RawC 0
branch-delay = if true `then delay 2 (return ⋆) `else delay 1 (return ⋆)

ex-branch-delay : reportOf Γ∅ branch-delay
                ≡ just (scope 0 0 3 ,
                        Unit ‼ econst [ 1 , ↑ 2 , s≤s z≤n ] ,
                        []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-delay = refl

-- Nesting a branch inside a branch puts three bounds on one effect
-- unknown, and the window spans all three durations.
-- `notes/ThreeArmBranch.agda` derives the same grade declaratively.

branch-delay³ : RawC 0
branch-delay³ = if true `then delay 1 (return ⋆)
                        `else (if true `then delay 2 (return ⋆)
                                       `else delay 3 (return ⋆))

ex-branch-delay³ : reportOf Γ∅ branch-delay³
                 ≡ just (scope 0 0 4 ,
                         Unit ‼ econst [ 1 , ↑ 3 , s≤s z≤n ] ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-delay³ = refl

-- an arm that returns contributes the unit window here too

branch-delay³-ret : RawC 0
branch-delay³-ret = if true `then return ⋆
                            `else (if true `then delay 2 (return ⋆)
                                           `else delay 3 (return ⋆))

ex-branch-delay³-ret : reportOf Γ∅ branch-delay³-ret
                     ≡ just (scope 0 0 3 ,
                             Unit ‼ econst [ 0 , ↑ 3 , z≤n ] ,
                             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-delay³-ret = refl

-- A resource boxed at `[ 2 ,+∞⟩` becomes available only once two ticks
-- stand between the binder and the `unbox`: that is the premise
-- `ρ' ≾ᵣ ρ₀` of the `unbox` rule, `ρ'` being the product of the locks
-- to the variable's right, which the term itself determines.

Γ₂ : OCtx ∅ˢ 1
Γ₂ = Γ∅ ∷ [ rconst [ 2 ,+∞⟩ ] Bool

-- a `write` elapses, and `mapᵉ [ 2 , 3 ] = [ 2 ,+∞⟩` meets the demand

unbox-after-write : RawC 1
unbox-after-write =
  perform write (const reading 0) (unbox (suc zero) (return (var zero)))

ex-unbox-after-write : reportOf Γ₂ unbox-after-write
                     ≡ just (scope 2 0 2 ,
                             Bool ‼ econst (op-grade write) ,
                             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unbox-after-write = refl

-- a `read` licenses only `[ 1 ,+∞⟩`, which does not: the ordering
-- `[ 1 ,+∞⟩ ≾ᵣ [ 2 ,+∞⟩` left over is closed, and false by
-- `ex-≾ᵣ-not-up`, so the program is refused; no derivation can choose
-- another `ρ'`

unbox-after-read : RawC 1
unbox-after-read =
  perform read ⋆ (unbox (suc zero) (return (var zero)))

ex-unbox-after-read : reportOf Γ₂ unbox-after-read ≡ nothing
ex-unbox-after-read = refl

-- idling meets the demand just as an operation does

unbox-after-delay : RawC 1
unbox-after-delay = delay 2 (unbox zero (return (var zero)))

ex-unbox-after-delay : reportOf Γ₂ unbox-after-delay
                     ≡ just (scope 2 0 2 ,
                             Bool ‼ econst (of-natᵉ 2) ,
                             []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-unbox-after-delay = refl

-- one tick short, and it does not: the same ordering is left, and the
-- program refused

unbox-too-soon : RawC 1
unbox-too-soon = delay 1 (unbox zero (return (var zero)))

ex-unbox-too-soon : reportOf Γ₂ unbox-too-soon ≡ nothing
ex-unbox-too-soon = refl

------------------------------------------------------------------------
-- 4. What the solver does
--
-- The passes, each on a program that isolates it: lower bounds on an
-- unknown folded by join, a box grade kept with its bound, unknowns
-- left open in the reported type, and an unknown escaping a rigid
-- binder refuted.

-- The slack pass. Both arms bound the branch's effect unknown from
-- below and the closer folds the two bounds into their join, which
-- the sequencing then multiplies by the unit.

fold-then-mul : RawC 0
fold-then-mul = branch-delay ⨟ return ⋆

ex-fold-then-mul : reportOf Γ∅ fold-then-mul
                 ≡ just (scope 0 0 5 ,
                         Unit ‼ econst [ 1 , ↑ 2 , s≤s z≤n ] ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-fold-then-mul = refl

-- An unknown whose bounds still hold an arm's own slack variable is
-- sent to their join all the same, and the join is computed once the
-- slack is settled. Three arms at one duration therefore land on a
-- single constant, not on a product with one arm's slack.

branch-delay³-flat : RawC 0
branch-delay³-flat = if true `then delay 1 (return ⋆)
                             `else (if true `then delay 1 (return ⋆)
                                            `else delay 1 (return ⋆))

ex-branch-delay³-flat : reportOf Γ∅ branch-delay³-flat
                      ≡ just (scope 0 0 4 ,
                              Unit ‼ econst (of-natᵉ 1) ,
                              []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-delay³-flat = refl

-- A conditional under a lambda. The branch's effect unknown bounds the
-- latent effect from below, and slack sends the latter to the former,
-- after which that ordering reads `e ≾ e` and bounds nothing: the
-- latent effect is the join of the two arms.

branch-lam : RawC 0
branch-lam = return (lam (if var zero `then delay 1 (return ⋆)
                                      `else delay 2 (return ⋆)))

ex-branch-lam : reportOf Γ∅ branch-lam
              ≡ just (scope 4 0 5 ,
                      (Bool ⇒ Unit ‼ econst [ 1 , ↑ 2 , s≤s z≤n ]) ‼ ûₑ ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-lam = refl

-- the same with equal arms

branch-lam₁ : RawC 0
branch-lam₁ = return (lam (if var zero `then delay 1 (return ⋆)
                                       `else delay 1 (return ⋆)))

ex-branch-lam₁ : reportOf Γ∅ branch-lam₁
               ≡ just (scope 4 0 5 ,
                       (Bool ⇒ Unit ‼ econst (of-natᵉ 1)) ‼ ûₑ ,
                       []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-branch-lam₁ = refl

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
-- variable, qualified by that bound.

ex-box-grade : reportOf (Γ∅ ∷ [ rconst [ 1 ,+∞⟩ ] Bool) (return (var zero))
             ≡ just (scope 1 1 1 ,
                     [ rvar (# 0) ] Bool ‼ ûₑ ,
                     []ᴸ , []ᴸ , (rvar (# 0) , rconst [ 1 ,+∞⟩) ∷ᴸ []ᴸ ,
                     []ᴸ , []ᴸ)
ex-box-grade = refl

-- both arms of a conditional bound that one variable above, by the
-- same expression, which is kept once

ex-box-branch : reportOf (Γ∅ ∷ Bool ∷ [ rconst [ 1 ,+∞⟩ ] Bool)
                  (if var (suc zero)
                    `then return (var zero)
                    `else return (var zero))
              ≡ just (scope 1 1 1 ,
                      [ rvar (# 0) ] Bool ‼ ûₑ ,
                      []ᴸ , []ᴸ , (rvar (# 0) , rconst [ 1 ,+∞⟩) ∷ᴸ []ᴸ ,
                      []ᴸ , []ᴸ)
ex-box-branch = refl

-- The identity function constrains its argument type from neither
-- side, and is reported at `α ⇒ α`.

ex-default : reportOf Γ∅ (return (lam (return (var zero))))
           ≡ just (scope 5 0 3 ,
                   (tvar (# 1) ⇒ tvar (# 1) ‼ ûₑ) ‼ ûₑ ,
                   []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-default = refl

-- The unknowns of every nesting level live in one store, so nesting
-- costs the solver nothing.

ex-lam² : reportOf Γ∅ (return (lam (return (lam (return true)))))
        ≡ just (scope 10 0 6 ,
                (tvar (# 6) ⇒ (tvar (# 3) ⇒ Bool ‼ ûₑ) ‼ ûₑ) ‼ ûₑ ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-lam² = refl

ex-lam³ : reportOf Γ∅ (return (lam (return (lam (return (lam (return true)))))))
        ≡ just (scope 18 0 10 ,
                (tvar (# 14)
                  ⇒ (tvar (# 10) ⇒ (tvar (# 3) ⇒ Bool ‼ ûₑ) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-lam³ = refl

ex-lam⁴ : reportOf Γ∅
            (return (lam (return (lam (return (lam (return (lam (return true)))))))))
        ≡ just (scope 28 0 15 ,
                (tvar (# 24)
                  ⇒ (tvar (# 20)
                      ⇒ (tvar (# 12) ⇒ (tvar (# 5) ⇒ Bool ‼ ûₑ) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ)
                  ‼ ûₑ ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
ex-lam⁴ = refl

-- The escape check, on the two binder orders of `Demo.Generic`.

ex-escape : solveOn escC ≡ nothing
ex-escape = refl

ex-escape-ok : is-just (solveOn okC) ≡ true
ex-escape-ok = refl

-- An unknown local to a rigid scope and bounded below by the rigid
-- alone is sent to the rigid before the scope closes.

ex-local : is-just (solveOn localC) ≡ true
ex-local = refl

-- An outer unknown bounded above by an expression in the rigid needs
-- that expression at the least rigid, which these windows lack.

ex-strip : solveOn stripC ≡ nothing
ex-strip = refl

-- An outer unknown bounded below by an expression in the rigid needs
-- that expression at the top rigid, which every grade has.

ex-top : is-just (solveOn topC) ≡ true
ex-top = refl

ex-strip-top : is-just (solveOn stripTopC) ≡ true
ex-strip-top = refl

-- The solver is principal on every constraint: a program the solver
-- accepts has a principal type.

module Unguarded where

  module OC = TypeInference.OpenSyntax.Contexts spec

  open import TypeInference.Principality            spec using (Principal; C[_,_])
  open import TypeInference.Principality.Restricted spec using (principal-on)
  open import TypeInference.SolverImpl.Restricted   spec ops₃ nothing nothing
    using (solverImplOn)

  -- a program the solver accepts has a principal solution-with-residue,
  -- and hence a principal type

  principal? : ∀ {n} → (Γ : OC.OCtx ∅ˢ n) → (M : RawC n) → Maybe (Principal Γ M)
  principal? Γ M with solveOn C[ Γ , M ] in e
  ... | nothing           = nothing
  ... | just (Θ' , σ , Q) = just (principal-on solverImplOn Γ M tt e)

  ex-principal : Σ[ p ∈ Principal Γ∅ unit ] (principal? Γ∅ unit ≡ just p)
  ex-principal = _ , refl

------------------------------------------------------------------------
-- 5. A second specification, and the benchmark
--
-- Right-sided intervals are deadlines `[0, n]`, ordered by `_≤_` on the
-- endpoint, so `[0, ↑0]` is below every grade. Both grade components
-- are this monoid, over the same sensor node. That least unit is
-- exactly what a non-resuming handler clause needs and what the
-- node's windows lack.

gradesᵈ : GradeSystem
gradesᵈ = identityGradeSystem right-sided-intervals

module Gᵈ = Syntax.GroundTypes gradesᵈ baseTypes

opTimeᵈ : Op → 𝕀ᵣ
opTimeᵈ read  = [0, ↑ 1 ]
opTimeᵈ write = [0, ↑ 3 ]
opTimeᵈ send  = [0, ↑ 6 ]

opsᵈ : Operations gradesᵈ baseTypes
opsᵈ = record
  { Op       = Op
  ; _≟ₒ_     = _≟ₒ_
  ; param    = λ { read → Gᵈ.Unit ; write → Gᵈ.Base reading ; send → Gᵈ.Base reading }
  ; arity    = λ { read → Gᵈ.Base reading ; write → Gᵈ.Unit ; send → Gᵈ.Unit }
  ; op-grade = opTimeᵈ
  }

specᵈ : LanguageSpec
specᵈ = record { Grades = gradesᵈ ; BTs = baseTypes ; Ops = opsᵈ }

-- the unit is the least element

uᵈ-min : (i : 𝕀ᵣ) → [0, ↑ 0 ] ≾ᵈ i
uᵈ-min [0, ↑ n ] = z≤n
uᵈ-min [0, ∞ ]   = tt

opsᵈ₃ : TypeInference.SolverImpl.Enum.OpEnum specᵈ
opsᵈ₃ = record { ops = read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ ; complete = c }
  where
    c : (op : Op) → op ∈ (read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ)
    c read  = here refl
    c write = there (here refl)
    c send  = there (there (here refl))

module Rwᵈ = TypeInference.Raw.Syntax specᵈ

-- the same demos at the deadline grades, with the unit-minimality
-- option taken and declined

module Gᵐ = TypeInference.SolverImpl.Demo.Generic
              specᵈ opsᵈ₃ (just uᵈ-min) (just uᵈ-min) read Rwᵈ.⋆

module G⁰ = TypeInference.SolverImpl.Demo.Generic
              specᵈ opsᵈ₃ nothing nothing read Rwᵈ.⋆

-- A non-resuming handler clause's effect (the unit) must be below its
-- declared grade `op-grade op ·̂ₑ e''`, `e''` rigid -- derivable only
-- with unit-minimality, by `minₑ`.

module Least where

  module Grᵈ = TypeInference.OpenSyntax.Grades         specᵈ
  module Tyᵈ = TypeInference.OpenSyntax.Types          specᵈ
  module Hyᵈ = TypeInference.OpenSyntax.Hyps           specᵈ
  module Cnᵈ = TypeInference.Constraints.Syntax        specᵈ
  module GIᵈ = GradeSystemInterface                    gradesᵈ

  module Rsᵈ =
    TypeInference.SolverImpl.Restricted specᵈ opsᵈ₃ nothing nothing

  -- the option bears on handler clauses alone: a program without a
  -- handler is inferred the same either way

  ex-unitᵈ : Gᵐ.reportOf Gᵐ.Γ∅ Gᵐ.unit
           ≡ just (scope 0 0 1 ,
                   Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ ,
                   []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-unitᵈ = refl

  -- a handler whose clauses return a constant, run by either solver

  prog : Rwᵈ.RawC 0
  prog = Rwᵈ.handle (Rwᵈ.return Rwᵈ.⋆)
         `with (λ op → Rwᵈ.return Rwᵈ.⋆)
         `in (Rwᵈ.return Rwᵈ.⋆)

  -- without the option, the clause's slack constraint is underivable

  ex-handle-no : G⁰.reportOf G⁰.Γ∅ prog ≡ nothing
  ex-handle-no = refl

  -- with it, the program is reported at the unit effect

  ex-handle-min : Gᵐ.reportOf Gᵐ.Γ∅ prog
                ≡ just (scope 1 0 3 ,
                        Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ ,
                        []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-handle-min = refl

  -- the handled computation may itself perform

  prog' : Rwᵈ.RawC 0
  prog' = Rwᵈ.handle (Rwᵈ.perform read Rwᵈ.⋆ (Rwᵈ.return (Rwᵈ.var zero)))
          `with (λ op → Rwᵈ.return Rwᵈ.⋆)
          `in (Rwᵈ.return Rwᵈ.⋆)

  ex-handle-op : Gᵐ.reportOf Gᵐ.Γ∅ prog'
               ≡ just (scope 2 0 4 ,
                       Tyᵈ.Unit Tyᵈ.‼ Grᵈ.econst (opTimeᵈ read) ,
                       []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-handle-op = refl

  -- Clauses that use their continuation. Each ends in an effect bounded
  -- below by the rigid `e''`, or by the unit, and is inferred once the
  -- unknowns local to the clause are sent to those bounds.

  ex-forward : Gᵐ.reportOf Gᵐ.Γ∅ Gᵐ.forward
             ≡ just (scope 10 0 12 ,
                     Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ ,
                     []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-forward = refl

  ex-unboxing : Gᵐ.reportOf Gᵐ.Γ∅ Gᵐ.unboxing
              ≡ just (scope 4 0 6 ,
                      Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ ,
                      []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-unboxing = refl

  ex-performing : Gᵐ.reportOf Gᵐ.Γ∅ Gᵐ.performing
                ≡ just (scope 1 0 6 ,
                        Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ ,
                        []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-performing = refl

  -- the forwarding clause needs no option: nothing it leaves is about
  -- the unit

  ex-forward-no : G⁰.reportOf G⁰.Γ∅ G⁰.forward
                ≡ just (scope 10 0 12 ,
                        Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ ,
                        []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-forward-no = refl

  -- Resuming twice is refused, as the source system refuses it: the
  -- second resumption uses a continuation that is not eternal across
  -- the lock `∣ e'' ∣` the first one leaves, and the clause's effect
  -- would be `op-grade op · (e'' · e'')`, above `op-grade op · e''`
  -- for every `e''` but the unit.

  ex-resumingTwice : Gᵐ.reportOf Gᵐ.Γ∅ Gᵐ.resumingTwice ≡ nothing
  ex-resumingTwice = refl

  -- With the unit least, an outer unknown bounded by an expression in
  -- the rigid is bounded by it at the unit.

  ex-strip-min : is-just (Gᵐ.solveOn Gᵐ.stripC) ≡ true
  ex-strip-min = refl

  ex-strip-no : G⁰.solveOn G⁰.stripC ≡ nothing
  ex-strip-no = refl

  -- Bounded below by an expression in the rigid, it is bounded by that
  -- expression at the top rigid, with the unit least or not.

  ex-top-min : is-just (Gᵐ.solveOn Gᵐ.topC) ≡ true
  ex-top-min = refl

  ex-top-no : is-just (G⁰.solveOn G⁰.topC) ≡ true
  ex-top-no = refl

  ex-strip-top-min : is-just (Gᵐ.solveOn Gᵐ.stripTopC) ≡ true
  ex-strip-top-min = refl

  ex-strip-top-no : is-just (G⁰.solveOn G⁰.stripTopC) ≡ true
  ex-strip-top-no = refl

  -- A local unknown bounded below by a product with itself has a least
  -- solution, the top, that no finite join reaches; it is left alone,
  -- and the constraint is declined although it is satisfiable.

  ex-cyc-sat : TypeInference.Constraints.Satisfaction._⊨[_]_ specᵈ
                (TypeInference.OpenSyntax.Subst.idˢ specᵈ) Hyᵈ.∅ᴴ Gᵐ.cycC
  ex-cyc-sat = Grᵈ.econst GIᵈ.⊤ₑ , Hyᵈ.topₑ , Hyᵈ.topₑ

  ex-cyc : Gᵐ.solveOn Gᵐ.cycC ≡ nothing
  ex-cyc = refl

  -- Deadlines have a least unit, so a `var`-rule disjunction whose
  -- grade is `[0, ↑ 1 ]` has a refutable grade side.

  disjC : Cnᵈ.Constraint ∅ˢ
  disjC = Cnᵈ.Et∨≾ᵘ Tyᵈ.Unit (Grᵈ.rconst [0, ↑ 1 ])

  disjOf : Maybe (Σ[ Θ ∈ Scope ] List (Tyᵈ.OVType Θ × Grᵈ.RExp Θ))
  disjOf with Rsᵈ.solveOn disjC
  ... | nothing          = nothing
  ... | just (Θ , _ , Q) = just (Θ , Hyᵈ.disj Q)

  -- the solver residualises the disjunction rather than committing to
  -- either side

  ex-disj : disjOf ≡ just (∅ˢ , (Tyᵈ.Unit , Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ)
  ex-disj = refl

  -- The same grade under a type variable: eternality is open, the
  -- grade side is refuted, so reporting settles the disjunction.

  settleC : Cnᵈ.Constraint (∅ˢ +ty)
  settleC = Cnᵈ.Et∨≾ᵘ (Tyᵈ.tvar (newᵗ {∅ˢ})) (Grᵈ.rconst [0, ↑ 1 ])

  -- the solver's disjunctions, then the report's atoms, orderings
  -- and surviving disjunctions

  reportOfᵈ : ∀ {Θ₀} → Cnᵈ.Constraint Θ₀
            → Maybe (Σ[ Θ ∈ Scope ] (List (Tyᵈ.OVType Θ × Grᵈ.RExp Θ)
                                      × List (TyVar Θ)
                                      × List (Grᵈ.RExp Θ × Grᵈ.RExp Θ)
                                      × List (Tyᵈ.OVType Θ × Grᵈ.RExp Θ)))
  reportOfᵈ C with Rsᵈ.reportOn (Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ) C
  ... | nothing = nothing
  ... | just r  = just (Rsᵈ.Reported.Θ' r ,
                        Hyᵈ.disj (Rsᵈ.Reported.Q  r) ,
                        Hyᵈ.ets  (Rsᵈ.Reported.Q̂ r) ,
                        Hyᵈ.ordᵣ (Rsᵈ.Reported.Q̂ r) ,
                        Hyᵈ.disj (Rsᵈ.Reported.Q̂ r))

  -- the solver residualises the disjunction; the report keeps the
  -- eternality atom alone

  ex-settle : reportOfᵈ settleC
            ≡ just (∅ˢ +ty ,
                    (Tyᵈ.tvar (newᵗ {∅ˢ}) , Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ ,
                    newᵗ {∅ˢ} ∷ᴸ []ᴸ , []ᴸ , []ᴸ)
  ex-settle = refl

  -- a met eternality demand is dropped outright

  ex-settle-met : reportOfᵈ disjC
                ≡ just (∅ˢ , (Tyᵈ.Unit , Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ ,
                        []ᴸ , []ᴸ , []ᴸ)
  ex-settle-met = refl

  -- a function type is never eternal, so both sides are refuted here:
  -- the disjunction is decided false, and the constraint refused

  bothC : Cnᵈ.Constraint ∅ˢ
  bothC = Cnᵈ.Et∨≾ᵘ (Tyᵈ.Unit Tyᵈ.⇒ (Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ)) (Grᵈ.rconst [0, ↑ 1 ])

  ex-settle-both : reportOfᵈ bothC ≡ nothing
  ex-settle-both = refl

------------------------------------------------------------------------
-- The library benchmark
--
-- The eight shapes of `Demo.Generic`, each stated twice: the full
-- report and its hypothesis counts by sort.

module Library where

  -- `return ⋆`

  ex-unit-report : reportOf Γ∅ unit
                 ≡ just (scope 0 0 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-unit-report = refl

  ex-unit-size : sizeOf Γ∅ unit ≡ just (0 , 0 , 0 , 0 , 0)
  ex-unit-size = refl

  -- `compose`, reported as
  -- `(α ⇒ β ‼ e₁) ⇒ (β ⇒ γ ‼ e₂) ⇒ (α ⇒ γ ‼ e₁ · e₂) ‼ 0`, with no
  -- qualifier: the lock that the capture of `g` crosses asks
  -- `∣ e₁ ∣ ≾ u`, and the resource unit is the top

  ex-compose-report : reportOf Γ∅ compose
                    ≡ just (scope 34 0 19 ,
                            ((tvar (# 18) ⇒ tvar (# 10) ‼ evar (# 5))
                              ⇒ ((tvar (# 10) ⇒ tvar (# 2) ‼ evar (# 1))
                                  ⇒ (tvar (# 18)
                                      ⇒ tvar (# 2) ‼ (evar (# 5) ·̂ₑ evar (# 1)))
                                    ‼ ûₑ)
                                ‼ ûₑ)
                              ‼ ûₑ ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-compose-report = refl

  ex-compose-size : sizeOf Γ∅ compose ≡ just (0 , 0 , 0 , 0 , 0)
  ex-compose-size = refl

  -- `twice`: the two uses of `f` leave two subtyping atoms, and the
  -- lock's qualifier holds outright, the resource unit being the top

  ex-twice-report : reportOf Γ∅ twice
                  ≡ just (scope 20 0 12 ,
                          ((tvar (# 3) ⇒ tvar (# 4) ‼ evar (# 2))
                            ⇒ (tvar (# 12)
                                ⇒ tvar (# 4) ‼ (evar (# 2) ·̂ₑ evar (# 2)))
                              ‼ ûₑ)
                            ‼ ûₑ ,
                          []ᴸ ,
                          (# 4 , # 3) ∷ᴸ (# 12 , # 3) ∷ᴸ []ᴸ ,
                          []ᴸ , []ᴸ , []ᴸ)
  ex-twice-report = refl

  ex-twice-size : sizeOf Γ∅ twice ≡ just (0 , 2 , 0 , 0 , 0)
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

  -- `keep`: the box grade stays a variable, and the var-rule
  -- disjunction on it holds by its second disjunct, the resource unit
  -- being the top

  ex-keep-report : reportOf Γ∅ keep
                 ≡ just (scope 8 3 3 ,
                         (tvar (# 4) ⇒ [ rvar (# 1) ] tvar (# 4) ‼ ûₑ) ‼ ûₑ ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-keep-report = refl

  ex-keep-size : sizeOf Γ∅ keep ≡ just (0 , 0 , 0 , 0 , 0)
  ex-keep-size = refl

  -- `wrap` is declined: the clause's slack needs unit-minimality,
  -- which these effect grades lack, and the failure is inside `solve`
  -- at the rigid binder

  ex-wrap-report : reportOf Γ∅ wrap ≡ nothing
  ex-wrap-report = refl

  ex-wrap-size : sizeOf Γ∅ wrap ≡ nothing
  ex-wrap-size = refl

  -- Over the deadline grades, whose unit is least, the same shape is
  -- reported, with nothing left over

  module Deadlines where

    module Grᵈ = TypeInference.OpenSyntax.Grades specᵈ
    module Tyᵈ = TypeInference.OpenSyntax.Types  specᵈ

    ex-wrap-reportᵈ : Gᵐ.reportOf Gᵐ.Γ∅ Gᵐ.wrap
                    ≡ just (scope 11 0 8 ,
                            ((Tyᵈ.Unit Tyᵈ.⇒ Tyᵈ.Unit Tyᵈ.‼ Grᵈ.evar (# 1))
                              Tyᵈ.⇒ Tyᵈ.Unit Tyᵈ.‼ Grᵈ.evar (# 1))
                              Tyᵈ.‼ Grᵈ.ûₑ ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
    ex-wrap-reportᵈ = refl

    ex-wrap-sizeᵈ : Gᵐ.sizeOf Gᵐ.Γ∅ Gᵐ.wrap ≡ just (0 , 0 , 0 , 0 , 0)
    ex-wrap-sizeᵈ = refl
