------------------------------------------------------------------
-- The solver at the sensor node's time intervals.                --
--                                                                --
-- `Syntax.Grades.Example.Worked.Spec` grades a computation by a  --
-- two-sided window of elapsed time and a resource by a lower     --
-- bound on it, the projection between them keeping the window's  --
-- lower endpoint. It satisfies the solver's three assumptions,   --
-- but not the optional one that the effect unit is least.        --
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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_; z≤n; s≤s)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩; _≾ₒ_)
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_,_]; min; max; _≾ᵢ_; _≤∞?_)
open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (spec; baseTypes; reading)

open import Syntax.Grades.Example.Time.RightSided
  using (𝕀ᵣ; [0,_]; ↑_; ∞; right-sided-intervals) renaming (_≾ₒ_ to _≾ᵈ_)
open import Syntax.Grades.Example.System.Identity using (identityGradeSystem)

import Syntax.GroundTypes
import Syntax.Contexts
import Syntax.Types

import TypeInference.OpenSyntax.Grades
import TypeInference.OpenSyntax.Types
import TypeInference.OpenSyntax.Contexts
import TypeInference.OpenSyntax.Hyps
import TypeInference.Raw.Syntax
import TypeInference.Constraints.Syntax
import TypeInference.SolverImpl.Enum
import TypeInference.SolverImpl.Restricted
import TypeInference.SolverImpl.Demo.Generic

open import TypeInference.Scopes

module TypeInference.SolverImpl.Demo.TimeIntervals where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

import Syntax.Types spec as T

open import Syntax.Contexts spec using (Ctx; []; _∷_; _⟨_⟩)

open import TypeInference.OpenSyntax.Grades         spec
open import TypeInference.OpenSyntax.Types          spec
open import TypeInference.OpenSyntax.ClosedContexts spec using (skel)

open import TypeInference.Raw.Syntax spec

open import TypeInference.SolverImpl.Enum spec using (OpEnum)

------------------------------------------------------------------------
-- 1. Setup
--
-- The solver is parametric in the two decidable orders, in an
-- enumeration of the operations, and in the two optional proofs that a
-- unit is least. Instantiating it here, and `Demo.Generic` with it,
-- fixes the wrappers the rest of the module runs: `infer!`, reporting
-- an inferred type and effect, and `typeOf`, running the whole pipeline
-- down to a derivation of the source system.

-- resource grades are lower bounds, ordered by `_≤_` reversed

≾ᵣ-dec : (i j : 𝕀) → Dec (i ≾ₒ j)
≾ᵣ-dec [ m ,+∞⟩ [ n ,+∞⟩ = n ≤? m

-- effect grades are two-sided intervals, ordered by containment

≾ₑ-dec : (i j : Interval∞) → Dec (i ≾ᵢ j)
≾ₑ-dec i j with min j ≤? min i | max i ≤∞? max j
... | yes p | yes q = yes (p , q)
... | yes p | no ¬q = no λ r → ¬q (proj₂ r)
... | no ¬p | _     = no λ r → ¬p (proj₁ r)

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
             spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing read ⋆

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

-- a base-typed constant, at the node's one base type

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

-- a `let`: the two effects are multiplied

ex-seq : infer! [] (return true ⨟ return (var zero))
       ≡ just (Bool , ûₑ)
ex-seq = refl

-- a boolean elimination

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
-- and the effect is its execution window, multiplied by the
-- continuation's

ex-perform : infer! [] (perform read ⋆ (return (var zero)))
           ≡ just (Base reading , econst (op-grade read))
ex-perform = refl

-- delaying: the declared duration is charged to the effect

ex-delay : infer! [] (delay 2 (return ⋆))
         ≡ just (Unit , econst (of-natᵉ 2))
ex-delay = refl

-- boxing: the box's grade is not annotated, and defaults to the unit

ex-box : infer! [] (box ⋆ (return (var zero)))
       ≡ just ([ ûᵣ ] Unit , ûₑ)
ex-box = refl

-- unboxing a boxed variable, at the unit grade, which demands nothing

ex-unbox : infer! ([] ∷ (T.[ uᵣ ] T.Bool)) (unbox zero (return (var zero)))
         ≡ just (Bool , ûₑ)
ex-unbox = refl

-- `handle` is refused at these grades: a clause that does not resume
-- runs in the unit effect, which these windows do not put below an
-- operation's. Section 5 runs the same program over grades whose unit
-- is least.

ex-handle : infer! [] (handle (return ⋆) `with (λ op → return ⋆) `in (return ⋆))
          ≡ nothing
ex-handle = refl

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

ex-branch-ops : infer! [] branch-ops ≡ just (Unit , econst [ 1 , ↑ 3 , s≤s z≤n ])
ex-branch-ops = refl

-- An arm that returns instead contributes the unit window, so the
-- containing window reaches down to `0`.

branch-ret : RawC 0
branch-ret = if true `then perform read ⋆ (return ⋆) `else return ⋆

ex-branch-ret : infer! [] branch-ret ≡ just (Unit , econst [ 0 , ↑ 1 , z≤n ])
ex-branch-ret = refl

-- Two delays: `delay n` contributes `of-natᵉ n`, and the join spans
-- both durations.

branch-delay : RawC 0
branch-delay = if true `then delay 2 (return ⋆) `else delay 1 (return ⋆)

ex-branch-delay : infer! [] branch-delay
                ≡ just (Unit , econst [ 1 , ↑ 2 , s≤s z≤n ])
ex-branch-delay = refl

-- Nesting a branch inside a branch puts three bounds on one effect
-- unknown, and the window spans all three durations.
-- `notes/ThreeArmBranch.agda` derives the same grade declaratively.

branch-delay³ : RawC 0
branch-delay³ = if true `then delay 1 (return ⋆)
                        `else (if true `then delay 2 (return ⋆)
                                       `else delay 3 (return ⋆))

ex-branch-delay³ : infer! [] branch-delay³
                 ≡ just (Unit , econst [ 1 , ↑ 3 , s≤s z≤n ])
ex-branch-delay³ = refl

-- an arm that returns contributes the unit window here too

branch-delay³-ret : RawC 0
branch-delay³-ret = if true `then return ⋆
                            `else (if true `then delay 2 (return ⋆)
                                           `else delay 3 (return ⋆))

ex-branch-delay³-ret : infer! [] branch-delay³-ret
                     ≡ just (Unit , econst [ 0 , ↑ 3 , z≤n ])
ex-branch-delay³-ret = refl

-- A resource boxed at `[ 2 ,+∞⟩` becomes available only once two ticks
-- stand between the binder and the `unbox`: that is the premise
-- `ρ' ≾ᵣ ρ₀` of the `unbox` rule, `ρ'` being the product of the locks
-- to the variable's right, which the term itself determines.

Γ₂ : Ctx
Γ₂ = [] ∷ (T.[ [ 2 ,+∞⟩ ] T.Bool)

-- a `write` elapses, and `mapᵉ [ 2 , 3 ] = [ 2 ,+∞⟩` meets the demand

unbox-after-write : RawC (skel Γ₂)
unbox-after-write =
  perform write (const reading 0) (unbox (suc zero) (return (var zero)))

ex-unbox-after-write : infer! Γ₂ unbox-after-write
                     ≡ just (Bool , econst (op-grade write))
ex-unbox-after-write = refl

-- and the derivation of the source system that the pipeline builds
-- says the same

ex-unbox-after-write-pipeline : typeOf (inferImpl Γ₂ unbox-after-write)
                              ≡ just (T.Bool , op-grade write ·ₑ uₑ)
ex-unbox-after-write-pipeline = refl

-- a `read` licenses only `[ 1 ,+∞⟩`, which does not, and `ex-≾ᵣ-not-up`
-- is the whole of the reason: no derivation can choose another `ρ'`

unbox-after-read : RawC (skel Γ₂)
unbox-after-read =
  perform read ⋆ (unbox (suc zero) (return (var zero)))

ex-unbox-after-read : infer! Γ₂ unbox-after-read ≡ nothing
ex-unbox-after-read = refl

-- idling meets the demand just as an operation does

unbox-after-delay : RawC (skel Γ₂)
unbox-after-delay = delay 2 (unbox zero (return (var zero)))

ex-unbox-after-delay : infer! Γ₂ unbox-after-delay
                     ≡ just (Bool , econst (of-natᵉ 2))
ex-unbox-after-delay = refl

-- one tick short, and it does not

unbox-too-soon : RawC (skel Γ₂)
unbox-too-soon = delay 1 (unbox zero (return (var zero)))

ex-unbox-too-soon : infer! Γ₂ unbox-too-soon ≡ nothing
ex-unbox-too-soon = refl

------------------------------------------------------------------------
-- 4. What the solver does
--
-- The passes, each on a program that isolates it: lower bounds on an
-- unknown folded by join, an unknown bounded only from above sent to
-- that bound, unconstrained unknowns defaulted by polarity, and an
-- unknown escaping a rigid binder refuted.

-- The slack pass. Both arms bound the branch's effect unknown from
-- below and the closer folds the two bounds into their join, which
-- the sequencing then multiplies by the unit.

fold-then-mul : RawC 0
fold-then-mul = branch-delay ⨟ return ⋆

ex-fold-then-mul : infer! [] fold-then-mul
                 ≡ just (Unit , econst [ 1 , ↑ 2 , s≤s z≤n ])
ex-fold-then-mul = refl

-- The fold declines a bound that does not combine rather than dropping
-- it, so an unknown whose bounds still hold an arm's own slack variable
-- is left to the round that follows, by which point they are constants.
-- Three arms at one duration therefore land on a single constant, not
-- on a product with one arm's slack.

branch-delay³-flat : RawC 0
branch-delay³-flat = if true `then delay 1 (return ⋆)
                             `else (if true `then delay 1 (return ⋆)
                                            `else delay 1 (return ⋆))

ex-branch-delay³-flat : infer! [] branch-delay³-flat
                      ≡ just (Unit , econst [ 1 , ↑ 1 , s≤s z≤n ])
ex-branch-delay³-flat = refl

-- The slack variable of a sequencing's first component is resolved
-- before the composite effect is built.

ex-seq-op : infer! [] (perform read ⋆ (return (var zero)) ⨟ return ⋆)
          ≡ just (Unit , econst (op-grade read))
ex-seq-op = refl

-- The tightening pass. Subtyping is contravariant in a box's grade, so
-- the result type's fresh grade variable is bounded above by the
-- annotation and never below: tightening sends it there, and the grade
-- is reported rather than coarsened to the unit.

ex-box-grade : infer! ([] ∷ (T.[ [ 1 ,+∞⟩ ] T.Bool)) (return (var zero))
             ≡ just ([ rconst [ 1 ,+∞⟩ ] Bool , ûₑ)
ex-box-grade = refl

-- both arms of a conditional bound that one variable above, by the
-- same expression, which is therefore its own cap

ex-box-branch : infer! ([] ∷ T.Bool ∷ (T.[ [ 1 ,+∞⟩ ] T.Bool))
                  (if var (suc zero)
                    `then return (var zero)
                    `else return (var zero))
              ≡ just ([ rconst [ 1 ,+∞⟩ ] Bool , ûₑ)
ex-box-branch = refl

-- Polarity defaults. The identity function constrains its argument
-- type from neither side, so it is defaulted, and the latent effect
-- stays slack.

ex-default : infer! [] (return (lam (return (var zero))))
           ≡ just (Unit ⇒ (Unit ‼ ûₑ) , ûₑ)
ex-default = refl

-- The unknowns of every nesting level live in one store, so nesting
-- costs the solver nothing.

ex-lam² : infer! [] (return (lam (return (lam (return true)))))
        ≡ just (Unit ⇒ ((Unit ⇒ (Bool ‼ ûₑ)) ‼ ûₑ) , ûₑ)
ex-lam² = refl

ex-lam³ : infer! [] (return (lam (return (lam (return (lam (return true)))))))
        ≡ just (Unit ⇒ ((Unit ⇒ ((Unit ⇒ (Bool ‼ ûₑ)) ‼ ûₑ)) ‼ ûₑ) , ûₑ)
ex-lam³ = refl

ex-lam⁴ : infer! [] (return (lam (return (lam (return (lam (return (lam (return true)))))))))
        ≡ just (Unit ⇒ ((Unit ⇒ ((Unit ⇒ ((Unit ⇒ (Bool ‼ ûₑ)) ‼ ûₑ)) ‼ ûₑ)) ‼ ûₑ) , ûₑ)
ex-lam⁴ = refl

-- The escape check, on the two binder orders of `Demo.Generic`.

ex-escape : solved? (gsolveImpl escC) ≡ nothing
ex-escape = refl

ex-escape-ok : solved? (gsolveImpl okC) ≡ just tt
ex-escape-ok = refl

-- The pipeline, end to end.

ex-pipeline : typeOf (inferImpl [] (return true)) ≡ just (T.Bool , uₑ)
ex-pipeline = refl

ex-pipeline-op : typeOf (inferImpl [] (perform read ⋆ (return (var zero))))
               ≡ just (T.Base reading , op-grade read ·ₑ uₑ)
ex-pipeline-op = refl

-- The solver is principal on every constraint: a program the solver
-- accepts has a principal type.

module Unguarded where

  module OC = TypeInference.OpenSyntax.Contexts spec

  open import TypeInference.Principality            spec using (Principal; C[_,_])
  open import TypeInference.Principality.Restricted spec using (principal-on)
  open import TypeInference.SolverImpl.Restricted   spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing
    using (solveOn; solverImplOn)

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

-- the order is decidable, and the unit is its least element

≾ᵈ-dec : (i j : 𝕀ᵣ) → Dec (i ≾ᵈ j)
≾ᵈ-dec [0, m ] [0, n ] = m ≤∞? n

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
              specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ (just uᵈ-min) (just uᵈ-min) read Rwᵈ.⋆

module G⁰ = TypeInference.SolverImpl.Demo.Generic
              specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ nothing nothing read Rwᵈ.⋆

-- A non-resuming handler clause's effect (the unit) must be below its
-- declared grade `op-grade op ·̂ₑ e''`, `e''` rigid -- derivable only
-- with unit-minimality, by `minₑ`.

module Least where

  module Cᵈ  = Syntax.Contexts               specᵈ
  module Tᵈ  = Syntax.Types                  specᵈ
  module Grᵈ = TypeInference.OpenSyntax.Grades         specᵈ
  module Tyᵈ = TypeInference.OpenSyntax.Types          specᵈ
  module Hyᵈ = TypeInference.OpenSyntax.Hyps           specᵈ
  module Cnᵈ = TypeInference.Constraints.Syntax        specᵈ

  module Rsᵈ =
    TypeInference.SolverImpl.Restricted specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ nothing nothing

  -- the option bears on handler clauses alone: a program without a
  -- handler is inferred the same either way

  ex-unitᵈ : Gᵐ.infer! Cᵈ.[] Gᵐ.unit ≡ just (Tyᵈ.Unit , Grᵈ.ûₑ)
  ex-unitᵈ = refl

  -- a handler whose clauses return a constant, run by either solver

  prog : Rwᵈ.RawC 0
  prog = Rwᵈ.handle (Rwᵈ.return Rwᵈ.⋆)
         `with (λ op → Rwᵈ.return Rwᵈ.⋆)
         `in (Rwᵈ.return Rwᵈ.⋆)

  -- without the option, the clause's slack constraint is underivable

  ex-handle-no : G⁰.infer! Cᵈ.[] prog ≡ nothing
  ex-handle-no = refl

  -- with it, the whole program is solved, and both slacks stay unit

  ex-handle-min : Gᵐ.infer! Cᵈ.[] prog
                ≡ just (Tyᵈ.Unit , Grᵈ.ûₑ)
  ex-handle-min = refl

  -- the handled computation may itself perform

  prog' : Rwᵈ.RawC 0
  prog' = Rwᵈ.handle (Rwᵈ.perform read Rwᵈ.⋆ (Rwᵈ.return (Rwᵈ.var zero)))
          `with (λ op → Rwᵈ.return Rwᵈ.⋆)
          `in (Rwᵈ.return Rwᵈ.⋆)

  ex-handle-op : Gᵐ.infer! Cᵈ.[] prog'
               ≡ just (Tyᵈ.Unit , Grᵈ.econst (opTimeᵈ read))
  ex-handle-op = refl

  -- end to end: the same program elaborated into the source system,
  -- its grounded derivation reading the clause's slack off `minₑ`

  ex-handle-pipeline : Gᵐ.typeOf (Gᵐ.inferImpl Cᵈ.[] prog)
                     ≡ just (Tᵈ.Unit , [0, ↑ 0 ])
  ex-handle-pipeline = refl

  -- Deadlines have a least unit, so a `var`-rule disjunction whose
  -- grade is `[0, ↑ 1 ]` has a refutable grade side.

  disjC : Cnᵈ.Constraint ∅ˢ
  disjC = Cnᵈ.Et∨≾ᵘ Tyᵈ.Unit (Grᵈ.rconst [0, ↑ 1 ])

  disjOf : Maybe (Σ[ Θ ∈ Scope ] List (Tyᵈ.OVType Θ × Grᵈ.RExp Θ))
  disjOf with Rsᵈ.solveOn disjC
  ... | nothing          = nothing
  ... | just (Θ , _ , Q) = just (Θ , Hyᵈ.disj Q)

  -- the open solver residualises the disjunction rather than committing
  -- to either side

  ex-disj : disjOf ≡ just (∅ˢ , (Tyᵈ.Unit , Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ)
  ex-disj = refl

  -- the ground path closes it by the eternality side, the grade side
  -- being false

  ex-disj-close : G⁰.solved? (G⁰.gsolveImpl disjC) ≡ just tt
  ex-disj-close = refl

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
  -- settling leaves the false ordering rather than hiding it

  bothC : Cnᵈ.Constraint ∅ˢ
  bothC = Cnᵈ.Et∨≾ᵘ (Tyᵈ.Unit Tyᵈ.⇒ (Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ)) (Grᵈ.rconst [0, ↑ 1 ])

  ex-settle-both : reportOfᵈ bothC
                 ≡ just (∅ˢ ,
                         (Tyᵈ.Unit Tyᵈ.⇒ (Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ) ,
                          Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ ,
                         []ᴸ , (Grᵈ.rconst [0, ↑ 1 ] , Grᵈ.ûᵣ) ∷ᴸ []ᴸ , []ᴸ)
  ex-settle-both = refl

------------------------------------------------------------------------
-- The library benchmark
--
-- The eight shapes of `Demo.Generic` go through `reportOn`, the open
-- path, which hands back a qualified type rather than a ground
-- solution. Each is stated twice, the full report and its hypothesis
-- counts by sort.

module Library where

  -- `return ⋆`

  ex-unit-report : reportOf unit
                 ≡ just (scope 0 0 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-unit-report = refl

  ex-unit-size : sizeOf unit ≡ just (0 , 0 , 0 , 0 , 0)
  ex-unit-size = refl

  -- `compose`, reported as
  -- `(α ⇒ β ‼ e₁) ⇒ (β ⇒ γ ‼ e₂) ⇒ (α ⇒ γ ‼ e₁ · e₂) ‼ 0`, with one
  -- qualifier: the lock that the capture of `g` crosses

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

  -- `wrap` is declined: the clause's slack needs unit-minimality,
  -- which these effect grades lack, and the failure is inside `solve`
  -- at the rigid binder

  ex-wrap-report : reportOf wrap ≡ nothing
  ex-wrap-report = refl

  ex-wrap-size : sizeOf wrap ≡ nothing
  ex-wrap-size = refl

  -- Over the deadline grades, whose unit is least, the same shape is
  -- reported, with nothing left over

  module Deadlines where

    module Grᵈ = TypeInference.OpenSyntax.Grades specᵈ
    module Tyᵈ = TypeInference.OpenSyntax.Types  specᵈ

    ex-wrap-reportᵈ : Gᵐ.reportOf Gᵐ.wrap
                    ≡ just (scope 11 0 8 ,
                            ((Tyᵈ.Unit Tyᵈ.⇒ Tyᵈ.Unit Tyᵈ.‼ Grᵈ.evar (# 1))
                              Tyᵈ.⇒ Tyᵈ.Unit Tyᵈ.‼ Grᵈ.evar (# 1))
                              Tyᵈ.‼ Grᵈ.ûₑ ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
    ex-wrap-reportᵈ = refl

    ex-wrap-sizeᵈ : Gᵐ.sizeOf Gᵐ.wrap ≡ just (0 , 0 , 0 , 0 , 0)
    ex-wrap-sizeᵈ = refl
