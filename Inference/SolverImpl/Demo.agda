------------------------------------------------------------------
-- The solver, run                                                --
--                                                                --
-- `Inference.SolverImpl` is parameterised by assumptions no       --
-- `LanguageSpec` supplies: decidability of the two grade orders   --
-- and an enumeration of the operation symbols. The sensor-node    --
-- specification of `Syntax.Grades.Example.Worked.Spec` satisfies  --
-- all three — its grades are time intervals, ordered by `_≤_` on  --
-- their endpoints, and it has three operations — so the solver    --
-- can be instantiated and run.                                    --
--                                                                --
-- Each example below is discharged by `refl`, so what the solver  --
-- infers is checked by computation, not asserted.                 --
--                                                                --
-- A second specification follows at the end — deadlines, whose    --
-- unit IS the least grade — to exercise the solver's optional     --
-- unit-minimality: the same handler is rejected without it and    --
-- inferred with it.                                               --
------------------------------------------------------------------

open import Data.List.Base using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_; z≤n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩; _≾ₒ_)
open import Syntax.Grades.Example.Time.TwoSided  using (Interval; min; max; _≾ᵢ_)
open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (spec; baseTypes; BT; reading)

open import Syntax.Grades.Example.Time.RightSided
  using (𝕀ᵣ; [0,_]; right-sided-intervals) renaming (_≾ₒ_ to _≾ᵈ_)
open import Syntax.Grades.Example.System.Identity using (identityGradeSystem)

-- the modules below are also applied to a second specification, at the
-- end of this module

import Syntax.GroundTypes
import Syntax.Contexts
import Syntax.Types

import Inference.Open.Grades
import Inference.Open.Types
import Inference.Open.Subst
import Inference.Open.Contexts
import Inference.Open.ClosedContexts
import Inference.Raw.Syntax
import Inference.Infer
import Inference.SolverImpl
import Inference.SolverImpl.Enum

open import Inference.Scopes

module Inference.SolverImpl.Demo where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

import Syntax.Types spec as T

open import Syntax.Contexts spec using (Ctx; []; _∷_; _⟨_⟩)

open import Inference.Open.Grades      spec
open import Inference.Open.Types       spec
open import Inference.Open.Subst       spec
open import Inference.Open.Hyps        spec
open import Inference.Open.ClosedContexts spec using (skel)

open import Inference.Raw.Syntax spec

open import Inference.Constraints.Syntax       spec
open import Inference.Constraints.Satisfaction spec

open import Inference.Infer spec using (Θ₁; X̂₁; t̂₁; C∅[_,_]; Inferred)

open import Inference.SolverImpl.Enum spec using (OpEnum)

--------------------------------------------------------------
-- The three assumptions, for this specification             --
--------------------------------------------------------------

-- resource grades are lower bounds, ordered by `_≤_` reversed

≾ᵣ-dec : (i j : 𝕀) → Dec (i ≾ₒ j)
≾ᵣ-dec [ m ,+∞⟩ [ n ,+∞⟩ = n ≤? m

-- effect grades are two-sided intervals, ordered by containment

≾ₑ-dec : (i j : Interval) → Dec (i ≾ᵢ j)
≾ₑ-dec i j with min j ≤? min i | max i ≤? max j
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

open import Inference.SolverImpl spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing

--------------------------------------------------------------
-- Reading the inferred type and effect off a solution       --
--------------------------------------------------------------

result : {X : Subst Θ₁ ∅ˢ → Set} → Maybe (Σ[ σ ∈ Subst Θ₁ ∅ˢ ] X σ)
       → Maybe (OVType ∅ˢ × EExp ∅ˢ)
result nothing        = nothing
result (just (σ , _)) = just (X̂₁ [ σ ]ᵛ , t̂₁ [ σ ]ᵉ)

infer! : (Γ : Ctx) → (M : RawC (skel Γ)) → Maybe (OVType ∅ˢ × EExp ∅ˢ)
infer! Γ M = result (gsolveImpl C∅[ Γ , M ])

--------------------------------------------------------------
-- Examples                                                  --
--------------------------------------------------------------

-- returning the unit value

ex-unit : infer! [] (return ⋆) ≡ just (Unit , ûₑ)
ex-unit = refl

-- returning a boolean: the result type is read off the constraint,
-- not defaulted

ex-bool : infer! [] (return true) ≡ just (Bool , ûₑ)
ex-bool = refl

-- a variable's type is looked up

ex-var : infer! ([] ∷ T.Bool) (return (var zero)) ≡ just (Bool , ûₑ)
ex-var = refl

-- a pair

ex-pair : infer! [] (return ⦉ ⋆ , true ⦊) ≡ just (Unit |×| Bool , ûₑ)
ex-pair = refl

-- a lambda: none of `α₁ ⇒ (α₂ ‼ e)` is fixed in advance, so the
-- argument type is defaulted and the latent effect is slack

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
       ≡ just (Bool , ûₑ ·̂ₑ ûₑ)
ex-seq = refl

-- a boolean elimination

ex-if : infer! [] (if true `then return ⋆ `else return ⋆)
      ≡ just (Unit , ûₑ)
ex-if = refl

-- performing an operation: the result type is the operation's arity
-- and the effect is its duration, multiplied by the continuation's

ex-perform : infer! [] (perform read ⋆ (return (var zero)))
           ≡ just (Base reading , econst (op-grade read) ·̂ₑ ûₑ)
ex-perform = refl

-- nested lambdas: the unknowns of every level are shared in one
-- store, so nesting costs the solver nothing

ex-lam² : infer! [] (return (lam (return (lam (return true)))))
        ≡ just (Unit ⇒ ((Unit ⇒ (Bool ‼ ûₑ)) ‼ ûₑ) , ûₑ)
ex-lam² = refl

ex-lam³ : infer! [] (return (lam (return (lam (return (lam (return true)))))))
        ≡ just (Unit ⇒ ((Unit ⇒ ((Unit ⇒ (Bool ‼ ûₑ)) ‼ ûₑ)) ‼ ûₑ) , ûₑ)
ex-lam³ = refl

ex-lam⁴ : infer! [] (return (lam (return (lam (return (lam (return (lam (return true)))))))))
        ≡ just (Unit ⇒ ((Unit ⇒ ((Unit ⇒ ((Unit ⇒ (Bool ‼ ûₑ)) ‼ ûₑ)) ‼ ûₑ)) ‼ ûₑ) , ûₑ)
ex-lam⁴ = refl

-- delaying: the declared duration is charged to the effect

ex-delay : infer! [] (delay 2 (return ⋆))
         ≡ just (Unit , econst (of-natᵉ 2) ·̂ₑ ûₑ)
ex-delay = refl

-- boxing: the box's grade is not annotated, and defaults to the unit

ex-box : infer! [] (box ⋆ (return (var zero)))
       ≡ just ([ ûᵣ ] Unit , ûₑ)
ex-box = refl

-- pattern-matching a pair

ex-match : infer! [] (match ⦉ ⋆ , true ⦊ `in return (var zero))
         ≡ just (Bool , ûₑ)
ex-match = refl

-- an operation inside a sequencing: the slack variable of the first
-- component is resolved before the composite effect is built

ex-seq-op : infer! [] (perform read ⋆ (return (var zero)) ⨟ return ⋆)
          ≡ just (Unit , (econst (op-grade read) ·̂ₑ ûₑ) ·̂ₑ ûₑ)
ex-seq-op = refl

-- unboxing a boxed variable

ex-unbox : infer! ([] ∷ (T.[ uᵣ ] T.Bool)) (unbox zero (return (var zero)))
         ≡ just (Bool , ûₑ)
ex-unbox = refl

-- what the solver cannot do here: a handler clause is typed under a
-- RIGID effect variable `e''`, and its slack constraint
-- `ûₑ ≾̂ₑᶜ (g ·̂ₑ e'')` is derivable only by `minₑ`, whose premise fails
-- for these grades — `[ 0 , 0 ]` is contained in `[ m , n ]` only when
-- `m` is `0`. The option is therefore `nothing` above, `handle` is
-- rejected, and this is checked, not asserted. The section at the end
-- of this module runs the same program over grades that do have a
-- least unit

ex-handle : infer! [] (handle (return ⋆) `with (λ op → return ⋆) `in (return ⋆))
          ≡ nothing
ex-handle = refl

--------------------------------------------------------------
-- The whole pipeline                                        --
--                                                           --
-- `inferImpl` runs the solution through `soundC` and         --
-- `groundC`, so what comes back is a typing derivation of    --
-- the ORIGINAL system, with its type and effect as fields.   --
--------------------------------------------------------------

typeOf : {Γ : Ctx} {M : RawC (skel Γ)} → Maybe (Inferred Γ M) → Maybe (T.VType × E)
typeOf nothing  = nothing
typeOf (just I) = just (Inferred.A I , Inferred.ε I)

ex-pipeline : typeOf (inferImpl [] (return true)) ≡ just (T.Bool , uₑ)
ex-pipeline = refl

ex-pipeline-op : typeOf (inferImpl [] (perform read ⋆ (return (var zero))))
               ≡ just (T.Base reading , op-grade read ·ₑ uₑ)
ex-pipeline-op = refl

--------------------------------------------------------------
-- A specification whose unit is the least grade             --
--                                                           --
-- Right-sided intervals are deadlines `[0, n ]`, ordered by  --
-- `_≤_` on the endpoint, so `[0, 0 ]` is below every grade.  --
-- Both components of the grade system are that monoid, over  --
-- the same sensor node: each operation is charged its worst  --
-- case.                                                      --
--------------------------------------------------------------

gradesᵈ : GradeSystem
gradesᵈ = identityGradeSystem right-sided-intervals

module Gᵈ = Syntax.GroundTypes gradesᵈ baseTypes

opTimeᵈ : Op → 𝕀ᵣ
opTimeᵈ read  = [0, 1 ]
opTimeᵈ write = [0, 3 ]
opTimeᵈ send  = [0, 6 ]

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
≾ᵈ-dec [0, m ] [0, n ] = m ≤? n

uᵈ-min : (i : 𝕀ᵣ) → [0, 0 ] ≾ᵈ i
uᵈ-min [0, n ] = z≤n

opsᵈ₃ : Inference.SolverImpl.Enum.OpEnum specᵈ
opsᵈ₃ = record { ops = read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ ; complete = c }
  where
    c : (op : Op) → op ∈ (read ∷ᴸ write ∷ᴸ send ∷ᴸ []ᴸ)
    c read  = here refl
    c write = there (here refl)
    c send  = there (there (here refl))

--------------------------------------------------------------
-- Handlers, accommodated                                    --
--                                                           --
-- A handler clause that does not resume the continuation has --
-- the unit as its effect, and must be below the clause's     --
-- declared grade `op-grade op ·̂ₑ e''`, whose `e''` is rigid. --
-- Nothing derives that without unit-minimality; with it,     --
-- `minₑ` does. The two instantiations below differ only in   --
-- whether the option is supplied.                            --
--------------------------------------------------------------

module Least where

  module Cᵈ  = Syntax.Contexts               specᵈ
  module Tᵈ  = Syntax.Types                  specᵈ
  module Grᵈ = Inference.Open.Grades         specᵈ
  module Tyᵈ = Inference.Open.Types          specᵈ
  module Sbᵈ = Inference.Open.Subst          specᵈ
  module CCᵈ = Inference.Open.ClosedContexts specᵈ
  module Rwᵈ = Inference.Raw.Syntax          specᵈ
  module Inᵈ = Inference.Infer               specᵈ

  -- with the option, and without it

  module Sᵐ = Inference.SolverImpl specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ (just uᵈ-min) (just uᵈ-min)
  module S⁰ = Inference.SolverImpl specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ nothing       nothing

  resultᵈ : {X : Sbᵈ.Subst Inᵈ.Θ₁ ∅ˢ → Set}
          → Maybe (Σ[ σ ∈ Sbᵈ.Subst Inᵈ.Θ₁ ∅ˢ ] X σ)
          → Maybe (Tyᵈ.OVType ∅ˢ × Grᵈ.EExp ∅ˢ)
  resultᵈ nothing        = nothing
  resultᵈ (just (σ , _)) = just (Inᵈ.X̂₁ Sbᵈ.[ σ ]ᵛ , Inᵈ.t̂₁ Sbᵈ.[ σ ]ᵉ)

  -- the option changes nothing about the rest: a program without a
  -- handler is inferred as before

  ex-unitᵈ : resultᵈ (Sᵐ.gsolveImpl Inᵈ.C∅[ Cᵈ.[] , Rwᵈ.return Rwᵈ.⋆ ])
           ≡ just (Tyᵈ.Unit , Grᵈ.ûₑ)
  ex-unitᵈ = refl

  -- a handler whose clauses return a constant, run by either solver

  prog : Rwᵈ.RawC 0
  prog = Rwᵈ.handle (Rwᵈ.return Rwᵈ.⋆)
         `with (λ op → Rwᵈ.return Rwᵈ.⋆)
         `in (Rwᵈ.return Rwᵈ.⋆)

  -- without the option, the clause's slack constraint is underivable

  ex-handle-no : resultᵈ (S⁰.gsolveImpl Inᵈ.C∅[ Cᵈ.[] , prog ]) ≡ nothing
  ex-handle-no = refl

  -- with it, the whole program is solved, and both slacks stay unit

  ex-handle-min : resultᵈ (Sᵐ.gsolveImpl Inᵈ.C∅[ Cᵈ.[] , prog ])
                ≡ just (Tyᵈ.Unit , Grᵈ.ûₑ Grᵈ.·̂ₑ Grᵈ.ûₑ)
  ex-handle-min = refl

  -- the handled computation may itself perform

  prog' : Rwᵈ.RawC 0
  prog' = Rwᵈ.handle (Rwᵈ.perform read Rwᵈ.⋆ (Rwᵈ.return (Rwᵈ.var zero)))
          `with (λ op → Rwᵈ.return Rwᵈ.⋆)
          `in (Rwᵈ.return Rwᵈ.⋆)

  ex-handle-op : resultᵈ (Sᵐ.gsolveImpl Inᵈ.C∅[ Cᵈ.[] , prog' ])
               ≡ just (Tyᵈ.Unit , (Grᵈ.econst (opTimeᵈ read) Grᵈ.·̂ₑ Grᵈ.ûₑ) Grᵈ.·̂ₑ Grᵈ.ûₑ)
  ex-handle-op = refl

  -- end to end: the same program elaborated into the ORIGINAL system,
  -- its grounded derivation reading the clause's slack off `minₑ`

  typeOfᵈ : {Γ : Cᵈ.Ctx} {M : Rwᵈ.RawC (CCᵈ.skel Γ)}
          → Maybe (Inᵈ.Inferred Γ M) → Maybe (Tᵈ.VType × 𝕀ᵣ)
  typeOfᵈ nothing  = nothing
  typeOfᵈ (just I) = just (Inᵈ.Inferred.A I , Inᵈ.Inferred.ε I)

  ex-handle-pipeline : typeOfᵈ (Sᵐ.inferImpl Cᵈ.[] prog) ≡ just (Tᵈ.Unit , [0, 0 ])
  ex-handle-pipeline = refl

--------------------------------------------------------------
-- The fragment, and a principal typing                      --
--                                                           --
-- The solver is principal on `Frag`: the constraints whose   --
-- `var`-rule disjunctions carry a lock grade convertible to  --
-- the unit, where the solver's bias towards the grade         --
-- disjunct costs nothing. Membership is decided by            --
-- computation, and a program in the fragment that the solver  --
-- accepts has a principal typing in Pretnar's sense.          --
--------------------------------------------------------------

module Fragment where

  module OC = Inference.Open.Contexts spec

  open import Inference.Principality            spec using (Principal; C[_,_])
  open import Inference.Principality.Restricted spec using (principal-on)
  open import Inference.Solver.Fragment         spec using (Frag; frag?)
  open import Inference.SolverImpl.Restricted   spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing
    using (solveOn; solverImplOn)

  Γ∅ : OC.OCtx ∅ˢ 0
  Γ∅ = OC.[]

  -- `return true` uses no variable, so it raises no disjunction at
  -- all: it is in the fragment, and the check is a computation

  prog-true : RawC 0
  prog-true = return true

  frag-true : Σ[ p ∈ Frag C[ Γ∅ , prog-true ] ]
                (frag? ops₃ C[ Γ∅ , prog-true ] ≡ just p)
  frag-true = _ , refl

  -- a program in the fragment that the solver accepts has a
  -- principal solution-with-residue, and hence a principal typing

  principal? : ∀ {n} → (Γ : OC.OCtx ∅ˢ n) → (M : RawC n) → Frag C[ Γ , M ]
             → Maybe (Principal Γ M)
  principal? Γ M fr with solveOn C[ Γ , M ] in e
  ... | nothing           = nothing
  ... | just (Θ' , σ , Q) = just (principal-on solverImplOn Γ M fr e)

  ex-principal : Σ[ p ∈ Principal Γ∅ prog-true ]
                   (principal? Γ∅ prog-true (proj₁ frag-true) ≡ just p)
  ex-principal = _ , refl
