------------------------------------------------------------------
-- Runs the solver against `Syntax.Grades.Example.Worked.Spec`, a --
-- sensor-node specification satisfying its three assumptions.    --
-- Every example is discharged by `refl`, so what is inferred is  --
-- checked by computation, not asserted.                          --
-- A second specification, deadlines, follows at the end to       --
-- exercise the optional unit-minimality assumption and the       --
-- residual var-rule disjunctions.                                --
------------------------------------------------------------------

open import Data.List.Base using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_; z≤n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩; _≾ₒ_)
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; min; max; _≾ᵢ_; _≤∞?_)
open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (spec; baseTypes; BT; reading)

open import Syntax.Grades.Example.Time.RightSided
  using (𝕀ᵣ; [0,_]; ↑_; ∞; right-sided-intervals) renaming (_≾ₒ_ to _≾ᵈ_)
open import Syntax.Grades.Example.System.Identity using (identityGradeSystem)

-- the modules below are also applied to a second specification, at the
-- end of this module

import Syntax.GroundTypes
import Syntax.Contexts
import Syntax.Types

import TypeInference.Open.Grades
import TypeInference.Open.Types
import TypeInference.Open.Subst
import TypeInference.Open.Contexts
import TypeInference.Open.ClosedContexts
import TypeInference.Open.Hyps
import TypeInference.Raw.Syntax
import TypeInference.Constraints.Syntax
import TypeInference.Infer
import TypeInference.SolverImpl
import TypeInference.SolverImpl.Enum
import TypeInference.SolverImpl.Restricted

open import TypeInference.Scopes

module TypeInference.SolverImpl.Demo where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

import Syntax.Types spec as T

open import Syntax.Contexts spec using (Ctx; []; _∷_; _⟨_⟩)

open import TypeInference.Open.Grades      spec
open import TypeInference.Open.Types       spec
open import TypeInference.Open.Subst       spec
open import TypeInference.Open.Hyps        spec
open import TypeInference.Open.ClosedContexts spec using (skel)

open import TypeInference.Raw.Syntax spec

open import TypeInference.Constraints.Syntax       spec
open import TypeInference.Constraints.Satisfaction spec

open import TypeInference.Infer spec using (Θ₁; X̂₁; t̂₁; C∅[_,_]; Inferred)

open import TypeInference.SolverImpl.Enum spec using (OpEnum)

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

open import TypeInference.SolverImpl spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing

result : {X : Subst Θ₁ ∅ˢ → Set} → Maybe (Σ[ σ ∈ Subst Θ₁ ∅ˢ ] X σ)
       → Maybe (OVType ∅ˢ × EExp ∅ˢ)
result nothing        = nothing
result (just (σ , _)) = just (X̂₁ [ σ ]ᵛ , t̂₁ [ σ ]ᵉ)

infer! : (Γ : Ctx) → (M : RawC (skel Γ)) → Maybe (OVType ∅ˢ × EExp ∅ˢ)
infer! Γ M = result (gsolveImpl C∅[ Γ , M ])

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

-- `handle` is rejected: the clause's slack constraint needs `minₑ`,
-- whose premise fails for these grades. The section at the end of this
-- module runs the same program over grades with a least unit.

ex-handle : infer! [] (handle (return ⋆) `with (λ op → return ⋆) `in (return ⋆))
          ≡ nothing
ex-handle = refl

-- Written directly, since a program never exposes binder order.
-- `escC` allocates the unknown outside the rigid's scope and pins it
-- to the rigid: unsatisfiable, refuted by the escape lemma. `okC`
-- swaps the binders, allocating the unknown inside.

solved? : ∀ {Θ} {X : Subst Θ ∅ˢ → Set} → Maybe (Σ[ σ ∈ Subst Θ ∅ˢ ] X σ) → Maybe ⊤
solved? nothing  = nothing
solved? (just _) = just tt

escC : Constraint ∅ˢ
escC = ∃ᵉ (∀ᵉ ((Unit ⇒ (Unit ‼ evar (suc zero))) ≐ᵥ (Unit ⇒ (Unit ‼ evar zero))))

okC : Constraint ∅ˢ
okC = ∀ᵉ (∃ᵉ ((Unit ⇒ (Unit ‼ evar zero)) ≐ᵥ (Unit ⇒ (Unit ‼ evar (suc zero)))))

ex-escape : solved? (gsolveImpl escC) ≡ nothing
ex-escape = refl

ex-escape-ok : solved? (gsolveImpl okC) ≡ just tt
ex-escape-ok = refl

-- `inferImpl` runs the solution through `soundC` and `groundC`,
-- yielding a typing derivation of the source system, with its type
-- and effect as fields.

typeOf : {Γ : Ctx} {M : RawC (skel Γ)} → Maybe (Inferred Γ M) → Maybe (T.VType × E)
typeOf nothing  = nothing
typeOf (just I) = just (Inferred.A I , Inferred.ε I)

ex-pipeline : typeOf (inferImpl [] (return true)) ≡ just (T.Bool , uₑ)
ex-pipeline = refl

ex-pipeline-op : typeOf (inferImpl [] (perform read ⋆ (return (var zero))))
               ≡ just (T.Base reading , op-grade read ·ₑ uₑ)
ex-pipeline-op = refl

-- Right-sided intervals are deadlines `[0, n]`, ordered by `_≤_` on
-- the endpoint, so `[0, ↑0]` is below every grade. Both grade
-- components are this monoid, over the same sensor node.

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

-- A non-resuming handler clause's effect (the unit) must be below its
-- declared grade `op-grade op ·̂ₑ e''`, `e''` rigid — derivable only
-- with unit-minimality, by `minₑ`.

module Least where

  module Cᵈ  = Syntax.Contexts               specᵈ
  module Tᵈ  = Syntax.Types                  specᵈ
  module Grᵈ = TypeInference.Open.Grades         specᵈ
  module Tyᵈ = TypeInference.Open.Types          specᵈ
  module Sbᵈ = TypeInference.Open.Subst          specᵈ
  module Hyᵈ = TypeInference.Open.Hyps           specᵈ
  module CCᵈ = TypeInference.Open.ClosedContexts specᵈ
  module Rwᵈ = TypeInference.Raw.Syntax          specᵈ
  module Cnᵈ = TypeInference.Constraints.Syntax  specᵈ
  module Inᵈ = TypeInference.Infer               specᵈ

  -- with the option, and without it

  module Sᵐ = TypeInference.SolverImpl specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ (just uᵈ-min) (just uᵈ-min)
  module S⁰ = TypeInference.SolverImpl specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ nothing       nothing

  module Rsᵈ =
    TypeInference.SolverImpl.Restricted specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ nothing nothing

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

  -- end to end: the same program elaborated into the source system,
  -- its grounded derivation reading the clause's slack off `minₑ`

  typeOfᵈ : {Γ : Cᵈ.Ctx} {M : Rwᵈ.RawC (CCᵈ.skel Γ)}
          → Maybe (Inᵈ.Inferred Γ M) → Maybe (Tᵈ.VType × 𝕀ᵣ)
  typeOfᵈ nothing  = nothing
  typeOfᵈ (just I) = just (Inᵈ.Inferred.A I , Inᵈ.Inferred.ε I)

  ex-handle-pipeline : typeOfᵈ (Sᵐ.inferImpl Cᵈ.[] prog)
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

  solved?ᵈ : ∀ {Θ} {X : Sbᵈ.Subst Θ ∅ˢ → Set}
           → Maybe (Σ[ σ ∈ Sbᵈ.Subst Θ ∅ˢ ] X σ) → Maybe ⊤
  solved?ᵈ nothing  = nothing
  solved?ᵈ (just _) = just tt

  -- the ground path closes it by the eternality side, the grade side
  -- being false

  ex-disj-close : solved?ᵈ (S⁰.gsolveImpl disjC) ≡ just tt
  ex-disj-close = refl

  -- The same grade under a type variable: eternality is open, the
  -- grade side is refuted, so reporting narrows the disjunction.

  narrowC : Cnᵈ.Constraint (∅ˢ +ty)
  narrowC = Cnᵈ.Et∨≾ᵘ (Tyᵈ.tvar (newᵗ {∅ˢ})) (Grᵈ.rconst [0, ↑ 1 ])

  -- the solver's disjunctions, then the report's atoms, orderings
  -- and surviving disjunctions

  reportOfᵈ : ∀ {Θ₀} → Cnᵈ.Constraint Θ₀
            → Maybe (Σ[ Θ ∈ Scope ] (List (Tyᵈ.OVType Θ × Grᵈ.RExp Θ)
                                      × List (TyVar Θ)
                                      × List (Grᵈ.RExp Θ × Grᵈ.RExp Θ)
                                      × List (Tyᵈ.OVType Θ × Grᵈ.RExp Θ)))
  reportOfᵈ C with Rsᵈ.reportOn C
  ... | nothing = nothing
  ... | just r  = just (Rsᵈ.Reported.Θ' r ,
                        Hyᵈ.disj (Rsᵈ.Reported.Q  r) ,
                        Hyᵈ.ets  (Rsᵈ.Reported.Q̂ r) ,
                        Hyᵈ.ordᵣ (Rsᵈ.Reported.Q̂ r) ,
                        Hyᵈ.disj (Rsᵈ.Reported.Q̂ r))

  -- the solver residualises the disjunction; the report keeps the
  -- eternality atom alone

  ex-narrow : reportOfᵈ narrowC
            ≡ just (∅ˢ +ty ,
                    (Tyᵈ.tvar (newᵗ {∅ˢ}) , Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ ,
                    newᵗ {∅ˢ} ∷ᴸ []ᴸ , []ᴸ , []ᴸ)
  ex-narrow = refl

  -- a met eternality demand is dropped outright

  ex-narrow-met : reportOfᵈ disjC
                ≡ just (∅ˢ , (Tyᵈ.Unit , Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ ,
                        []ᴸ , []ᴸ , []ᴸ)
  ex-narrow-met = refl

  -- a function type is never eternal, so both sides are refuted here:
  -- narrowing leaves the false ordering rather than hiding it

  bothC : Cnᵈ.Constraint ∅ˢ
  bothC = Cnᵈ.Et∨≾ᵘ (Tyᵈ.Unit Tyᵈ.⇒ (Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ)) (Grᵈ.rconst [0, ↑ 1 ])

  ex-narrow-both : reportOfᵈ bothC
                 ≡ just (∅ˢ ,
                         (Tyᵈ.Unit Tyᵈ.⇒ (Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ) ,
                          Grᵈ.rconst [0, ↑ 1 ]) ∷ᴸ []ᴸ ,
                         []ᴸ , (Grᵈ.rconst [0, ↑ 1 ] , Grᵈ.ûᵣ) ∷ᴸ []ᴸ , []ᴸ)
  ex-narrow-both = refl

-- The solver is principal on every constraint: a program the solver
-- accepts has a principal type.

module Unguarded where

  module OC = TypeInference.Open.Contexts spec

  open import TypeInference.Principality            spec using (Principal; C[_,_])
  open import TypeInference.Principality.Restricted spec using (principal-on)
  open import TypeInference.SolverImpl.Restricted   spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing
    using (solveOn; solverImplOn)

  Γ∅ : OC.OCtx ∅ˢ 0
  Γ∅ = OC.[]

  prog-true : RawC 0
  prog-true = return true

  -- a program the solver accepts has a principal solution-with-residue,
  -- and hence a principal type

  principal? : ∀ {n} → (Γ : OC.OCtx ∅ˢ n) → (M : RawC n) → Maybe (Principal Γ M)
  principal? Γ M with solveOn C[ Γ , M ] in e
  ... | nothing           = nothing
  ... | just (Θ' , σ , Q) = just (principal-on solverImplOn Γ M tt e)

  ex-principal : Σ[ p ∈ Principal Γ∅ prog-true ]
                   (principal? Γ∅ prog-true ≡ just p)
  ex-principal = _ , refl
