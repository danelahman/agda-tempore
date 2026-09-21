------------------------------------------------------------------
-- Runs the solver against `Syntax.Grades.Example.Worked.Spec`, a --
-- sensor-node specification satisfying its three assumptions.    --
-- Every example is discharged by `refl`, so what is inferred is  --
-- checked by computation, not asserted.                          --
-- A second specification, deadlines, follows to exercise the     --
-- optional unit-minimality assumption and the residual var-rule  --
-- disjunctions, and a benchmark over five library shapes closes  --
-- the module.                                                    --
------------------------------------------------------------------

open import Data.List.Base using (List; length) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero; suc; #_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_; z≤n; s≤s; _⊓_; _⊔_)
open import Data.Nat.Properties using (m⊓n≤m; m⊓n≤n; ⊓-glb; m≤m⊔n; m≤n⊔m; ⊔-lub)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩; _≾ₒ_)
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_,_]; min; max; min≤max; _≾ᵢ_; _≤∞_; _≤∞?_; ≤∞-trans; ℕ∞)
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
import TypeInference.Principality
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

open import TypeInference.SolverImpl spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing nothing nothing

result : {X : Subst Θ₁ ∅ˢ → Set} → Maybe (Σ[ σ ∈ Subst Θ₁ ∅ˢ ] X σ)
       → Maybe (OVType ∅ˢ × EExp ∅ˢ)
result nothing        = nothing
result (just (σ , _)) = just (X̂₁ [ σ ]ᵛ , t̂₁ [ σ ]ᵉ)

infer! : (Γ : Ctx) → (M : RawC (skel Γ)) → Maybe (OVType ∅ˢ × EExp ∅ˢ)
infer! Γ M = result (gsolveImpl C∅[ Γ , M ])

-- returning the unit value: the slack bound on the result effect is
-- resolved to its lower bound rather than carried

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

-- Several lower bounds on one unknown
--
-- Both branches of an `if` bound the shared effect unknown from below,
-- and the two bounds are incomparable. Without a join the closer falls
-- back on the greatest grade.

branch-op : RawC 0
branch-op = if true `then perform read ⋆ (return ⋆) `else return ⋆

ex-branch-⊤ : infer! [] branch-op ≡ just (Unit , econst ⊤ₑ)
ex-branch-⊤ = refl

-- Both grades of this specification have a binary join. Supplied, it
-- gives the same program the join of its two branch effects.

module Joins where

  infixl 7 _⊔∞_

  _⊔∞_ : ℕ∞ → ℕ∞ → ℕ∞
  (↑ m) ⊔∞ (↑ n) = ↑ (m ⊔ n)
  (↑ _) ⊔∞ ∞     = ∞
  ∞     ⊔∞ _     = ∞

  ⊔∞-ubˡ : (a b : ℕ∞) → a ≤∞ a ⊔∞ b
  ⊔∞-ubˡ (↑ m) (↑ n) = m≤m⊔n m n
  ⊔∞-ubˡ (↑ _) ∞     = tt
  ⊔∞-ubˡ ∞     _     = tt

  ⊔∞-ubʳ : (a b : ℕ∞) → b ≤∞ a ⊔∞ b
  ⊔∞-ubʳ (↑ m) (↑ n) = m≤n⊔m m n
  ⊔∞-ubʳ (↑ _) ∞     = tt
  ⊔∞-ubʳ ∞     (↑ _) = tt
  ⊔∞-ubʳ ∞     ∞     = tt

  ⊔∞-lub : {a b c : ℕ∞} → a ≤∞ c → b ≤∞ c → a ⊔∞ b ≤∞ c
  ⊔∞-lub {↑ _} {↑ _} {↑ _} p q = ⊔-lub p q
  ⊔∞-lub {↑ _} {↑ _} {∞}   p q = tt
  ⊔∞-lub {↑ _} {∞}   {∞}   p q = tt
  ⊔∞-lub {∞}   {_}   {∞}   p q = tt

  -- a lower bound is the weaker grade, so the join takes the smaller
  -- endpoint

  join𝕀 : Joinᵣ
  join𝕀 = record
    { _⊔ᵣ_   = λ { [ m ,+∞⟩ [ n ,+∞⟩ → [ m ⊓ n ,+∞⟩ }
    ; ⊔ᵣ-ubˡ = λ { [ m ,+∞⟩ [ n ,+∞⟩ → m⊓n≤m m n }
    ; ⊔ᵣ-ubʳ = λ { [ m ,+∞⟩ [ n ,+∞⟩ → m⊓n≤n m n }
    ; ⊔ᵣ-lub = λ { {[ _ ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} p q → ⊓-glb p q }
    }

  -- the order on two-sided intervals is containment, so the join is the
  -- smallest interval containing both

  _⊔ᵢ_ : Interval∞ → Interval∞ → Interval∞
  i ⊔ᵢ j = [ min i ⊓ min j
           , max i ⊔∞ max j
           , ≤∞-trans {↑ (min i ⊓ min j)} {↑ min i} (m⊓n≤m (min i) (min j))
                      (≤∞-trans {↑ min i} (min≤max i) (⊔∞-ubˡ (max i) (max j)))
           ]

  joinᵢ : Joinₑ
  joinᵢ = record
    { _⊔ₑ_   = _⊔ᵢ_
    ; ⊔ₑ-ubˡ = λ i j → m⊓n≤m (min i) (min j) , ⊔∞-ubˡ (max i) (max j)
    ; ⊔ₑ-ubʳ = λ i j → m⊓n≤n (min i) (min j) , ⊔∞-ubʳ (max i) (max j)
    ; ⊔ₑ-lub = λ { (p₁ , p₂) (q₁ , q₂) → ⊓-glb p₁ q₁ , ⊔∞-lub p₂ q₂ }
    }

  module S⊔ = TypeInference.SolverImpl spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing
                                            (just join𝕀) (just joinᵢ)

  infer⊔ : (Γ : Ctx) → (M : RawC (skel Γ)) → Maybe (OVType ∅ˢ × EExp ∅ˢ)
  infer⊔ Γ M = result (S⊔.gsolveImpl C∅[ Γ , M ])

  ex-branch-⊔ : infer⊔ [] branch-op ≡ just (Unit , econst [ 0 , ↑ 1 , z≤n ])
  ex-branch-⊔ = refl

  -- two delays: the join spans both durations

  branch-delay : RawC 0
  branch-delay = if true `then delay 2 (return ⋆) `else delay 1 (return ⋆)

  ex-delay-⊔ : infer⊔ [] branch-delay
             ≡ just (Unit , econst [ 1 , ↑ 2 , s≤s z≤n ])
  ex-delay-⊔ = refl

  -- a join changes nothing where one bound already dominates

  ex-unit-⊔ : infer⊔ [] (return ⋆) ≡ just (Unit , ûₑ)
  ex-unit-⊔ = refl

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
                 nothing nothing
  module S⁰ = TypeInference.SolverImpl specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃ nothing       nothing
                 nothing nothing

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
  reportOfᵈ C with Rsᵈ.reportOn (Tyᵈ.Unit Tyᵈ.‼ Grᵈ.ûₑ) C
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

-- The library benchmark
--
-- `reportOn` is the open path: it hands back a qualified type rather
-- than a ground solution. Five library shapes go through it, with
-- `return ⋆` for a floor, each stated twice — the report in full,
-- and the number of hypotheses of each sort left with it. Every
-- grade expression shown is in product normal form.

module Library where

  module OC = TypeInference.Open.Contexts spec

  open import TypeInference.Principality spec using (X̂; t̂; C[_,_])
  open import TypeInference.SolverImpl.Restricted spec ≾ᵣ-dec ≾ₑ-dec ops₃ nothing nothing
    using (reportOn; Reported)

  Γ∅ : OC.OCtx ∅ˢ 0
  Γ∅ = OC.[]

  -- a report: the scope it is stated in, the reported type, and the
  -- eternality atoms, subtyping atoms, resource-grade orderings,
  -- effect-grade orderings and var-rule disjunctions left with it

  Report : Set
  Report = Σ[ Θ ∈ Scope ] (OCType Θ
                            × List (TyVar Θ)
                            × List (TyVar Θ × TyVar Θ)
                            × List (RExp Θ × RExp Θ)
                            × List (EExp Θ × EExp Θ)
                            × List (OVType Θ × RExp Θ))

  reportOf : RawC 0 → Maybe Report
  reportOf M with reportOn (X̂ ∅ˢ ‼ t̂ ∅ˢ) C[ Γ∅ , M ]
  ... | nothing = nothing
  ... | just r  = just (Reported.Θ' r , Reported.X̃ r ,
                        ets  (Reported.Q̃ r) , subᵥ (Reported.Q̃ r) ,
                        ordᵣ (Reported.Q̃ r) , ordₑ (Reported.Q̃ r) ,
                        disj (Reported.Q̃ r))

  sizeOf : RawC 0 → Maybe (ℕ × ℕ × ℕ × ℕ × ℕ)
  sizeOf M with reportOn (X̂ ∅ˢ ‼ t̂ ∅ˢ) C[ Γ∅ , M ]
  ... | nothing = nothing
  ... | just r  = just (length (ets  (Reported.Q̃ r)) ,
                        length (subᵥ (Reported.Q̃ r)) ,
                        length (ordᵣ (Reported.Q̃ r)) ,
                        length (ordₑ (Reported.Q̃ r)) ,
                        length (disj (Reported.Q̃ r)))

  -- `return ⋆`

  ex-unit-report : reportOf (return ⋆)
                 ≡ just (scope 0 0 1 , Unit ‼ ûₑ , []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
  ex-unit-report = refl

  ex-unit-size : sizeOf (return ⋆) ≡ just (0 , 0 , 0 , 0 , 0)
  ex-unit-size = refl

  -- `compose f g x = let y = f x in g y`, reported as
  -- `(α ⇒ β ‼ e₁) ⇒ (β ⇒ γ ‼ e₂) ⇒ (α ⇒ γ ‼ e₁ · e₂) ‼ 0`, with one
  -- qualifier: the lock that the capture of `g` crosses

  compose : RawC 0
  compose = return (lam (return (lam (return (lam
              ((var (suc (suc zero)) · var zero)
                ⨟ (var (suc (suc zero)) · var zero)))))))

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

  -- `twice f x = let y = f x in f y`: the two uses of `f` leave two
  -- subtyping atoms, and the lock leaves one qualifier

  twice : RawC 0
  twice = return (lam (return (lam
            ((var (suc zero) · var zero)
              ⨟ (var (suc (suc zero)) · var zero)))))

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

  -- `branch b x y = if b then x else y`: one subtyping atom per arm,
  -- and no grade ordering at all

  branch : RawC 0
  branch = return (lam (return (lam (return (lam
             (if var (suc (suc zero))
               `then return (var (suc zero))
               `else return (var zero)))))))

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

  -- `keep x = box x`: the box grade stays a variable, and the one
  -- var-rule disjunction on it is all that is left

  keep : RawC 0
  keep = return (lam (box (var zero) (return (var zero))))

  ex-keep-report : reportOf keep
                 ≡ just (scope 8 3 3 ,
                         (tvar (# 4) ⇒ [ rvar (# 1) ] tvar (# 4) ‼ ûₑ) ‼ ûₑ ,
                         []ᴸ , []ᴸ , []ᴸ , []ᴸ ,
                         (tvar (# 4) , rvar (# 1)) ∷ᴸ []ᴸ)
  ex-keep-report = refl

  ex-keep-size : sizeOf keep ≡ just (0 , 0 , 0 , 0 , 1)
  ex-keep-size = refl

  -- `wrap f = handle f ⋆ with (λ op → return ⋆) in return x` is
  -- declined: the clause's slack needs unit-minimality, which the
  -- node's effect grades lack, and the failure is inside `solve` at
  -- the rigid binder

  wrap : RawC 0
  wrap = return (lam (handle (var zero · ⋆)
                      `with (λ op → return ⋆)
                      `in (return (var zero))))

  ex-wrap-report : reportOf wrap ≡ nothing
  ex-wrap-report = refl

  ex-wrap-size : sizeOf wrap ≡ nothing
  ex-wrap-size = refl

  -- Over the deadline grades, whose unit is least, the same shape is
  -- reported, with nothing left over

  module Deadlines where

    module Grᵈ = TypeInference.Open.Grades      specᵈ
    module Tyᵈ = TypeInference.Open.Types       specᵈ
    module Hyᵈ = TypeInference.Open.Hyps        specᵈ
    module OCᵈ = TypeInference.Open.Contexts    specᵈ
    module Rwᵈ = TypeInference.Raw.Syntax       specᵈ
    module Prᵈ = TypeInference.Principality     specᵈ

    module Rsᵐ = TypeInference.SolverImpl.Restricted specᵈ ≾ᵈ-dec ≾ᵈ-dec opsᵈ₃
                   (just uᵈ-min) (just uᵈ-min)

    Γ∅ᵈ : OCᵈ.OCtx ∅ˢ 0
    Γ∅ᵈ = OCᵈ.[]

    Reportᵈ : Set
    Reportᵈ = Σ[ Θ ∈ Scope ] (Tyᵈ.OCType Θ
                               × List (TyVar Θ)
                               × List (TyVar Θ × TyVar Θ)
                               × List (Grᵈ.RExp Θ × Grᵈ.RExp Θ)
                               × List (Grᵈ.EExp Θ × Grᵈ.EExp Θ)
                               × List (Tyᵈ.OVType Θ × Grᵈ.RExp Θ))

    reportOfᵈ : Rwᵈ.RawC 0 → Maybe Reportᵈ
    reportOfᵈ M with Rsᵐ.reportOn (Prᵈ.X̂ ∅ˢ Tyᵈ.‼ Prᵈ.t̂ ∅ˢ) Prᵈ.C[ Γ∅ᵈ , M ]
    ... | nothing = nothing
    ... | just r  = just (Rsᵐ.Reported.Θ' r , Rsᵐ.Reported.X̃ r ,
                          Hyᵈ.ets  (Rsᵐ.Reported.Q̃ r) , Hyᵈ.subᵥ (Rsᵐ.Reported.Q̃ r) ,
                          Hyᵈ.ordᵣ (Rsᵐ.Reported.Q̃ r) , Hyᵈ.ordₑ (Rsᵐ.Reported.Q̃ r) ,
                          Hyᵈ.disj (Rsᵐ.Reported.Q̃ r))

    sizeOfᵈ : Rwᵈ.RawC 0 → Maybe (ℕ × ℕ × ℕ × ℕ × ℕ)
    sizeOfᵈ M with Rsᵐ.reportOn (Prᵈ.X̂ ∅ˢ Tyᵈ.‼ Prᵈ.t̂ ∅ˢ) Prᵈ.C[ Γ∅ᵈ , M ]
    ... | nothing = nothing
    ... | just r  = just (length (Hyᵈ.ets  (Rsᵐ.Reported.Q̃ r)) ,
                          length (Hyᵈ.subᵥ (Rsᵐ.Reported.Q̃ r)) ,
                          length (Hyᵈ.ordᵣ (Rsᵐ.Reported.Q̃ r)) ,
                          length (Hyᵈ.ordₑ (Rsᵐ.Reported.Q̃ r)) ,
                          length (Hyᵈ.disj (Rsᵐ.Reported.Q̃ r)))

    wrapᵈ : Rwᵈ.RawC 0
    wrapᵈ = Rwᵈ.return (Rwᵈ.lam (Rwᵈ.handle (Rwᵈ.var zero Rwᵈ.· Rwᵈ.⋆)
                                 `with (λ op → Rwᵈ.return Rwᵈ.⋆)
                                 `in (Rwᵈ.return (Rwᵈ.var zero))))

    ex-wrap-reportᵈ : reportOfᵈ wrapᵈ
                    ≡ just (scope 11 0 8 ,
                            ((Tyᵈ.Unit Tyᵈ.⇒ Tyᵈ.Unit Tyᵈ.‼ Grᵈ.evar (# 1))
                              Tyᵈ.⇒ Tyᵈ.Unit Tyᵈ.‼ Grᵈ.evar (# 1))
                              Tyᵈ.‼ Grᵈ.ûₑ ,
                            []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ)
    ex-wrap-reportᵈ = refl

    ex-wrap-sizeᵈ : sizeOfᵈ wrapᵈ ≡ just (0 , 0 , 0 , 0 , 0)
    ex-wrap-sizeᵈ = refl
