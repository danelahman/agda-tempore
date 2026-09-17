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
------------------------------------------------------------------

open import Data.List.Base using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.LeftSided using (𝕀; [_,+∞⟩; _≾ₒ_)
open import Syntax.Grades.Example.Time.TwoSided  using (Interval; min; max; _≾ᵢ_)
open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (spec; BT; reading)

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

open import Inference.SolverImpl spec ≾ᵣ-dec ≾ₑ-dec ops₃

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
-- staged resolution of the probe is what produces this answer

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

-- a nested lambda: each level costs the probe one stage

ex-lam² : infer! [] (return (lam (return (lam (return true)))))
        ≡ just (Unit ⇒ ((Unit ⇒ (Bool ‼ ûₑ)) ‼ ûₑ) , ûₑ)
ex-lam² = refl

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

-- what the solver cannot do: a handler clause is typed under a RIGID
-- effect variable `e''`, and its slack constraint `ûₑ ≾̂ₑᶜ (g ·̂ₑ e'')`
-- has no derivation in `_⊩_≾̂ₑ_` — there is no rule taking a unit below
-- a product with an opaque variable. `handle` is therefore rejected,
-- and this is checked, not asserted

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
