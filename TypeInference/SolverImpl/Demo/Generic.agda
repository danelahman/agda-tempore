------------------------------------------------------------------
-- The demo programs, and the way they are measured.              --
--                                                                --
-- Everything here is stated over an arbitrary `LanguageSpec`: a  --
-- handful of library-shaped programs, which name no grade, and   --
-- the wrappers that run the solver on them. The programs that    --
-- perform take the operation and the value to pass it as module  --
-- parameters, since a raw term cannot know either.               --
--                                                                --
-- No expected results live here. Against an abstract spec they   --
-- could not be discharged by computation, which is the whole     --
-- point of stating them; each instance writes its own out at its --
-- own grades, as `Worked.Typing.*` do for the typing rules.      --
------------------------------------------------------------------

open import Data.List.Base using (List; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)


open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H
import TypeInference.Raw.Syntax as R

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Demo.Generic
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  -- an operation, and a raw value to pass it, for the shapes that perform
  (op₀ : Operations.Op (LanguageSpec.Ops S))
  (arg₀ : ∀ {n} → R.RawV S n)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

import Syntax.Types S as T

open import Syntax.Contexts S using (Ctx)

open import TypeInference.OpenSyntax.Grades         S
open import TypeInference.OpenSyntax.Types          S
open import TypeInference.OpenSyntax.Subst          S
open import TypeInference.OpenSyntax.Hyps           S
open import TypeInference.OpenSyntax.ClosedContexts S using (skel)

import TypeInference.OpenSyntax.Contexts S as OC

open import TypeInference.Raw.Syntax S

open import TypeInference.Constraints.Syntax S

open import TypeInference.Infer S using (Inferred)
open import TypeInference.Principality S using (X̂; t̂; C[_,_])

open import TypeInference.SolverImpl S opEnum umin?ᵣ umin?ₑ
  using (gsolveImpl; greportImpl; inferImpl) public

open import TypeInference.SolverImpl.Restricted S opEnum umin?ᵣ umin?ₑ
  using (reportOn; Reported)

------------------------------------------------------------------------
-- Running the solver
--
-- `infer!` reports the inferred type and effect of a closed program,
-- in sum-of-products normal form;
-- `typeOf` runs the whole pipeline, whose result is a derivation of the
-- source system, and reads its type and effect off. `solved?` forgets
-- everything but whether a constraint was solved at all.

infer! : (Γ : Ctx) → (M : RawC (skel Γ)) → Maybe (OVType ∅ˢ × EExp ∅ˢ)
infer! = greportImpl

typeOf : {Γ : Ctx} {M : RawC (skel Γ)} → Maybe (Inferred Γ M) → Maybe (T.VType × E)
typeOf nothing  = nothing
typeOf (just I) = just (Inferred.A I , Inferred.ε I)

solved? : ∀ {Θ} {X : Subst Θ ∅ˢ → Set} → Maybe (Σ[ σ ∈ Subst Θ ∅ˢ ] X σ) → Maybe ⊤
solved? nothing  = nothing
solved? (just _) = just tt

------------------------------------------------------------------------
-- Reporting
--
-- The open path hands back a qualified type rather than a ground
-- solution: the scope it is stated in, the reported type, and the
-- eternality atoms, subtyping atoms, resource-grade orderings,
-- effect-grade orderings and var-rule disjunctions left with it.
-- `sizeOf` keeps only how many of each sort survive.

Γ∅ : OC.OCtx ∅ˢ 0
Γ∅ = OC.[]

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

------------------------------------------------------------------------
-- The library
--
-- Eight shapes, each isolating one thing the solver has to do with the
-- grades it is given.

-- `return ⋆`: the smallest program there is

unit : RawC 0
unit = return ⋆

-- `compose f g x = let y = f x in g y`: the two latent effects are
-- multiplied, and the capture of `g` crosses a lock

compose : RawC 0
compose = return (lam (return (lam (return (lam
            ((var (suc (suc zero)) · var zero)
              ⨟ (var (suc (suc zero)) · var zero)))))))

-- `twice f x = let y = f x in f y`: the same function used at two
-- types, and one lock

twice : RawC 0
twice = return (lam (return (lam
          ((var (suc zero) · var zero)
            ⨟ (var (suc (suc zero)) · var zero)))))

-- `branch b x y = if b then x else y`: two arms equalised by
-- subtyping, with no grade involved

branch : RawC 0
branch = return (lam (return (lam (return (lam
           (if var (suc (suc zero))
             `then return (var (suc zero))
             `else return (var zero)))))))

-- `branchE f b = if b then perform op₀ arg₀ (return ⋆) else f ⋆`: the
-- arms carry different effects, so both bound the result's effect
-- unknown from below

branchE : RawC 0
branchE =
  return (lam (return (lam
    (if var zero
       `then perform op₀ arg₀ (return ⋆)
       `else (var (suc zero) · ⋆)))))

-- the same branch sequenced with another `perform`, so that the join
-- of the two bounds stands underneath a product

seqBranch : RawC 0
seqBranch =
  return (lam (return (lam
    ((if var zero `then perform op₀ arg₀ (return ⋆)
                  `else (var (suc zero) · ⋆))
      ⨟ perform op₀ arg₀ (return ⋆)))))

-- `keep x = box x`: the box grade is not annotated, and nothing
-- constrains it

keep : RawC 0
keep = return (lam (box (var zero) (return (var zero))))

-- `wrap f = handle f ⋆ with (λ op → return ⋆) in return x`: a handler
-- whose clauses do not resume, so each clause's effect is the unit

wrap : RawC 0
wrap = return (lam (handle (var zero · ⋆)
                    `with (λ op → return ⋆)
                    `in (return (var zero))))

------------------------------------------------------------------------
-- Binder order
--
-- Written as constraints, since a program never exposes it. `escC`
-- allocates the unknown outside the rigid's scope and pins it to the
-- rigid, which the escape lemma refutes; `okC` swaps the binders,
-- allocating the unknown inside.

escC : Constraint ∅ˢ
escC = ∃ᵉ (∀ᵉ ((Unit ⇒ (Unit ‼ evar (suc zero))) ≐ᵥ (Unit ⇒ (Unit ‼ evar zero))))

okC : Constraint ∅ˢ
okC = ∀ᵉ (∃ᵉ ((Unit ⇒ (Unit ‼ evar zero)) ≐ᵥ (Unit ⇒ (Unit ‼ evar (suc zero)))))
