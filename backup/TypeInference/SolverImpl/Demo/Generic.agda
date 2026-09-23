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

open import Data.Maybe.Base using (Maybe)
open import Data.Fin using (zero; suc)
open import Data.Product using (_,_)

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

open import TypeInference.OpenSyntax.Grades         S
open import TypeInference.OpenSyntax.Types          S
open import TypeInference.OpenSyntax.Subst          S using (idˢ)
open import TypeInference.OpenSyntax.Hyps           S

import TypeInference.OpenSyntax.Contexts S as OC

open import TypeInference.Raw.Syntax S

open import TypeInference.Constraints.Syntax S
open import TypeInference.Constraints.Satisfaction S using (_⊨[_]_)

------------------------------------------------------------------------
-- Running the solver
--
-- `reportOf` reports a program's principal type, and `solveOn` solves
-- a constraint.

open import TypeInference.SolverImpl.Demo.Report S opEnum umin?ᵣ umin?ₑ public

open import TypeInference.SolverImpl.Restricted S opEnum umin?ᵣ umin?ₑ
  using (solveOn) public

-- the empty context

Γ∅ : OC.OCtx ∅ˢ 0
Γ∅ = OC.[]

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
-- Handler clauses that touch their continuation
--
-- A clause is typed for every effect `e''` of the continuation it is
-- handed, so the continuation's effect is a rigid. Each clause below
-- works on it: `forward` performs the operation again and resumes with
-- its answer, which is `Worked.Typing.Core`'s `forwarding`; `unboxing`
-- unboxes the continuation and drops it; `performing` performs and does
-- not resume; `resumingTwice` resumes twice, the second time across the
-- lock the first resumption leaves.

forward : RawC 0
forward = handle (return ⋆)
          `with (λ op → perform op (var (suc zero))
                          (unbox (suc zero) (var zero · var (suc zero))))
          `in (return ⋆)

unboxing : RawC 0
unboxing = handle (return ⋆) `with (λ op → unbox zero (return ⋆)) `in (return ⋆)

performing : RawC 0
performing = handle (return ⋆)
             `with (λ op → perform op (var (suc zero)) (return ⋆))
             `in (return ⋆)

resumingTwice : RawC 0
resumingTwice =
  handle (return ⋆)
  `with (λ op → perform op (var (suc zero))
                  (unbox (suc zero)
                    ((var zero · var (suc zero))
                      ⨟ (var (suc zero) · var (suc (suc zero))))))
  `in (return ⋆)

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

------------------------------------------------------------------------
-- Rigid scopes
--
-- `localC` bounds an unknown allocated under the rigid by the rigid
-- alone: its least solution is the rigid itself. `stripC` bounds an
-- unknown allocated outside by an expression in the rigid, which holds
-- for every rigid exactly when it holds at the least one. `topC` and
-- `stripTopC` bound it below instead, which holds for every rigid
-- exactly when it holds at the top. `cycC` bounds the local unknown by
-- a product with itself as well, and no finite join reaches its least
-- solution.

localC : Constraint ∅ˢ
localC = ∀ᵉ (∃ᵉ (evar (suc zero) ≾̂ₑᶜ evar zero))

stripC : Constraint ∅ˢ
stripC = ∃ᵉ (∀ᵉ (evar (suc zero) ≾̂ₑᶜ (econst (op-grade op₀) ·̂ₑ evar zero)))

topC : Constraint ∅ˢ
topC = ∃ᵉ (∀ᵉ (evar zero ≾̂ₑᶜ evar (suc zero)))

stripTopC : Constraint ∅ˢ
stripTopC = ∃ᵉ (∀ᵉ ((econst (op-grade op₀) ·̂ₑ evar zero) ≾̂ₑᶜ evar (suc zero)))

-- `topC` holds with its unknown at the top

topC-sat : idˢ ⊨[ ∅ᴴ ] topC
topC-sat = econst ⊤ₑ , topₑ

cycC : Constraint ∅ˢ
cycC = ∀ᵉ (∃ᵉ (((econst (op-grade op₀) ·̂ₑ evar zero) ≾̂ₑᶜ evar zero)
              ∧̂ (evar (suc zero) ≾̂ₑᶜ evar zero)))
