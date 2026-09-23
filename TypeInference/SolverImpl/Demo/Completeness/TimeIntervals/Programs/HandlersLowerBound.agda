--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows:                          --
-- `handlers_lower_bound.tpe`.                                                --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read; write)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.HandlersLowerBound where

open LanguageSpec spec
open Operations Ops

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- `handlers_lower_bound.tpe`, `h`: `Get` resumes after its tick, `Set`
-- is forwarded, and the return case performs both

lb-h : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h = handle perform read ⋆ (return (v Hd))
       `with (λ op → readResumes {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
       `in (perform write (const reading 42)
              (perform read ⋆ (return ⦉ #ᵛ (# 2) , #ᵛ (# 0) ⦊)))

ex-lb-h : Verdict lb-h
ex-lb-h = ok (Base reading |×| Base reading) (econst [ 4 , ↑ 5 , s≤s (s≤s (s≤s (s≤s z≤n))) ]) refl ≤!

-- `h'`: the same clauses, a return case that takes no time

lb-h' : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h' = handle perform read ⋆ (return (v Hd))
        `with (λ op → readResumes {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
        `in (return ⦉ v Hd , v Hd ⦊)

ex-lb-h' : Verdict lb-h'
ex-lb-h' = ok (Base reading |×| Base reading) (econst (op-grade read)) refl ≤!

-- `h''`: the `Get` clause performs `Get` itself

lb-h'' : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h'' = handle perform read ⋆ (return (v Hd))
         `with (λ op → readPerforms {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
         `in (return ⦉ v Hd , v Hd ⦊)

ex-lb-h'' : Verdict lb-h''
ex-lb-h'' = ok (Base reading |×| Base reading) (econst (op-grade read)) refl ≤!

-- `h_offset 10`: the clause resumes with a reading bound outside it

lb-offset : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-offset =
  return (const reading 10)
  ⨟ handle perform read ⋆ (return (v Hd))
    `with (λ op → readOffset {Q = ∅ᴴ} {Γ = ∅ᶜ ⟨ ∣ ûₑ ∣̂ᵉ ⟩}
                             {B = Base reading |×| Base reading} op)
    `in (return ⦉ #ᵛ (# 0) , #ᵛ (# 1) ⦊)

ex-lb-offset : Verdict lb-offset
ex-lb-offset = ok (Base reading |×| Base reading) (econst (op-grade read)) refl ≤!
