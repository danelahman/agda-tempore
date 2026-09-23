--------------------------------------------------------------------------------
-- Tests at the sensor node's windows:                                        --
-- `handlers_lower_bound.tpe`.                                                --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read; write)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Programs.HandlersLowerBound where

open LanguageSpec spec
open GradeSystemInterface Grades
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

ex-lb-h : Outcome lb-h
ex-lb-h = ok (scope 13 0 15 ,
              (Base reading |×| Base reading) ‼ econst [ 4 , ↑ 5 , s≤s (s≤s (s≤s (s≤s z≤n))) ] ,
              []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

-- `h'`: the same clauses, a return case that takes no time

lb-h' : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h' = handle perform read ⋆ (return (v Hd))
        `with (λ op → readResumes {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
        `in (return ⦉ v Hd , v Hd ⦊)

ex-lb-h' : Outcome lb-h'
ex-lb-h' = ok (scope 13 0 13 ,
               (Base reading |×| Base reading) ‼ econst (of-natᵉ 1) ,
               []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

-- `h''`: the `Get` clause performs `Get` itself

lb-h'' : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h'' = handle perform read ⋆ (return (v Hd))
         `with (λ op → readPerforms {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
         `in (return ⦉ v Hd , v Hd ⦊)

ex-lb-h'' : Outcome lb-h''
ex-lb-h'' = ok (scope 13 0 13 ,
                (Base reading |×| Base reading) ‼ econst (of-natᵉ 1) ,
                []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

-- `h_offset 10`: the clause resumes with a reading bound outside it

lb-offset : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-offset =
  return (const reading 10)
  ⨟ handle perform read ⋆ (return (v Hd))
    `with (λ op → readOffset {Q = ∅ᴴ} {Γ = ∅ᶜ ⟨ ∣ ûₑ ∣̂ᵉ ⟩}
                             {B = Base reading |×| Base reading} op)
    `in (return ⦉ #ᵛ (# 0) , #ᵛ (# 1) ⦊)

ex-lb-offset : Outcome lb-offset
ex-lb-offset = ok (scope 13 0 15 ,
                   (Base reading |×| Base reading) ‼ econst (of-natᵉ 1) ,
                   []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
