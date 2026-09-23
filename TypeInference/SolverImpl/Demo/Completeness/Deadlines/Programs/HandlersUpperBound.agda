--------------------------------------------------------------------------------
-- Completeness checks at deadlines: `handlers_upper_bound.tpe`.              --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read)
open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; uᵈ-min)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs.HandlersUpperBound where

open LanguageSpec specᵈ
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades   specᵈ
open import TypeInference.OpenSyntax.Types    specᵈ
open import TypeInference.OpenSyntax.Contexts specᵈ
open import TypeInference.OpenSyntax.Hyps     specᵈ
open import TypeInference.OpenSyntax.Language specᵈ

open M

-- `handlers_upper_bound.tpe`, run on `let x = perform Get () in return x`

get : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (econst (op-grade read) ·̂ₑ ûₑ)
get = perform read ⋆ (return (v Hd))

-- `h`: the clause idles the operation's tick and resumes

ub-h : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h = handle get
       `with (λ op → resumeAfter τ τₑ τᵣ ans {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading} op)
       `in (return (v Hd))

ex-ub-h : Verdict ub-h
ex-ub-h = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

-- `h_fast`: it idles less than the operation allows

ub-h-fast : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h-fast = handle get
            `with (λ op → resumeAfter (λ _ → 0)
                            (λ op → uᵈ-min (op-grade op)) (λ op → uᵈ-min (mapᵉ (op-grade op)))
                            ans {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading} op)
            `in (return (v Hd))

ex-ub-h-fast : Verdict ub-h-fast
ex-ub-h-fast = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

-- `h_abandon`: the clause never resumes

ub-h-abandon : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h-abandon = handle get
               `with (λ op → coerce (minₑ uᵈ-min) (return (const reading 0)))
               `in (return (v Hd))

ex-ub-h-abandon : Verdict ub-h-abandon
ex-ub-h-abandon = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

-- `h_before`: a local function is used before resuming, its result
-- kept across the resumption

ub-h-before : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h-before = handle get `with before `in (return (v Hd))
  where
    before : (op : Op) → Clause ∅ᴴ ∅ᶜ (Base reading) op
    before op =
      coerce (transₑ (eqₑ (≡̂ₑ-trans ≡̂ₑ-identityˡ (≡̂ₑ-trans ≡̂ₑ-identityˡ ≡̂ₑ-identityʳ)))
               (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (minₑ uᵈ-min) ⊩≾̂ₑ-refl)))
        (return (lam (return (const reading 1)))
         ⨟ ((v Hd · ⋆)
         ⨟ unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))
             (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong (≡̂ᵣ-trans ≡̂ᵣ-identityˡ ≡̂ᵣ-map-const)
                                              ≡̂ᵣ-map-const)
                                    ≡̂ᵣ-const-·))
                     (minᵣ uᵈ-min))
             (<:̂ᵛ-refl _)
             ((v Hd · ans op) ⨟ return (v Hd))))

ex-ub-h-before : Verdict ub-h-before
ex-ub-h-before = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!
