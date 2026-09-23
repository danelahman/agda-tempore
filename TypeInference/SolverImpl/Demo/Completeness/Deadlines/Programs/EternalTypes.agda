--------------------------------------------------------------------------------
-- Completeness checks at deadlines: `eternal_types.tpe` without `after`.     --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; uᵈ-min)

open import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Setup

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs.EternalTypes where

open LanguageSpec specᵈ
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades   specᵈ
open import TypeInference.OpenSyntax.Types    specᵈ
open import TypeInference.OpenSyntax.Contexts specᵈ
open import TypeInference.OpenSyntax.Hyps     specᵈ
open import TypeInference.OpenSyntax.Language specᵈ

open M

-- `eternal_types.tpe`, `stamp_later`: an eternal value survives a wait

et-stamp : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (ûₑ ·̂ₑ (d 3 ·̂ₑ ûₑ))
et-stamp = return true ⨟ delay 3 (return (v𝔹 (Tl-⟨⟩ Hd)))

ex-et-stamp : Verdict et-stamp
ex-et-stamp = ok Bool (econst (of-natᵉ 3)) refl ≤!

-- `keep 5`

et-keep : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (d 1 ·̂ₑ ûₑ)
et-keep = lam (delay 1 (return (v𝔹 (Tl-⟨⟩ Hd)))) · true

ex-et-keep : Verdict et-keep
ex-et-keep = ok Bool (econst (of-natᵉ 1)) refl ≤!

-- `handle (perform Tick (); 1) with h 2`: the `Tick` clause resumes and
-- returns the eternal value captured from outside the handler

et-h : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ _
et-h = return false
       ⨟ handle perform write (const reading 0) (return true)
         `with tick
         `in (return (v Hd))
  where
    tick : (op : Op) → Clause ∅ᴴ (∅ᶜ ⟨ ∣ ûₑ ∣̂ᵉ ⟩ ∷ Bool) Bool op
    tick write =
      coerce (transₑ (eqₑ ≡̂ₑ-identityʳ)
               (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (minₑ uᵈ-min) ⊩≾̂ₑ-refl)))
        (unbox Hd (minᵣ uᵈ-min) (<:̂ᵛ-refl _) (v Hd · ⋆)
         ⨟ return (v𝔹 (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd)))))))
    tick read  = forward read
    tick send  = forward send

-- refused: `x` is used under the lock of the resumption, as in `Kept`

ex-et-h : Verdict et-h
ex-et-h = refused refl
