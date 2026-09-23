--------------------------------------------------------------------------------
-- Tests at deadlines: `eternal_types.tpe` without `after`.                   --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; uᵈ-min)

open import TypeInference.Tests.Deadlines.Setup

module TypeInference.Tests.Deadlines.Programs.EternalTypes where

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

ex-et-stamp : Outcome et-stamp
ex-et-stamp = ok (scope 1 0 4 , Bool ‼ econst (of-natᵉ 3) ,
                  []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

-- `keep 5`

et-keep : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (d 1 ·̂ₑ ûₑ)
et-keep = lam (delay 1 (return (v𝔹 (Tl-⟨⟩ Hd)))) · true

ex-et-keep : Outcome et-keep
ex-et-keep = ok (scope 4 0 4 , Bool ‼ econst (of-natᵉ 1) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

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

ex-et-h : Outcome et-h
ex-et-h = ok (scope 12 0 16 , Bool ‼ econst (of-natᵉ 3) ,
              []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
