--------------------------------------------------------------------------------
-- Tests at deadlines: `eternal_types.tpe`'s `after`, run                     --
-- twice.                                                                     --
--------------------------------------------------------------------------------

open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.Fin using (#_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ)

open import TypeInference.Tests.Deadlines.Setup

module TypeInference.Tests.Deadlines.Programs.After where

open LanguageSpec specᵈ
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   specᵈ
open import TypeInference.OpenSyntax.Types    specᵈ
open import TypeInference.OpenSyntax.Contexts specᵈ
open import TypeInference.OpenSyntax.Hyps     specᵈ
open import TypeInference.OpenSyntax.Language specᵈ

open M

-- `after (fun () -> delay 2) 5`: the kept value is eternal

after : ∀ {A : OVType ∅ˢ} {ε}
      → ∅ᴴ ∣ (∅ᶜ ∷ (Unit ⇒ Unit ‼ ε) ∷ A) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ Unit ⊢V⦂ A
      → ∅ᴴ ∣ ∅ᶜ ⊢V⦂ (Unit ⇒ Unit ‼ ε) ⇒ (A ⇒ A ‼ (ε ·̂ₑ ûₑ)) ‼ ûₑ
after x = lam (return (lam ((v (Tl-∷ Hd) · ⋆) ⨟ return x)))

et-after : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (ûₑ ·̂ₑ ((d 2 ·̂ₑ ûₑ) ·̂ₑ ûₑ))
et-after = (after (v𝔹 (Tl-∷ (Tl-⟨⟩ Hd))) · lam (delay 2 (return ⋆)))
           ⨟ (v Hd · true)

ex-et-after : Outcome et-after
ex-et-after = ok (scope 22 0 17 , Bool ‼ econst (of-natᵉ 2) ,
                  []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

-- `after (fun () -> ()) (fun () -> ())`: `g` takes no time

et-after-pure : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Unit ⇒ Unit ‼ ûₑ) ‼ (ûₑ ·̂ₑ (ûₑ ·̂ₑ ûₑ))
et-after-pure = (after (var (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵘ-ok map-û)) · lam (return ⋆))
                ⨟ (v Hd · lam (return ⋆))

ex-et-after-pure : Outcome et-after-pure
ex-et-after-pure = ok (scope 45 0 28 , (tvar (# 0) ⇒ Unit ‼ ûₑ) ‼ ûₑ ,
                       []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
