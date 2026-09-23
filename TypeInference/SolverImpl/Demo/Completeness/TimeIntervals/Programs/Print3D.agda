--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: `3dprint.tpe`.           --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Spec using (spec)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.Print3D where

open LanguageSpec spec
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- `3dprint.tpe`, the first run: two prints of seven ticks, each boxed
-- for five, then cured in five; a model is a `Bool`

print-model : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n}
            → Q ∣ Γ ⊢V⦂ Bool ⇒ [ rconst (of-natʳ 5) ] Bool ‼ (d 7 ·̂ₑ ûₑ)
print-model = lam (delay 7 (box (rconst (of-natʳ 5)) (v𝔹 (Tl-⟨⟩ (Tl-⟨⟩ Hd))) (return (v Hd))))

uv-cure : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n}
        → Q ∣ Γ ⊢V⦂ Bool ⇒ Bool ‼ (d 5 ·̂ₑ ûₑ)
uv-cure = lam (delay 5 (return (v𝔹 (Tl-⟨⟩ Hd))))

pr-run : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Bool |×| Bool) ‼ _
pr-run =
  return print-model ⨟ (return uv-cure
  ⨟ ((#ᵛ (# 1) · true)
  ⨟ ((#ᵛ (# 2) · false)
  ⨟ unbox (lookup-var _ (# 1)) ⊩ᵣ! (<:̂ᵛ-refl _)
      ((#ᵛ (# 3) · #ᵛ (# 0))
      ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _)
          ((#ᵛ (# 5) · #ᵛ (# 0))
          ⨟ return ⦉ #ᵛ (# 1) , #ᵛ (# 0) ⦊)))))

ex-pr-run : Verdict pr-run
ex-pr-run = ok (Bool |×| Bool) (econst (of-natᵉ 24)) refl ≤!
