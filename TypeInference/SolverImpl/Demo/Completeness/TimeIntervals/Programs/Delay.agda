--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: `delay.tpe` without      --
-- `foobar`.                                                                  --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.Delay where

open LanguageSpec spec
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- `delay.tpe`, `foo_int_temporal`, applied to `Zero`

fit : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n}
    → Q ∣ Γ ⊢V⦂ Bool ⇒ Base reading ‼ (d 3 ·̂ₑ ûₑ)
fit = lam (if v𝔹 Hd `then delay 3 (return (const reading 0))
                    `else delay 3 (return (const reading 1)))

dl-foo-int : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (d 3 ·̂ₑ ûₑ)
dl-foo-int = fit · true

ex-dl-foo-int : Verdict dl-foo-int
ex-dl-foo-int = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!

-- `del Zero`: the argument is computed in two ticks

dl-del : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (d 9 ·̂ₑ ((d 2 ·̂ₑ ûₑ) ·̂ₑ (d 3 ·̂ₑ ûₑ)))
dl-del = delay 9 (delay 2 (return true) ⨟ (fit · v Hd))

ex-dl-del : Verdict dl-del
ex-dl-del = ok (Base reading) (econst (of-natᵉ 14)) refl ≤!

-- `higher 5 6`: the function's five ticks sit on the inner arrow

dl-higher : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ (ûₑ ·̂ₑ (d 5 ·̂ₑ ûₑ))
dl-higher = (lam (return (lam (delay 5 (return ⦉ #ᵛ (# 1) , #ᵛ (# 0) ⦊))))
               · const reading 5)
            ⨟ (#ᵛ (# 0) · const reading 6)

ex-dl-higher : Verdict dl-higher
ex-dl-higher = ok (Base reading |×| Base reading) (econst (of-natᵉ 5)) refl ≤!

-- `higher2 5 6`: ten ticks before the closure, five on it

dl-higher2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading)
                          ‼ ((d 10 ·̂ₑ ûₑ) ·̂ₑ (d 5 ·̂ₑ ûₑ))
dl-higher2 = (lam (delay 10 (return (lam (delay 5 (return ⦉ #ᵛ (# 1) , #ᵛ (# 0) ⦊)))))
                · const reading 5)
             ⨟ (#ᵛ (# 0) · const reading 6)

ex-dl-higher2 : Verdict dl-higher2
ex-dl-higher2 = ok (Base reading |×| Base reading) (econst (of-natᵉ 15)) refl ≤!

-- `test2 ()`: the delay banks the three ticks the box demands

dl-test2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (d 3 ·̂ₑ ûₑ)
dl-test2 = box (rconst (of-natʳ 3)) (const reading 42)
             (delay 3 (unbox (lookup-var _ (# 0)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd))))

ex-dl-test2 : Verdict dl-test2
ex-dl-test2 = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!
