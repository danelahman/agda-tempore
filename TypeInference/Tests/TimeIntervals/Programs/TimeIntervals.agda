--------------------------------------------------------------------------------
-- Tests at the sensor node's windows: `time_intervals.tpe`.                  --
--------------------------------------------------------------------------------

open import Data.Fin using (#_)
open import Data.Unit using (tt)

open import Data.Product using (_,_)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

open import Util.Equality

open import TypeInference.Scopes

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Tests.TimeIntervals.Setup

module TypeInference.Tests.TimeIntervals.Programs.TimeIntervals where

open LanguageSpec spec
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

open M

-- `time_intervals.tpe`, `foo1` to `foo5`: two delays, of three ticks
-- in all, then a box demanding one tick opened

ti-foo1 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ti-foo1 = box (rconst (of-natʳ 1)) (const reading 1)
            (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (const reading 1))))

ex-ti-foo1 : Outcome ti-foo1
ex-ti-foo1 = ok (scope 1 1 7 , Base reading ‼ econst (of-natᵉ 3) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ti-foo2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ti-foo2 = box (rconst (of-natʳ 1)) (const reading 1)
            (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd))))

ex-ti-foo2 : Outcome ti-foo2
ex-ti-foo2 = ok (scope 2 1 7 , Base reading ‼ econst (of-natᵉ 3) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

ti-foo3 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
ti-foo3 = return (const reading 7)
          ⨟ box (rconst (of-natʳ 1)) (const reading 1)
              (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆) ⨟ (return (const reading 3)
                ⨟ unbox (lookup-var _ (# 3)) ⊩ᵣ! (<:̂ᵛ-refl _)
                    (return ⦉ #ᵛ (# 0) , #ᵛ (# 1) ⦊))))

ex-ti-foo3 : Outcome ti-foo3
ex-ti-foo3 = ok (scope 3 1 11 ,
                 (Base reading |×| Base reading) ‼ econst (of-natᵉ 3) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

-- `x` is used three ticks after it is bound

ti-foo4 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
ti-foo4 = return (const reading 7)
          ⨟ box (rconst (of-natʳ 1)) (const reading 1)
              (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆) ⨟ (return (const reading 3)
                ⨟ unbox (lookup-var _ (# 3)) ⊩ᵣ! (<:̂ᵛ-refl _)
                    (return ⦉ #ᵛ (# 0) , #ᵛ (# 5) ⦊))))

ex-ti-foo4 : Outcome ti-foo4
ex-ti-foo4 = ok (scope 3 1 11 ,
                 (Base reading |×| Base reading) ‼ econst (of-natᵉ 3) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl

-- `x` boxed at two ticks as well, and both boxes opened

ti-foo5 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| (Base reading |×| Base reading)) ‼ _
ti-foo5 = return (const reading 7)
          ⨟ box (rconst (of-natʳ 2)) (#ᵛ (# 0))
              (box (rconst (of-natʳ 1)) (const reading 1)
                (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆) ⨟ (return (const reading 3)
                  ⨟ unbox (lookup-var _ (# 3)) ⊩ᵣ! (<:̂ᵛ-refl _)
                      (unbox (lookup-var _ (# 5)) ⊩ᵣ! (<:̂ᵛ-refl _)
                        (return ⦉ #ᵛ (# 1) , ⦉ #ᵛ (# 7) , #ᵛ (# 0) ⦊ ⦊))))))

ex-ti-foo5 : Outcome ti-foo5
ex-ti-foo5 = ok (scope 6 2 11 ,
                 (Base reading |×| (Base reading |×| Base reading)) ‼ econst (of-natᵉ 3) ,
                 []ᴸ , []ᴸ , []ᴸ , []ᴸ , []ᴸ) refl
