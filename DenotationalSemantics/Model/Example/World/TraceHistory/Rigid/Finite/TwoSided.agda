------------------------------------------------------------------------
-- A trace-history Kripke frame for the rigid timed finite-expression --
-- grades as intervals.                                               --
--                                                                    --
-- Worlds are timed traces, and a grade `[ L , U ]` reaches the       --
-- histories extending the current one by one continuation that both --
-- endpoints admit (`World.History` at the interval grade):           --
--                                                                    --
--   w ⊑ʰ[ [ L , U ] ] w'   iff   Σ[ s ] w ∙ s ≡ w'                    --
--                                  and  ⟦ s ⟧ ≾ L  and  ⟦ s ⟧ ≾ U     --
--                                                                    --
-- The continuation is shared: the guarantee and the bound concern    --
-- the same run, and every exact word of it fits a word of each.      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Finite.TwoSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)

open import Syntax.Grades.Traces.Base ℚ≥0ᵀ Op
  using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; _∙_; ∣_∣⁺)

open import Syntax.Grades.Example.Traces.Rigid.Finite.TwoSided Op n code name name-code code-name running
  using (two-sided; operation′)
open import Syntax.Grades.Example.Traces.Rigid.Finite.Base Op n code name name-code code-name running
  using (expr; ⟦_⟧; _≾ᴳ_; waitᴸ; waitᵁ) renaming (_·ᵉ_ to _·ᵍ_)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Finite.Base
  Op n code name name-code code-name running
  using (‵ᵍ; events; code-injective)

open import Syntax.Grades.Exact.Lift ℚ≥0ᵀ Op n code code-injective using (_≾_)
open import Syntax.Grades.Exact.Hull ℚ≥0ᵀ Op n code code-injective running
  using (runᴸ)

import DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Finite.LeftSided
  Op n code name name-code code-name running as FL
import DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Finite.RightSided
  Op n code name name-code code-name running as FU

open import DenotationalSemantics.Model.World.History ℚ≥0ᵀ Op two-sided
  (λ o → operation′ o (‵ᵍ o) (‵ᵍ o) refl refl) public

------------------------------------------------------------------------
-- The reading at the interval is the pair of the readings

private
  ⟦⟧-pair  : ∀ s → proj₁ ⟦ s ⟧ᵗ ≡ (FL.⟦ s ⟧ᵗ , FU.⟦ s ⟧ᵗ)
  ⟦⟧-pair⁻ : ∀ s → proj₁ ⟦ s ⟧⁻ ≡ (FL.⟦ s ⟧⁻ , FU.⟦ s ⟧⁻)

  ⟦⟧-pair ε               = refl
  ⟦⟧-pair (operation o s) =
    cong (λ (a , b) → (‵ᵍ o ·ᵍ a , ‵ᵍ o ·ᵍ b)) (⟦⟧-pair s)
  ⟦⟧-pair (delay d s)     =
    cong (λ (a , b) → (waitᴸ ∣ d ∣⁺ ·ᵍ a , waitᵁ ∣ d ∣⁺ ·ᵍ b)) (⟦⟧-pair⁻ s)

  ⟦⟧-pair⁻ ε⁻               = refl
  ⟦⟧-pair⁻ (operation⁻ o s) =
    cong (λ (a , b) → (‵ᵍ o ·ᵍ a , ‵ᵍ o ·ᵍ b)) (⟦⟧-pair s)

-- so accessibility asks every exact word of the one run to fit a word
-- of each endpoint

reaches⇔ : ∀ {L U c w w'}
         → w ⊑ʰ[ ((L , U) , c) ] w'
         ⇔ (Σ[ s ∈ Trace ] w ∙ s ≡ w'
              × runᴸ (events s) ≾ ⟦ expr L ⟧ × runᴸ (events s) ≾ ⟦ expr U ⟧)
reaches⇔ {L} {U} {c} = mk⇔
  (λ (mkʰ s e (pL , pU)) →
     s , e ,
     Equivalence.to (FL.admits⇔ L s) (subst (_≾ᴳ L) (cong proj₁ (⟦⟧-pair s)) pL) ,
     Equivalence.to (FU.admits⇔ U s) (subst (_≾ᴳ U) (cong proj₂ (⟦⟧-pair s)) pU))
  (λ (s , e , qL , qU) →
     mkʰ s e
       (subst (_≾ᴳ L) (sym (cong proj₁ (⟦⟧-pair s))) (Equivalence.from (FL.admits⇔ L s) qL) ,
        subst (_≾ᴳ U) (sym (cong proj₂ (⟦⟧-pair s))) (Equivalence.from (FU.admits⇔ U s) qU)))
