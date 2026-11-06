------------------------------------------------------------------------
-- A trace-history Kripke frame for the rigid timed finite-expression --
-- grades as upper bounds.                                            --
--                                                                    --
-- Worlds are timed traces. A grade `U` reaches the histories         --
-- extending the current one by a continuation whose reading is below --
-- `U` (`World.History`):                                             --
--                                                                    --
--   w ⊑ʰ[ U ] w'   iff   Σ[ s ] w ∙ s ≡ w'  and  ⟦ s ⟧ ≾ U           --
--                                                                    --
-- The reading of a trace is the hull of the run it records, so by    --
-- the invisibility of the hull this is the reading the order gives:  --
-- every exact word of the run fits a word of `U`.                    --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ)
import Grades.Traces.RunningTimes as RunningTimes

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.TimedRegex.Finite.UpperBound
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Grades.Traces.Base ℚ≥0ᵀ Op
  using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; _∙_)

open import Grades.Examples.Traces.TimedRegex.Finite.UpperBound Op n code name name-code code-name running
  using (upper-bound; Instance; upper; Proper′; expr; _≾ᴳ_; _≾ᵉ?_; decided; by-reader; ‵_; ⟦_⟧)
  renaming (_·_ to _·ᵉ_; ε to εᵉ; str to strᵉ)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.TimedRegex.Finite.Base
  Op n code name name-code code-name running
  using (‵ᵍ; events; events⁻; code-injective)

open import Grades.Exact.Lift ℚ≥0ᵀ Op n code code-injective using (_≾_)
open import Grades.Exact.Hull ℚ≥0ᵀ Op n code code-injective running
  using (runᴸ; hullᵁ; hull-upper)

open import MonomorphicCalculus.DenotationalSemantics.Model.World.History ℚ≥0ᵀ Op upper-bound ‵ᵍ public

------------------------------------------------------------------------
-- The reading of a trace is the hull of its run

private
  hull-⟦⟧  : ∀ s → expr ⟦ s ⟧ᵗ ≡ hullᵁ (events s)
  hull-⟦⟧⁻ : ∀ s → expr ⟦ s ⟧⁻ ≡ hullᵁ (events⁻ s)

  hull-⟦⟧ ε               = refl
  hull-⟦⟧ (operation o s) = cong (‵ o ·ᵉ_) (hull-⟦⟧ s)
  hull-⟦⟧ (delay d s)     = cong (_ ·ᵉ_) (hull-⟦⟧⁻ s)

  hull-⟦⟧⁻ ε⁻               = refl
  hull-⟦⟧⁻ (operation⁻ o s) = cong (‵ o ·ᵉ_) (hull-⟦⟧ s)

-- a grade admits a continuation iff every exact word of its run fits
-- a word of the grade

admits⇔ : ∀ (U : Proper′ upper) s → ⟦ s ⟧ᵗ ≾ᴳ U ⇔ runᴸ (events s) ≾ ⟦ expr U ⟧
admits⇔ U s = mk⇔
  (λ p → proj₂ (hull-upper (events s) (expr U))
           (subst (λ e → ⟦ e ⟧ ≾ ⟦ expr U ⟧) (hull-⟦⟧ s)
                  (toWitness {a? = ⟦ s ⟧ᵗ ≾ᵉ? U} (by-reader p))))
  (λ q → decided (fromWitness {a? = ⟦ s ⟧ᵗ ≾ᵉ? U}
           (subst (λ e → ⟦ e ⟧ ≾ ⟦ expr U ⟧) (sym (hull-⟦⟧ s))
                  (proj₁ (hull-upper (events s) (expr U)) q))))

-- so accessibility is the reading the order gives

reaches⇔ : ∀ {U w w'}
         → w ⊑ʰ[ U ] w' ⇔ (Σ[ s ∈ Trace ] w ∙ s ≡ w' × runᴸ (events s) ≾ ⟦ expr U ⟧)
reaches⇔ {U} = mk⇔
  (λ (mkʰ s e p) → s , e , Equivalence.to (admits⇔ U s) p)
  (λ (s , e , q) → mkʰ s e (Equivalence.from (admits⇔ U s) q))
