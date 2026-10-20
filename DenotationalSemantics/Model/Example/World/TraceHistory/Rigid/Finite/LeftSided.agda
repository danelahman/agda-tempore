------------------------------------------------------------------------
-- A trace-history Kripke frame for the rigid timed finite-expression --
-- grades as lower bounds.                                            --
--                                                                    --
-- Worlds are timed traces. A grade `L` reaches the histories         --
-- extending the current one by a continuation whose reading is below --
-- `L` (`World.History`):                                             --
--                                                                    --
--   w ⊑ʰ[ L ] w'   iff   Σ[ s ] w ∙ s ≡ w'  and  ⟦ s ⟧ ≾ L            --
--                                                                    --
-- The reading of a trace is the hull of the run it records, so by    --
-- the invisibility of the hull this is the reading the order gives:  --
-- every exact word of the run fits a word of `L`.                    --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Finite.LeftSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades.Traces.Base ℚ≥0ᵀ Op
  using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; _∙_; ∣_∣⁺)

open import Syntax.Grades.Example.Traces.Rigid.Finite.LeftSided Op n code name name-code code-name running
  using (left-sided; Instance; lower; at-least′; Proper′; expr; _≾ᴳ_; _≾ᵉ?_; decided; by-reader; ‵_; ⟦_⟧)
  renaming (_·_ to _·ᵉ_; ε to εᵉ; str to strᵉ)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Rigid.Finite.Base
  Op n code name name-code code-name running
  using (‵ᵍ; events; events⁻; code-injective)

open import Syntax.Grades.Exact.Lift ℚ≥0ᵀ Op n code code-injective using (_≾_)
open import Syntax.Grades.Exact.Hull ℚ≥0ᵀ Op n code code-injective running
  using (runᴸ; hullᴸ; hull-lower; at-least)

open import DenotationalSemantics.Model.World.History ℚ≥0ᵀ Op left-sided ‵ᵍ public

------------------------------------------------------------------------
-- The reading of a trace is the hull of its run

private
  wait-hull : ∀ τ c → expr (at-least′ τ c) ≡ at-least τ c
  wait-hull τ (yes _) = refl
  wait-hull τ (no _)  = refl

  hull-⟦⟧  : ∀ s → expr ⟦ s ⟧ᵗ ≡ hullᴸ (events s)
  hull-⟦⟧⁻ : ∀ s → expr ⟦ s ⟧⁻ ≡ hullᴸ (events⁻ s)

  hull-⟦⟧ ε               = refl
  hull-⟦⟧ (operation o s) = cong (‵ o ·ᵉ_) (hull-⟦⟧ s)
  hull-⟦⟧ (delay d s)     = cong₂ _·ᵉ_ (wait-hull ∣ d ∣⁺ _) (hull-⟦⟧⁻ s)

  hull-⟦⟧⁻ ε⁻               = refl
  hull-⟦⟧⁻ (operation⁻ o s) = cong (‵ o ·ᵉ_) (hull-⟦⟧ s)

-- a grade admits a continuation iff every exact word of its run fits
-- a word of the grade

admits⇔ : ∀ (L : Proper′ lower) s → ⟦ s ⟧ᵗ ≾ᴳ L ⇔ runᴸ (events s) ≾ ⟦ expr L ⟧
admits⇔ L s = mk⇔
  (λ p → proj₂ (hull-lower (events s) (expr L))
           (subst (λ e → ⟦ e ⟧ ≾ ⟦ expr L ⟧) (hull-⟦⟧ s)
                  (toWitness {a? = ⟦ s ⟧ᵗ ≾ᵉ? L} (by-reader p))))
  (λ q → decided (fromWitness {a? = ⟦ s ⟧ᵗ ≾ᵉ? L}
           (subst (λ e → ⟦ e ⟧ ≾ ⟦ expr L ⟧) (sym (hull-⟦⟧ s))
                  (proj₁ (hull-lower (events s) (expr L)) q))))

-- so accessibility is the reading the order gives

reaches⇔ : ∀ {L w w'}
         → w ⊑ʰ[ L ] w' ⇔ (Σ[ s ∈ Trace ] w ∙ s ≡ w' × runᴸ (events s) ≾ ⟦ expr L ⟧)
reaches⇔ {L} = mk⇔
  (λ (mkʰ s e p) → s , e , Equivalence.to (admits⇔ L s) p)
  (λ (s , e , q) → mkʰ s e (Equivalence.from (admits⇔ L s) q))
