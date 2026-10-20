------------------------------------------------------------------------
-- Upper bounds on counts, by name: "at most `k` of each operation",  --
-- for every operation name.                                          --
--                                                                    --
-- A grade maps each name to an extended natural number, all but      --
-- finitely many names to one default bound: the indexed grade of the --
-- right-sided time intervals, with delays drawing on no counter      --
-- (`untimed`). Sequencing adds the counts name by name, the order is --
-- `≤` at each name and the join the maximum; the unit, every count   --
-- 0, is least, and `_·_` commutes.                                   --
--                                                                    --
-- Restricting to the names below `n` is a grade morphism onto the    --
-- `n`-counter quotas `at-most-counts n`.                             --
------------------------------------------------------------------------

module Syntax.Grades.Example.Counts.UpperBound where

open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate-cong)

open import Syntax.Durations using (Duration)
open import Syntax.Durations.Nat using (ℕᴰ)
open import Syntax.Grades
open import Syntax.Grades.Indexed using (ℕ-names; module Maps)
open Maps ℕ-names using (indexedᵍ; Map; _∣_; _!_; !-map₂; pointwise⁻)

open import Syntax.Grades.Example.Time.RightSided using (right-sided-intervals; 𝕀ᵣ)
open import Syntax.Grades.Example.Counts.AtMost using (at-most-counts)
import Syntax.Grades.Example.Counts.Power right-sided-intervals as P

open import Util.Equality

------------------------------------------------------------------------
-- A grade whose delays are the unit

untimed : {D : Duration} → Grade D → Grade D
untimed G = record G
  { of-dur      = λ _ → u
  ; of-dur-zero = ≃-refl
  ; of-dur-plus = ≃-sym (·-identityˡ u)
  }
  where open Grade G

------------------------------------------------------------------------
-- The grade

counts-upper-bound : Grade ℕᴰ
counts-upper-bound = indexedᵍ (untimed right-sided-intervals)

-- "at most `k` of the operation `s`", none of the others

upto : ℕ → 𝕀ᵣ → Map 𝕀ᵣ
upto s k = Grade.u right-sided-intervals ∣ ((s , k) ∷ [])

------------------------------------------------------------------------
-- Restriction to the first `n` names

module _ (n : ℕ) where

  private
    open Grade right-sided-intervals
      using () renaming (_·_ to _·ᴳ_; _⊔_ to _⊔ᴳ_; _≾_ to _≾ᴳ_)
    open Grade (at-most-counts n) using () renaming (_≃_ to _≃ᵛ_)

    ≡⇒≃ᵛ : ∀ {c d : Vec 𝕀ᵣ n} → c ≡ d → c ≃ᵛ d
    ≡⇒≃ᵛ refl = P.≾ᵛ-refl , P.≾ᵛ-refl

  restrict : Map 𝕀ᵣ → Vec 𝕀ᵣ n
  restrict f = tabulate (λ i → f ! toℕ i)

  restrictᵍ : counts-upper-bound →ᵍ at-most-counts n
  restrictᵍ = record
    { map          = restrict
    ; map-monotone = λ p → P.tabulate-≾ᵛ (λ i → pointwise⁻ _≾ᴳ_ p (toℕ i))
    ; map-u        = ≡⇒≃ᵛ (P.tabulate-uᵛ _ (λ _ → refl))
    ; map-·        = λ {f} {g} → ≡⇒≃ᵛ
        (trans (tabulate-cong (λ i → !-map₂ _·ᴳ_ f g (toℕ i)))
               (P.tabulate-·ᵛ (λ i → f ! toℕ i) (λ i → g ! toℕ i)))
    ; map-⊤        = ≡⇒≃ᵛ (P.lookup-ext (λ i → trans (lookup∘tabulate _ i) (sym (P.lookup-⊤ᵛ i))))
    ; map-⊔        = λ {f} {g} → ≡⇒≃ᵛ
        (trans (tabulate-cong (λ i → !-map₂ _⊔ᴳ_ f g (toℕ i)))
               (P.tabulate-⊔ᵛ (λ i → f ! toℕ i) (λ i → g ! toℕ i)))
    ; map-of-dur   = ≡⇒≃ᵛ (P.tabulate-uᵛ _ (λ _ → refl))
    }
