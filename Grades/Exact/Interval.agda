------------------------------------------------------------------------
-- Interval grades from a lower and an upper grade of sets of runs.   --
--                                                                    --
-- Let a lower and an upper grade each denote sets of exact words,    --
-- their orders below the ∀∃ lift (`Exact.Lift`), the unit holding    --
-- the empty word, sequencing the concatenations, and a delay the     --
-- strict wait of its length. A pair `(L , U)` is consistent when     --
-- some exact word fits a word of each,                               --
--                                                                    --
--   Σ[ x ] (Σ[ y ∈ ⟦ L ⟧ ] x ⊑ y) × (Σ[ z ∈ ⟦ U ⟧ ] x ⊑ z)           --
--                                                                    --
-- Consistency is closed upward, holds of the unit and of every       --
-- delay, and words concatenate; so consistent pairs are a sub-grade  --
-- of the product (`Grades.Upward`). A run of operations and delays   --
-- whose hulls (`Exact.Hull`) lie below the endpoints witnesses it.   --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes
open import Grades.Base using (Grade)
import Grades.Exact.Base as Base
import Grades.Exact.Lift as Lift
import Data.List.Base

module Grades.Exact.Interval
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (Lᵍ Uᵍ : Grade D)
  (⟦_⟧ˡ : Grade.Carrier Lᵍ → Lift.Lang T Op n code code-injective)
  (⟦_⟧ᵘ : Grade.Carrier Uᵍ → Lift.Lang T Op n code code-injective)
  (soundˡ : ∀ {c d} → Grade._≾_ Lᵍ c d → Lift._≾_ T Op n code code-injective ⟦ c ⟧ˡ ⟦ d ⟧ˡ)
  (soundᵘ : ∀ {c d} → Grade._≾_ Uᵍ c d → Lift._≾_ T Op n code code-injective ⟦ c ⟧ᵘ ⟦ d ⟧ᵘ)
  (unitˡ : ⟦ Grade.𝟏 Lᵍ ⟧ˡ Data.List.Base.[])
  (unitᵘ : ⟦ Grade.𝟏 Uᵍ ⟧ᵘ Data.List.Base.[])
  (seqˡ : ∀ {c d x y} → ⟦ c ⟧ˡ x → ⟦ d ⟧ˡ y → ⟦ Grade._·_ Lᵍ c d ⟧ˡ (x Data.List.Base.++ y))
  (seqᵘ : ∀ {c d x y} → ⟦ c ⟧ᵘ x → ⟦ d ⟧ᵘ y → ⟦ Grade._·_ Uᵍ c d ⟧ᵘ (x Data.List.Base.++ y))
  (delayˡ : ∀ τ → ⟦ Grade.ι Lᵍ τ ⟧ˡ (Base.idle T Op n code code-injective τ))
  (delayᵘ : ∀ τ → ⟦ Grade.ι Uᵍ τ ⟧ᵘ (Base.idle T Op n code code-injective τ)) where

open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Upward using (Upward; _∣ᵍ_; _∣ʰ_)

open import Grades.Exact.Base T Op n code code-injective using (Word; op; idle)
open import Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-refl; ⊑-trans)
open import Grades.Exact.Lift T Op n code code-injective
  using (Lang; ⊑-++) renaming (_≾_ to _≾ᴸ_)
open import Grades.Exact.Hull T Op n code code-injective running
  using (Run; perform; delay; runᴸ; hullᴸ; hullᵁ; run⊆hullᴸ; run⊆hullᵁ) public
open import Grades.Exact.Expression T Op n code code-injective running using (⟦_⟧)
open RunningTimes.RunningTimes running using (rt-inhabited⁺)

------------------------------------------------------------------------
-- Consistency

-- a word fitting a word of a set

Fits : Word → Lang → Set
Fits x X = Σ[ y ∈ Word ] X y × x ⊑ y

Consistent : Grade.Carrier Lᵍ × Grade.Carrier Uᵍ → Set
Consistent (L , U) = Σ[ x ∈ Word ] Fits x ⟦ L ⟧ˡ × Fits x ⟦ U ⟧ᵘ

fits-up : ∀ {x X Y} → X ≾ᴸ Y → Fits x X → Fits x Y
fits-up le (y , y∈ , xy) with le y y∈
... | z , z∈ , yz = z , z∈ , ⊑-trans xy yz

fits-∈ : ∀ {x} {X : Lang} → X x → Fits x X
fits-∈ {x} x∈ = x , x∈ , ⊑-refl

private
  fits-·ˡ : ∀ {x x′ c d} → Fits x ⟦ c ⟧ˡ → Fits x′ ⟦ d ⟧ˡ → Fits (x ++ x′) ⟦ Grade._·_ Lᵍ c d ⟧ˡ
  fits-·ˡ (y , y∈ , xy) (y′ , y′∈ , xy′) = y ++ y′ , seqˡ y∈ y′∈ , ⊑-++ xy xy′

  fits-·ᵘ : ∀ {x x′ c d} → Fits x ⟦ c ⟧ᵘ → Fits x′ ⟦ d ⟧ᵘ → Fits (x ++ x′) ⟦ Grade._·_ Uᵍ c d ⟧ᵘ
  fits-·ᵘ (y , y∈ , xy) (y′ , y′∈ , xy′) = y ++ y′ , seqᵘ y∈ y′∈ , ⊑-++ xy xy′

consistent : Upward (Lᵍ ×ᵍ Uᵍ) Consistent
consistent = record
  { up       = λ (le , le′) (x , fl , fu) → x , fits-up (soundˡ le) fl , fits-up (soundᵘ le′) fu
  ; P-𝟏      = [] , fits-∈ unitˡ , fits-∈ unitᵘ
  ; P-·      = λ (x , fl , fu) (x′ , fl′ , fu′) → x ++ x′ , fits-·ˡ fl fl′ , fits-·ᵘ fu fu′
  ; P-ι = λ τ → idle τ , fits-∈ (delayˡ τ) , fits-∈ (delayᵘ τ)
  }

intervalᵍ : Grade D
intervalᵍ = (Lᵍ ×ᵍ Uᵍ) ∣ᵍ consistent

-- its hints, from those of the ends

intervalʰ : GradeHints Lᵍ → GradeHints Uᵍ → GradeHints intervalᵍ
intervalʰ Hˡ Hᵘ = (Hˡ ×ʰ Hᵘ) ∣ʰ consistent

------------------------------------------------------------------------
-- Consistency witnessed by a run

-- a word of a run of operations and delays, each operation running for
-- a time it admits

word : Run → Word
word []              = []
word (perform o ∷ r) = op o (proj₁ (rt-inhabited⁺ o)) ∷ word r
word (delay τ ∷ r)   = idle τ ++ word r

word-∈ : ∀ r → runᴸ r (word r)
word-∈ []              = refl
word-∈ (perform o ∷ r) =
  op o _ ∷ [] , word r , refl ,
  (o , proj₁ (rt-inhabited⁺ o) , x∈⁅x⁆ (code o) , proj₂ (rt-inhabited⁺ o) , refl) , word-∈ r
word-∈ (delay τ ∷ r)   = idle τ , word r , refl , refl , word-∈ r

run-consistent : ∀ r L U → ⟦ hullᴸ r ⟧ ≾ᴸ ⟦ L ⟧ˡ → ⟦ hullᵁ r ⟧ ≾ᴸ ⟦ U ⟧ᵘ → Consistent (L , U)
run-consistent r L U l u =
  word r , fits-up l (fits-∈ (run⊆hullᴸ r _ (word-∈ r))) ,
           fits-up u (fits-∈ (run⊆hullᵁ r _ (word-∈ r)))
