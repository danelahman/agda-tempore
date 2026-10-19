------------------------------------------------------------------------
-- Intervals of a time domain, with open or closed ends, as grades.    --
--                                                                    --
-- A grade is an interval of durations, "between `lo` and `hi`", each  --
-- end open or closed and the upper one possibly absent. The order is  --
-- the order of the ends, a wider interval being weaker; sequencing    --
-- adds the ends, an end of a sum being open when an end summed is;   --
-- the join is the hull; and a delay by `τ` is the point `[τ, τ]`.     --
--                                                                    --
-- The laws hold over any time domain. In a dense one the order is     --
-- containment of the durations admitted and sequencing their          --
-- Minkowski sum (`Durations.Intervals.Dense`); that is the grade of    --
-- rational time, `Example.Time.Dense.TwoSided`.                      --
------------------------------------------------------------------------

open import Syntax.Durations

module Syntax.Grades.Example.Time.Intervals {D : Duration} (T : TimeDomain D) where

open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_,_)

open import Syntax.Grades

open import Util.Equality

open import Syntax.Durations.Intervals T public

-- the closure: the same lower end, and an upper end that only the
-- point zero or no bound absorbs

plusⁱ : (i : Interval) → Plus _⊕_ _⊆ⁱ_ i
plusⁱ i = plus (i⁺ i)
  (⊑-refl , ⊑ʰ-plusʰ (hi i))
  (+ˡ-inflate (lo i) (lo i) , plusʰ-iter {hi i} (◁⇒0⁺⊑ʰ {lo i} {hi i} (lo◁hi i)))
  (λ { (p , q) (_ , q') → p , plusʰ-least {hi i} q q' })
  (λ { (p , q) → p , plusʰ-indˡ {hi i} q })
  (λ { (p , q) → p , plusʰ-indʳ {hi i} q })

intervals : Grade D
intervals = record
  { Carrier         = Interval
  ; _·_             = _⊕_
  ; u               = 0ⁱ
  ; _≾_             = _⊆ⁱ_
  ; ⊤               = ⊤ⁱ
  ; _⊔_             = _∪ⁱ_
  ; of-dur          = pointⁱ
  ; ·-identityˡ     = ⊕-identityˡ
  ; ·-identityʳ     = ⊕-identityʳ
  ; ·-assoc         = ⊕-assoc
  ; ≾-refl          = λ {i} → ⊆ⁱ-refl {i}
  ; ≾-trans         = λ {i} {j} {k} → ⊆ⁱ-trans {i} {j} {k}
  ; ≾-antisym       = λ {i} {j} → ⊆ⁱ-antisym {i} {j}
  ; ≾-irrelevant    = λ {i} {j} → ⊆ⁱ-irrelevant {i} {j}
  ; _≾?_            = _⊆ⁱ?_
  ; ≾-⊤             = ⊆ⁱ-⊤
  ; ⊔-ubˡ           = ∪ⁱ-ubˡ
  ; ⊔-ubʳ           = ∪ⁱ-ubʳ
  ; ⊔-lub           = λ {i} {j} {k} → ∪ⁱ-lub {i} {j} {k}
  ; ·-monoˡ-≾       = λ {k} {i} {j} r → ⊕-mono {i} {j} {k} {k} r (⊆ⁱ-refl {k})
  ; ·-monoʳ-≾       = λ {k} {i} {j} r → ⊕-mono {k} {k} {i} {j} (⊆ⁱ-refl {k}) r
  ; ·-distribˡ-⊔-≾  = ⊕-distribˡ-∪ⁱ
  ; ·-distribʳ-⊔-≾  = ⊕-distribʳ-∪ⁱ
  ; ≾-zero-productˡ = λ {i} {j} → ⊆ⁱ-0ⁱ-sumˡ i j
  ; ≾-zero-productʳ = λ {i} {j} → ⊆ⁱ-0ⁱ-sumʳ i j
  ; of-dur-zero     = refl
  ; of-dur-plus     = λ {τ} {τ'} → pointⁱ-+ τ τ'
  ; u-least?        = nothing
  ; ·-comm?         = just ⊕-comm
  ; plus?           = λ i → just (plusⁱ i)
  }
