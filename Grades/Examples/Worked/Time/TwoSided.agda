------------------------------------------------------------------------
-- Worked instances of two-sided intervals: both bounds at once.      --
--                                                                    --
-- `i₁ ≾ i₂` is `min i₂ ≤ min i₁ × max i₁ ≤∞ max i₂`, containment,    --
-- the two halves being the two one-sided orders; weakening enlarges  --
-- the window at both ends. An upper endpoint `∞` imposes no upper    --
-- bound.                                                             --
--                                                                    --
-- The `uplink` run of the sensor node (read, idle two ticks, send)   --
-- lies in the window `[ 7 , ↑ 9 ]` under `opTime`.                   --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.TwoSided where

open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Time.ExtendedNat using (↑_; ∞)

open import Grades.Examples.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_]; ]_,_]; [_,_[; ]_,_[; eqᵢ; two-sided-intervals-with-∞)
  renaming (_·ᵢ_ to _·²_; _≾ᵢ_ to _≾²_; ⊤ᵢ to ⊤²)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

-- the window in which the uplink run lies

uplink-window : Interval∞
uplink-window = [ 7 , ↑ 9 ]

-- it is exactly `opTime read · [2,2] · opTime send`, as the run's shape
-- would suggest: 1 + 2 + 4 at the bottom, 1 + 2 + 6 at the top

uplink-window-computed :
  [ 1 , ↑ 1 ] ·² [ 2 , ↑ 2 ] ·² [ 4 , ↑ 6 ] ≡ uplink-window
uplink-window-computed = eqᵢ refl refl

-- a looser budget is a weaker grade

tsi-weaken : uplink-window ≾² [ 5 , ↑ 12 ]
tsi-weaken = ≤! , ≤!

tsi-no-tighten : ¬ ([ 5 , ↑ 12 ] ≾² uplink-window)
tsi-no-tighten rel = ≰! (proj₂ rel)

-- enlarging only one end is still weakening: the two halves are
-- independent

tsi-weaken-lo : uplink-window ≾² [ 5 , ↑ 9 ]
tsi-weaken-lo = ≤! , ≤!

tsi-weaken-hi : uplink-window ≾² [ 7 , ↑ 12 ]
tsi-weaken-hi = ≤! , ≤!

-- but the two windows below are incomparable: neither contains the
-- other, so a computation graded by one cannot be regraded to the other

tsi-incomparableˡ : ¬ ([ 7 , ↑ 9 ] ≾² [ 8 , ↑ 12 ])
tsi-incomparableˡ rel = ≰! (proj₁ rel)

tsi-incomparableʳ : ¬ ([ 8 , ↑ 12 ] ≾² [ 7 , ↑ 9 ])
tsi-incomparableʳ rel = ≰! (proj₂ rel)

-- the unit is the singleton window at 0, and it is minimal: only a
-- computation that takes no time at all can be graded by it

tsi-unit : Grade.𝟏 two-sided-intervals-with-∞ ≡ [ 0 , ↑ 0 ]
tsi-unit = eqᵢ refl refl

-- `n` time steps is the singleton window at `n`

tsi-ι : Grade.ι two-sided-intervals-with-∞ 7 ≡ [ 7 , ↑ 7 ]
tsi-ι = eqᵢ refl refl

------------------------------------------------------------------------
-- The infinite upper endpoint
--
-- `[ n , ∞ ]` is the largest grade with lower bound `n`, and `[ 0 , ∞ ]`
-- the largest of all, the greatest grade of this monoid. Unlike the
-- right-sided intervals' top it is not absorbing: its `min` endpoint is
-- the unit, so a run sequenced after it keeps its own lower bound.

-- dropping the upper bound is weakening

tsi-forget-max : uplink-window ≾² [ 7 , ∞ ]
tsi-forget-max = ≤! , _

-- and it cannot be recovered

tsi-no-recover : ¬ ([ 7 , ∞ ] ≾² uplink-window)
tsi-no-recover rel = proj₂ rel

-- ∞ absorbs in the upper endpoint: once a run is unbounded above, so is
-- everything that sequences it

tsi-seq : [ 1 , ↑ 1 ] ·² [ 6 , ∞ ] ≡ [ 7 , ∞ ]
tsi-seq = eqᵢ refl refl

-- the unbounded grades are still ordered by their lower bounds alone,
-- exactly as the left-sided intervals are

tsi-lower-bounds : [ 7 , ∞ ] ≾² [ 4 , ∞ ]
tsi-lower-bounds = ≤! , _

-- the greatest grade claims nothing at either end

tsi-top : ⊤² ≡ [ 0 , ∞ ]
tsi-top = eqᵢ refl refl

tsi-weaken-to-top : uplink-window ≾² ⊤²
tsi-weaken-to-top = ≤! , _

-- but it does not absorb: sequencing keeps the lower bound that follows

tsi-top-keeps-min : ⊤² ·² [ 6 , ∞ ] ≡ [ 6 , ∞ ]
tsi-top-keeps-min = eqᵢ refl refl

------------------------------------------------------------------------
-- Open ends are notation for the adjacent closed ones

tsi-open-lower : ] 1 , ↑ 3 ] ≡ [ 2 , ↑ 3 ]
tsi-open-lower = refl

tsi-open-upper : [ 1 , ↑ 3 [ ≡ [ 1 , ↑ 2 ]
tsi-open-upper = refl

tsi-open-both : ] 1 , ↑ 3 [ ≡ [ 2 , ↑ 2 ]
tsi-open-both = refl

tsi-open-∞ : [ 4 , ∞ [ ≡ [ 4 , ∞ ]
tsi-open-∞ = refl
