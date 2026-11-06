------------------------------------------------------------------------
-- Worked instances of intervals: both bounds at once.                --
--                                                                    --
-- `i₁ ≾ i₂` is `min i₂ ≤ min i₁ × max i₁ ≤∞ max i₂`, containment,    --
-- the two halves being the two one-sided orders; weakening enlarges  --
-- the window at both ends. An upper endpoint `∞` imposes no upper    --
-- bound.                                                             --
--                                                                    --
-- The `uplink` run of the sensor node (read, idle two ticks, send)   --
-- lies in the window `[ 7 , ↑ 9 ]` under `opTime`.                   --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Interval where

open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Time.ExtendedNat using (↑_; ∞)

open import Grades.Examples.Time.Interval
  using (Interval∞; [_,_]; ]_,_]; [_,_[; ]_,_[; eqᵢ; interval)
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

-- a wider interval is a weaker grade

interval-weaken : uplink-window ≾² [ 5 , ↑ 12 ]
interval-weaken = ≤! , ≤!

interval-no-tighten : ¬ ([ 5 , ↑ 12 ] ≾² uplink-window)
interval-no-tighten rel = ≰! (proj₂ rel)

-- enlarging only one end is still weakening: the two halves are
-- independent

interval-weaken-lo : uplink-window ≾² [ 5 , ↑ 9 ]
interval-weaken-lo = ≤! , ≤!

interval-weaken-hi : uplink-window ≾² [ 7 , ↑ 12 ]
interval-weaken-hi = ≤! , ≤!

-- but the two windows below are incomparable: neither contains the
-- other, so a computation graded by one cannot be regraded to the other

interval-incomparableˡ : ¬ ([ 7 , ↑ 9 ] ≾² [ 8 , ↑ 12 ])
interval-incomparableˡ rel = ≰! (proj₁ rel)

interval-incomparableʳ : ¬ ([ 8 , ↑ 12 ] ≾² [ 7 , ↑ 9 ])
interval-incomparableʳ rel = ≰! (proj₂ rel)

-- the unit is the singleton window at 0, and it is minimal: only a
-- computation that takes no time at all can be graded by it

interval-unit : Grade.𝟏 interval ≡ [ 0 , ↑ 0 ]
interval-unit = eqᵢ refl refl

-- `n` time steps is the singleton window at `n`

interval-ι : Grade.ι interval 7 ≡ [ 7 , ↑ 7 ]
interval-ι = eqᵢ refl refl

------------------------------------------------------------------------
-- The infinite upper endpoint
--
-- `[ n , ∞ ]` is the largest grade with lower bound `n`, and `[ 0 , ∞ ]`
-- the largest of all, the greatest grade of this monoid. Unlike the
-- upper bounds' top it is not absorbing: its `min` endpoint is
-- the unit, so a run sequenced after it keeps its own lower bound.

-- dropping the upper bound is weakening

interval-forget-max : uplink-window ≾² [ 7 , ∞ ]
interval-forget-max = ≤! , _

-- and it cannot be recovered

interval-no-recover : ¬ ([ 7 , ∞ ] ≾² uplink-window)
interval-no-recover rel = proj₂ rel

-- ∞ absorbs in the upper endpoint: once a run is unbounded above, so is
-- everything that sequences it

interval-seq : [ 1 , ↑ 1 ] ·² [ 6 , ∞ ] ≡ [ 7 , ∞ ]
interval-seq = eqᵢ refl refl

-- the unbounded grades are still ordered by their lower bounds alone,
-- exactly as the lower bounds are

interval-lower-bounds : [ 7 , ∞ ] ≾² [ 4 , ∞ ]
interval-lower-bounds = ≤! , _

-- the greatest grade claims nothing at either end

interval-top : ⊤² ≡ [ 0 , ∞ ]
interval-top = eqᵢ refl refl

interval-weaken-to-top : uplink-window ≾² ⊤²
interval-weaken-to-top = ≤! , _

-- but it does not absorb: sequencing keeps the lower bound that follows

interval-top-keeps-min : ⊤² ·² [ 6 , ∞ ] ≡ [ 6 , ∞ ]
interval-top-keeps-min = eqᵢ refl refl

------------------------------------------------------------------------
-- Open ends are notation for the adjacent closed ones

interval-open-lower : ] 1 , ↑ 3 ] ≡ [ 2 , ↑ 3 ]
interval-open-lower = refl

interval-open-upper : [ 1 , ↑ 3 [ ≡ [ 1 , ↑ 2 ]
interval-open-upper = refl

interval-open-both : ] 1 , ↑ 3 [ ≡ [ 2 , ↑ 2 ]
interval-open-both = refl

interval-open-∞ : [ 4 , ∞ [ ≡ [ 4 , ∞ ]
interval-open-∞ = refl
