------------------------------------------------------------------------
-- Worked instances of the interval grades.                            --
--                                                                     --
-- The sensor node's `uplink` run -- read, idle two ticks, send -- is   --
-- the running example. Under `opTime` it takes between 7 and 9 ticks:  --
-- read 1, the idle 2, and send anywhere from 4 to 6. Each interval     --
-- grade records a different part of that fact:                         --
--                                                                     --
--   left-sided   [ 7 ,+∞⟩       "at least 7 ticks have passed"        --
--   right-sided  [0, ↑ 9 ]      "at most 9 ticks have passed"         --
--   two-sided    [ 7 , ↑ 9 ]    both bounds at once                    --
--                                                                     --
-- Both upper endpoints range over the extended naturals, so `[0, ∞ ]`  --
-- and `[ 7 , ∞ ]` impose no upper bound at all.                        --
--                                                                     --
-- In each case `_·_` adds the endpoints, so sequencing two runs adds   --
-- their windows, and the order is *weakening*: a grade sits below the  --
-- grades that claim less than it does. Which way "less" points differs --
-- per grade, and that is what the examples below pin down. Each grade  --
-- also has a designated greatest element `⊤`, and the sections below   --
-- say which one it is.                                                 --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Time where

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Time.LeftSided
  using ([_,+∞⟩; left-sided-intervals)
  renaming (𝕀 to 𝕀ˡ; _·ₒ_ to _·ˡ_; uₒ to uˡ; _≾ₒ_ to _≾ˡ_)

open import Syntax.Grades.Example.Time.RightSided
  using ([0,_]; ℕ∞; ↑_; ∞; right-sided-intervals)
  renaming (𝕀ᵣ to 𝕀ʳ; _·ₒ_ to _·ʳ_; uₒ to uʳ; _≾ₒ_ to _≾ʳ_; ⊤ₒ to ⊤ʳ)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_,_]; eqᵢ; two-sided-intervals-with-∞)
  renaming (_·ᵢ_ to _·²_; _≾ᵢ_ to _≾²_; ⊤ᵢ to ⊤²)

------------------------------------------------------------------------
-- Discharging the numeric side conditions
--
-- Every interval fact below reduces to comparisons of natural numbers:
-- `≤!` runs `_≤?_` and `≰!` runs it the other way, so an example
-- asserted the wrong way round does not typecheck.

≤! : {m n : ℕ} {p : True (m ≤? n)} → m ≤ n
≤! {p = p} = toWitness p

≰! : {m n : ℕ} {p : False (m ≤? n)} → ¬ (m ≤ n)
≰! {p = p} = toWitnessFalse p

------------------------------------------------------------------------
-- Left-sided intervals: a lower bound on elapsed time
--
-- `[ m ,+∞⟩ ≾ [ n ,+∞⟩` is `n ≤ m`: a *larger* lower bound is the
-- stronger claim, so it sits below. Weakening forgets how much time is
-- known to have passed; it can never invent more.

uplink-lo : 𝕀ˡ
uplink-lo = [ 7 ,+∞⟩

-- "at least 7" is a stronger guarantee than "at least 4", so it is the
-- smaller grade

lsi-weaken : [ 7 ,+∞⟩ ≾ˡ [ 4 ,+∞⟩
lsi-weaken = ≤!

-- and the other direction fails: nothing lets a grade claim more time
-- has passed than it recorded

lsi-no-strengthen : ¬ ([ 4 ,+∞⟩ ≾ˡ [ 7 ,+∞⟩)
lsi-no-strengthen = ≰!

-- sequencing adds the guarantees: read (≥1) then the rest of the uplink
-- (≥6) guarantees ≥7

lsi-seq : [ 1 ,+∞⟩ ·ˡ [ 6 ,+∞⟩ ≡ [ 7 ,+∞⟩
lsi-seq = refl

-- the unit claims nothing, and so is the largest grade

lsi-unit : uˡ ≡ [ 0 ,+∞⟩
lsi-unit = refl

lsi-unit-top : [ 7 ,+∞⟩ ≾ˡ uˡ
lsi-unit-top = ≤!

-- so the unit is the designated greatest grade here, and it is not
-- absorbing

lsi-top : Grade.⊤ left-sided-intervals ≡ uˡ
lsi-top = refl

-- `n` time steps, as a grade

lsi-of-nat : Grade.of-nat left-sided-intervals 7 ≡ [ 7 ,+∞⟩
lsi-of-nat = refl

------------------------------------------------------------------------
-- Right-sided intervals: an upper bound on elapsed time
--
-- The mirror image. `[0, m ] ≾ [0, n ]` is `m ≤ n`, so here it is the
-- *smaller* bound that is the stronger claim. A budget may always be
-- relaxed, never tightened.

uplink-hi : 𝕀ʳ
uplink-hi = [0, ↑ 9 ]

rsi-weaken : [0, ↑ 9 ] ≾ʳ [0, ↑ 12 ]
rsi-weaken = ≤!

rsi-no-tighten : ¬ ([0, ↑ 12 ] ≾ʳ [0, ↑ 9 ])
rsi-no-tighten = ≰!

rsi-seq : [0, ↑ 1 ] ·ʳ [0, ↑ 8 ] ≡ [0, ↑ 9 ]
rsi-seq = refl

-- here the unit is the *smallest* grade: "at most 0 ticks" is the
-- strongest budget there is

rsi-unit : uʳ ≡ [0, ↑ 0 ]
rsi-unit = refl

rsi-unit-bottom : uʳ ≾ʳ [0, ↑ 9 ]
rsi-unit-bottom = ≤!

-- and the greatest grade is `[0, ∞ ]`, which imposes no deadline; it is
-- absorbing, a run after an unbounded one being unbounded too

rsi-top : ⊤ʳ ≡ [0, ∞ ]
rsi-top = refl

rsi-weaken-to-top : [0, ↑ 9 ] ≾ʳ ⊤ʳ
rsi-weaken-to-top = _

rsi-top-absorbs : ⊤ʳ ·ʳ [0, ↑ 9 ] ≡ ⊤ʳ
rsi-top-absorbs = refl

rsi-of-nat : Grade.of-nat right-sided-intervals 9 ≡ [0, ↑ 9 ]
rsi-of-nat = refl

------------------------------------------------------------------------
-- Two-sided intervals: both bounds at once
--
-- `i₁ ≾ i₂` is `min i₂ ≤ min i₁ × max i₁ ≤∞ max i₂`: containment, the
-- two halves being the two one-sided orders, so weakening enlarges the
-- window at both ends. An `∞` upper endpoint imposes no upper bound.

-- the window the uplink run actually falls in

uplink-window : Interval∞
uplink-window = [ 7 , ↑ 9 , ≤! ]

-- it is exactly `opTime read · [2,2] · opTime send`, as the run's shape
-- would suggest: 1 + 2 + 4 at the bottom, 1 + 2 + 6 at the top

uplink-window-computed :
  [ 1 , ↑ 1 , ≤! ] ·² [ 2 , ↑ 2 , ≤! ] ·² [ 4 , ↑ 6 , ≤! ] ≡ uplink-window
uplink-window-computed = eqᵢ refl refl

-- a looser budget is a weaker grade

tsi-weaken : uplink-window ≾² [ 5 , ↑ 12 , ≤! ]
tsi-weaken = ≤! , ≤!

tsi-no-tighten : ¬ ([ 5 , ↑ 12 , ≤! ] ≾² uplink-window)
tsi-no-tighten rel = ≰! (proj₂ rel)

-- enlarging only one end is still weakening: the two halves are
-- independent

tsi-weaken-lo : uplink-window ≾² [ 5 , ↑ 9 , ≤! ]
tsi-weaken-lo = ≤! , ≤!

tsi-weaken-hi : uplink-window ≾² [ 7 , ↑ 12 , ≤! ]
tsi-weaken-hi = ≤! , ≤!

-- but the two windows below are incomparable: neither contains the
-- other, so a computation graded by one cannot be regraded to the other

tsi-incomparableˡ : ¬ ([ 7 , ↑ 9 , ≤! ] ≾² [ 8 , ↑ 12 , ≤! ])
tsi-incomparableˡ rel = ≰! (proj₁ rel)

tsi-incomparableʳ : ¬ ([ 8 , ↑ 12 , ≤! ] ≾² [ 7 , ↑ 9 , ≤! ])
tsi-incomparableʳ rel = ≰! (proj₂ rel)

-- the unit is the singleton window at 0, and it is minimal: only a
-- computation that takes no time at all can be graded by it

tsi-unit : Grade.u two-sided-intervals-with-∞ ≡ [ 0 , ↑ 0 , ≤! ]
tsi-unit = eqᵢ refl refl

-- `n` time steps is the singleton window at `n`

tsi-of-nat : Grade.of-nat two-sided-intervals-with-∞ 7 ≡ [ 7 , ↑ 7 , ≤! ]
tsi-of-nat = eqᵢ refl refl

------------------------------------------------------------------------
-- The infinite upper endpoint
--
-- `[ n , ∞ ]` is the largest grade with lower bound `n`, and `[ 0 , ∞ ]`
-- the largest of all -- the greatest grade of this monoid. Unlike the
-- right-sided intervals' top it is not absorbing: its `min` endpoint is
-- the unit, so a run sequenced after it keeps its own lower bound.

-- dropping the upper bound is weakening

tsi-forget-max : uplink-window ≾² [ 7 , ∞ , _ ]
tsi-forget-max = ≤! , _

-- and it cannot be recovered

tsi-no-recover : ¬ ([ 7 , ∞ , _ ] ≾² uplink-window)
tsi-no-recover rel = proj₂ rel

-- ∞ absorbs in the upper endpoint: once a run is unbounded above, so is
-- everything that sequences it

tsi-seq : [ 1 , ↑ 1 , ≤! ] ·² [ 6 , ∞ , _ ] ≡ [ 7 , ∞ , _ ]
tsi-seq = eqᵢ refl refl

-- the unbounded grades are still ordered by their lower bounds alone,
-- exactly as the left-sided intervals are

tsi-lower-bounds : [ 7 , ∞ , _ ] ≾² [ 4 , ∞ , _ ]
tsi-lower-bounds = ≤! , _

-- the greatest grade claims nothing at either end

tsi-top : ⊤² ≡ [ 0 , ∞ , _ ]
tsi-top = eqᵢ refl refl

tsi-weaken-to-top : uplink-window ≾² ⊤²
tsi-weaken-to-top = ≤! , _

-- but it does not absorb: sequencing keeps the lower bound that follows

tsi-top-keeps-min : ⊤² ·² [ 6 , ∞ , _ ] ≡ [ 6 , ∞ , _ ]
tsi-top-keeps-min = eqᵢ refl refl
