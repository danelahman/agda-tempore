------------------------------------------------------------------------
-- Worked instances of the dense-time grades.                          --
--                                                                     --
-- Orderings between concrete grades, each discharged by the grade's    --
-- own decision procedure, so an example asserted the wrong way round   --
-- does not typecheck; products and joins, computed; and the embedding  --
-- of the discrete grades on concrete windows.                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Time.Dense.Examples where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade; _→ᵍ_)

open import Util.Equality

import Syntax.Grades.Example.Time.Dense.LeftSided as L
import Syntax.Grades.Example.Time.Dense.RightSided as R
import Syntax.Grades.Example.Time.Dense.TwoSided as T

import Syntax.Grades.Example.Time.TwoSidedWithInfinity as Discrete

open import Syntax.Grades.Example.Time.Dense.ExtendedRational
  using (↑_; ∞; _/_; #_; nonZero)

------------------------------------------------------------------------
-- Running a grade's decision procedure

module Decide (G : Grade) where
  open Grade G

  ≾! : {c d : Carrier} {p : True (c ≾? d)} → c ≾ d
  ≾! {p = p} = toWitness p

  ⋠! : {c d : Carrier} {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! {p = p} = toWitnessFalse p

open Decide L.dense-left-sided-intervals
  renaming (≾! to ≾ˡ!; ⋠! to ⋠ˡ!)
open Decide R.dense-right-sided-intervals
  renaming (≾! to ≾ʳ!; ⋠! to ⋠ʳ!)
open Decide T.dense-two-sided-intervals-with-∞
  renaming (≾! to ≾²!; ⋠! to ⋠²!)

------------------------------------------------------------------------
-- Left-sided: "at least q units"
--
-- A larger lower bound is the stronger claim, so it sits below.

-- "at least 1" is stronger than "at least 0.5"

lsi-weaken : L.[ # 1 ,+∞⟩ L.≾ₒ L.[ 1 / 2 ,+∞⟩
lsi-weaken = ≾ˡ!

lsi-no-strengthen : ¬ (L.[ 1 / 2 ,+∞⟩ L.≾ₒ L.[ # 1 ,+∞⟩)
lsi-no-strengthen = ⋠ˡ!

-- two half-unit delays make at least one unit

lsi-halves : L.[ 1 / 2 ,+∞⟩ L.·ₒ L.[ 1 / 2 ,+∞⟩ ≡ L.[ # 1 ,+∞⟩
lsi-halves = refl

-- the join keeps the smaller guarantee

lsi-join : L.[ 1 / 3 ,+∞⟩ L.⊔ₒ L.[ 1 / 2 ,+∞⟩ ≡ L.[ 1 / 3 ,+∞⟩
lsi-join = refl

------------------------------------------------------------------------
-- Right-sided: "at most q units", a real-time deadline

-- meeting a deadline of 2.5 units meets one of 3

rsi-weaken : R.[0, ↑ 5 / 2 ] R.≾ₒ R.[0, ↑ # 3 ]
rsi-weaken = ≾ʳ!

rsi-no-strengthen : ¬ (R.[0, ↑ # 3 ] R.≾ₒ R.[0, ↑ 5 / 2 ])
rsi-no-strengthen = ⋠ʳ!

-- every deadline is below having none

rsi-top : R.[0, ↑ 5 / 2 ] R.≾ₒ R.[0, ∞ ]
rsi-top = ≾ʳ! {R.[0, ↑ 5 / 2 ]} {R.[0, ∞ ]}

-- deadlines add: 1/2 + 2/3 = 7/6

rsi-add : R.[0, ↑ 1 / 2 ] R.·ₒ R.[0, ↑ 2 / 3 ] ≡ R.[0, ↑ 7 / 6 ]
rsi-add = refl

-- an unbounded computation stays unbounded

rsi-absorb : R.[0, ↑ 1 / 2 ] R.·ₒ R.[0, ∞ ] ≡ R.[0, ∞ ]
rsi-absorb = refl

------------------------------------------------------------------------
-- Two-sided: "between min and max units"
--
-- The order is containment: a wider window is weaker.

tsi-weaken : T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1 / 2 , ↑ 5 / 2 ]
tsi-weaken = ≾²!

tsi-no-strengthen : ¬ (T.[ 1 / 2 , ↑ 5 / 2 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ])
tsi-no-strengthen = ⋠²!

-- overlapping windows are incomparable

tsi-incomparable₁ : ¬ (T.[ 1 / 2 , ↑ # 1 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ])
tsi-incomparable₁ = ⋠²!

tsi-incomparable₂ : ¬ (T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1 / 2 , ↑ # 1 ])
tsi-incomparable₂ = ⋠²!

-- and their join is the smallest window containing both

tsi-join : T.[ 1 / 2 , ↑ # 1 ] T.⊔ᵢ T.[ # 1 , ↑ # 2 ] ≡ T.[ 1 / 2 , ↑ # 2 ]
tsi-join = refl

-- a half-unit delay followed by a task of 1 to 2 units

tsi-seq : T.[ 1 / 2 , ↑ 1 / 2 ] T.·ᵢ T.[ # 1 , ↑ # 2 ] ≡ T.[ 3 / 2 , ↑ 5 / 2 ]
tsi-seq = refl

-- one time step is two half-unit delays

tsi-tick : Grade.of-nat T.dense-two-sided-intervals-with-∞ 1
         ≡ T.[ 1 / 2 , ↑ 1 / 2 ] T.·ᵢ T.[ 1 / 2 , ↑ 1 / 2 ]
tsi-tick = refl

------------------------------------------------------------------------
-- The discrete windows, read in dense time

tsi-embed : _→ᵍ_.map T.two-sided→dense Discrete.[ 1 , Discrete.↑ 2 ]
          ≡ T.[ # 1 , ↑ # 2 ]
tsi-embed = refl

tsi-embed-∞ : _→ᵍ_.map T.two-sided→dense Discrete.[ 3 , Discrete.∞ ]
            ≡ T.[ # 3 , ∞ ]
tsi-embed-∞ = refl

-- a dense window strictly inside the image of a discrete one

tsi-inside : T.[ 1 / 2 , ↑ 3 / 2 ]
               T.≾ᵢ _→ᵍ_.map T.two-sided→dense Discrete.[ 0 , Discrete.↑ 2 ]
tsi-inside = ≾²!
