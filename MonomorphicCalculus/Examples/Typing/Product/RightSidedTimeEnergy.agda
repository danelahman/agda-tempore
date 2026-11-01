------------------------------------------------------------------------
-- Typed example computations at upper bounds on time paired with an  --
-- energy budget.                                                     --
--                                                                    --
-- Effect grades and resource grades are both `([0, n ] , [0, e ])`,  --
-- "at most `n` time steps and at most `e` units of energy", and an   --
-- operation is graded by its worst-case time and the energy it       --
-- draws: read 1 and 1, write 3 and 2, send 6 and 5. Idling spends    --
-- time and draws no energy.                                          --
--                                                                    --
-- As a resource grade, `[ ([0, n ] , [0, e ]) ] A` is a calibration  --
-- that drifts with time and with use: claimable while at most `n`    --
-- steps have passed and at most `e` units have been drawn since      --
-- boxing. The same elapsed time can keep or lose it, according to    --
-- whether it was spent idling or working; both cases are shown       --
-- below.                                                             --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order   --
-- behave as at the upper bounds on time: a reading goes stale after  --
-- any activity, and a handler clause may discard its continuation.   --
--                                                                    --
-- Every claim is checked componentwise, `≤!` on the time and on the  --
-- energy; a refutation names the component that fails.               --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a        --
-- modality, `∷ A` a binding.                                         --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Product.RightSidedTimeEnergy where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Grades.Examples.Time.RightSided
  using (𝕀ᵣ; ↑_; 𝟏ₒ-least)
  renaming ([0,_] to ⌈0,_⌉)
open import Grades.Examples.Product.RightSidedTimeEnergy
  using (right-sided-time×energy)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; slow)
open import Grades.Examples.Worked.Operations.Footprint using (draws)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

-- every bound written below is finite

[0,_] : ℕ → 𝕀ᵣ
[0, n ] = ⌈0, ↑ n ⌉

------------------------------------------------------------------------
-- The operations, graded by worst-case time and the energy drawn

opTime : Op → 𝕀ᵣ × 𝕀ᵣ
opTime o = ([0, slow o ] , [0, draws o ])

open import MonomorphicCalculus.Examples.Typing.Core
  right-sided-time×energy opTime

------------------------------------------------------------------------
-- Effectful computations

sampling : [] ⊢ᶜ⦂ Reading ! ([0, 1 ] , [0, 1 ])
sampling =
  perform read ⋆                     -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
    (return here)

relaying : [] ⊢ᶜ⦂ unit ! ([0, 7 ] , [0, 6 ])
relaying =
  perform read ⋆                     -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
    (perform send here               -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ unit
      (return ⋆))

-- idling spends time and no energy

idling : [] ⊢ᶜ⦂ unit ! ([0, 5 ] , [0, 0 ])
idling = delay 5 (return ⋆)          -- ⟨ ([0, 5 ] , [0, 0 ]) ⟩

-- and a reading goes stale under it all the same, on the time
-- component

reading-stale-after-idling : ¬ (𝟏ᵣ ·ᵣ ιᵣ 1 ≾ᵣ 𝟏ᵣ)
reading-stale-after-idling (late , _) = ≰! late

------------------------------------------------------------------------
-- An energy budget
--
-- Thirty steps and twelve units.

budget : E
budget = ([0, 30 ] , [0, 12 ])

-- two uplinks, spaced by ten ticks of idling, fit it: the idling costs
-- time the budget has to spare, and no energy

spaced-uplinks : [] ⊢ᶜ⦂ unit ! budget
spaced-uplinks =
  coerce (≤! , ≤!)
    (perform read ⋆                  -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
      (perform send here             -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ unit
        (delay 10                    -- ⟨ ([0, 10 ] , [0, 0 ]) ⟩
          (perform read ⋆            -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
            (perform send here       -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ unit
              (return ⋆))))))

-- three uplinks back to back take less time than that and draw more
-- energy than the budget holds

three-uplinks-overdraw : ¬ (([0, 21 ] , [0, 18 ]) ≾ₑ budget)
three-uplinks-overdraw (_ , overdrawn) = ≰! overdrawn

------------------------------------------------------------------------
-- Conditional branching
--
-- The join is taken componentwise, so a conditional is charged its
-- slower branch's time and its hungrier branch's energy, even when no
-- single branch spends both.

branching : [] ∷ bool ∷ Reading ⊢ᶜ⦂ unit ! ([0, 8 ] , [0, 5 ])
branching =
  if eternal-var boolₑ (Tl-∷ Hd)
    `then coerce (≤! , ≤!) (perform send here (return ⋆))
    `else coerce (≤! , ≤!) (delay 8 (return ⋆))

------------------------------------------------------------------------
-- Unboxing: a calibration that drifts
--
-- Valid for ten steps and six units of energy.

calibration : R
calibration = ([0, 10 ] , [0, 6 ])

-- claimed after eight ticks of idling: eight steps, nothing drawn

claim-after-idling : [] ⊢ᶜ⦂ unit ! ([0, 14 ] , [0, 5 ])
claim-after-idling =
  box calibration (const reading 42) -- ∷ [ calibration ] Reading
    (delay 8                         -- ⟨ ([0, 8 ] , [0, 0 ]) ⟩
      (unbox (Tl-⟨⟩ Hd) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- claimed after an uplink: seven steps, and the six units exactly

claim-after-relaying : [] ⊢ᶜ⦂ unit ! ([0, 10 ] , [0, 8 ])
claim-after-relaying =
  box calibration (const reading 42) -- ∷ [ calibration ] Reading
    (perform read ⋆                  -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
      (perform send here             -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform write here (return ⋆)))))

-- eight steps spent working rather than idling (two readings and a
-- transmission) draw seven units, and the claim is refused

drained : ¬ (𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ calibration)
drained (_ , overdrawn) = ≰! overdrawn

-- and idling past ten steps drifts it, having drawn nothing

drifted : ¬ (𝟏ᵣ ·ᵣ ιᵣ 11 ≾ᵣ calibration)
drifted (late , _) = ≰! late

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢ᶜ⦂ Reading ! ([0, 1 ] , [0, 1 ])
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
      (return here)

-- a clause may drop its continuation: doing nothing meets every
-- deadline and every budget

nothing-fits : (op : Op) → (ε'' : E) → 𝟏ₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits op ε'' =
  𝟏ₒ-least (proj₁ (op-grade op ·ₑ ε'')) , 𝟏ₒ-least (proj₂ (op-grade op ·ₑ ε''))

-- the barrier `⊤ᵣ` has no deadline, so no clause may close over a
-- reading

reading-stale-at-⊤ : ¬ (𝟏ᵣ ·ᵣ ⊤ᵣ ≾ᵣ 𝟏ᵣ)
reading-stale-at-⊤ (() , _)

no-reporting : (op : Op) → (ε'' : E)
             → ¬ (𝟏ᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ 𝟏ᵣ)
no-reporting op ε'' bound =
  reading-stale-at-⊤
    (≾ᵣ-zero-productˡ {𝟏ᵣ ·ᵣ ⊤ᵣ} {op-grade op}
      (≾ᵣ-zero-productˡ {𝟏ᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op} {ε''} bound))
