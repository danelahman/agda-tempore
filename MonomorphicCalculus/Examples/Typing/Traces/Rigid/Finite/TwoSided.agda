------------------------------------------------------------------------
-- Typed example computations at the rigid timed finite-expression    --
-- interval grade, in dense time.                                     --
--                                                                    --
-- A grade `[ L , U ]` pairs a guarantee with a bound, each a finite  --
-- expression over interval letters, that a common run fits. The      --
-- guarantee below demands a reading, then an undisturbed wait of at  --
-- least one unit, with anything before and after; the bound allows a --
-- reading and at most six units of anything after it. A box at this  --
-- grade may be unboxed after a reading and a wait of one unit; after --
-- a reading and a transmission instead it may not, the transmission  --
-- filling the wait the guarantee demands, though it stays within     --
-- the bound and within a guarantee asking only for a unit of         --
-- anything.                                                          --
--                                                                    --
-- Reading takes more than a quarter and at most half a unit, writing --
-- one to two units, sending two to four.                             --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Traces.Rigid.Finite.TwoSided where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using () renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.Product using (_×_; _,_)
open import Grades.Base using (module Grade)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ)
open import Grades.Examples.Time.Dense.TwoSided
  using (Interval; [_,_]; ]_,_]; ↑_; _/_; #_; _⊑?_; 0⁺; lo)
open import Grades.Traces.RunningTimes ℚ≥0ᵀ using (RunningTimes) renaming (fin to bounded)
open import Grades.Durations.Intervals.Dense ℚ≥0ᵀ using (_∈ⁱ?_)

open import Grades.Examples.Worked.Operations using (Op; read; write; send)

------------------------------------------------------------------------
-- The operations, coded, and their running times

code : Op → Fin 3
code read  = zero
code write = suc zero
code send  = suc (suc zero)

name : Fin 3 → Op
name zero             = read
name (suc zero)       = write
name (suc (suc zero)) = send

name-code : ∀ o → name (code o) ≡ o
name-code read  = refl
name-code write = refl
name-code send  = refl

code-name : ∀ c → code (name c) ≡ c
code-name zero             = refl
code-name (suc zero)       = refl
code-name (suc (suc zero)) = refl

rt : Op → Interval
rt read  = ] 1 / 4 , ↑ 1 / 2 ]
rt write = [ # 1 , ↑ # 2 ]
rt send  = [ # 2 , ↑ # 4 ]

running : RunningTimes Op
running = record
  { rt          = rt
  ; rt-bounded  = λ { read → bounded _ ; write → bounded _ ; send → bounded _ }
  ; rt-positive = λ { read  → toWitness {a? = 0⁺ ⊑? lo (rt read)} _
                    ; write → toWitness {a? = 0⁺ ⊑? lo (rt write)} _
                    ; send  → toWitness {a? = 0⁺ ⊑? lo (rt send)} _ }
  ; rt-inhabited = λ { read  → 1 / 2 , toWitness {a? = 1 / 2 ∈ⁱ? rt read} _
                     ; write → # 1 , toWitness {a? = # 1 ∈ⁱ? rt write} _
                     ; send  → # 2 , toWitness {a? = # 2 ∈ⁱ? rt send} _ }
  }

import Grades.Examples.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running as L
import Grades.Examples.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running as U
open import Grades.Examples.Traces.Rigid.Finite.TwoSided Op 3 code name name-code code-name running
  using (two-sided; operation; [_,_]⟨_⟩; perform; delay) renaming ([_,_] to [_,_]ᵍ)

open L using (Proper′; ‵_; _·_; ≥_; idle_; upper; lower)
open U using (≤_)

------------------------------------------------------------------------
-- The operations, graded by the operation at both endpoints

opTime : Op → Grade.Carrier two-sided
opTime = operation

open import MonomorphicCalculus.Examples.Typing.Core two-sided opTime

------------------------------------------------------------------------
-- The contracts

settling settling-busy : Proper′ lower
settling      = L.⌜ ≥ (# 0) · ‵ read · idle ≥ (# 1) · ≥ (# 0) ⌝
settling-busy = L.⌜ ≥ (# 0) · ‵ read · ≥ (# 1) · ≥ (# 0) ⌝

within-six : Proper′ upper
within-six = U.⌜ ‵ read · ≤ (# 6) ⌝

contract contract-busy : R
contract      = [ settling      , within-six ]ᵍ
contract-busy = [ settling-busy , within-six ]⟨ perform read ∷ᴸ delay (# 1) ∷ᴸ []ᴸ ⟩

------------------------------------------------------------------------
-- A box at the contract, opened after the wait

settled : [] ⊢C⦂ Unit ‼ _
settled =
  box contract (const 42)    -- ∷ [ contract ] Reading
    (perform read ⋆          -- ⟨ opTime read ⟩ ∷ Reading
      (delay (# 1)           -- ⟨ ι 1 ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) _ (<:ᵛ-refl _)
                             -- ∷ Reading
          (perform write here (return ⋆)))))

-- transmitting in place of waiting fills the wait the contract
-- demands: the box cannot be opened

stirred-run : R
stirred-run = 𝟏ᵣ ·ᵣ opTime read ·ᵣ opTime send

stirred : ¬ (stirred-run ≾ᵣ contract)
stirred (() , _)

-- the transmission stays within the bound, and gives the unit of a
-- guarantee that does not ask for an undisturbed wait

stirred-busy : stirred-run ≾ᵣ contract-busy
stirred-busy = _
