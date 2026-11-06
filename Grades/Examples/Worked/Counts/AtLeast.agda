------------------------------------------------------------------------
-- Worked instances of at-least counts, at the sensor node.           --
--                                                                    --
-- An at-least count for each of `read`, `write` and `send`. A        --
-- smaller demand is weaker, and demanding nothing is the greatest    --
-- grade. Every ordering is established by the decision procedure of  --
-- the grade, and every computation by reduction.                     --
------------------------------------------------------------------------

module Grades.Examples.Worked.Counts.AtLeast where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Grades.Examples.Worked.Counts.Index using (Certain; ⟪_,_,_⟫ˡ)

import Grades.Examples.Counts.AtLeast as AtLeast

open AtLeast using (_≾ᵛ_; _≾ᵛ?_; _·ᵛ_; _⊔ᵛ_; 𝟏ᵛ)

holds : {c d : Certain} {p : True (c ≾ᵛ? d)} → c ≾ᵛ d
holds {p = p} = toWitness p

fails : {c d : Certain} {p : False (c ≾ᵛ? d)} → ¬ (c ≾ᵛ d)
fails {p = p} = toWitnessFalse p

-- three readings certain is enough for a token asking for one

three-readings : ⟪ 3 , 0 , 0 ⟫ˡ ≾ᵛ ⟪ 1 , 0 , 0 ⟫ˡ
three-readings = holds

-- one reading is not enough for a token asking for three

one-reading : ¬ (⟪ 1 , 0 , 0 ⟫ˡ ≾ᵛ ⟪ 3 , 0 , 0 ⟫ˡ)
one-reading = fails

-- a certain transmission does not stand in for a reading

send-for-read : ¬ (⟪ 0 , 0 , 1 ⟫ˡ ≾ᵛ ⟪ 1 , 0 , 0 ⟫ˡ)
send-for-read = fails

-- sequencing adds the at-least counts; the join keeps only what both
-- make certain

sequenced : ⟪ 1 , 0 , 1 ⟫ˡ ·ᵛ ⟪ 2 , 1 , 0 ⟫ˡ ≡ ⟪ 3 , 1 , 1 ⟫ˡ
sequenced = refl

joined : ⟪ 3 , 1 , 0 ⟫ˡ ⊔ᵛ ⟪ 1 , 0 , 2 ⟫ˡ ≡ ⟪ 1 , 0 , 0 ⟫ˡ
joined = refl

-- demanding nothing is the greatest grade, and it is the unit

nothing-greatest : ⟪ 3 , 1 , 2 ⟫ˡ ≾ᵛ 𝟏ᵛ
nothing-greatest = holds
