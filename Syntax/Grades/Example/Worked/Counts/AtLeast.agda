------------------------------------------------------------------------
-- Worked instances of at-least counts, at the sensor node.             --
--
-- A certain count for each of `read`, `write`, `send`. A smaller demand --
-- is weaker, and demanding nothing is the greatest grade. Every         --
-- ordering is closed by the grade's own decision procedure, and every   --
-- computation by reduction, so a claim stated the wrong way round does  --
-- not typecheck.                                                        --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Counts.AtLeast where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Counts.Index using (Certain; ⟪_,_,_⟫ˡ)

import Syntax.Grades.Example.Counts.AtLeast as AtLeast

open AtLeast using (_≾ᵛ_; _≾ᵛ?_; _·ᵛ_; _⊔ᵛ_; uᵛ)

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

-- sequencing adds the certain counts; the join keeps only what both
-- make certain

sequenced : ⟪ 1 , 0 , 1 ⟫ˡ ·ᵛ ⟪ 2 , 1 , 0 ⟫ˡ ≡ ⟪ 3 , 1 , 1 ⟫ˡ
sequenced = refl

joined : ⟪ 3 , 1 , 0 ⟫ˡ ⊔ᵛ ⟪ 1 , 0 , 2 ⟫ˡ ≡ ⟪ 1 , 0 , 0 ⟫ˡ
joined = refl

-- demanding nothing is the greatest grade, and it is the unit

nothing-greatest : ⟪ 3 , 1 , 2 ⟫ˡ ≾ᵛ uᵛ
nothing-greatest = holds
