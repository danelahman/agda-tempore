------------------------------------------------------------------------
-- Worked instances of at-most counts, at the sensor node.            --
--                                                                    --
-- A quota on each of `read`, `write` and `send`. A larger quota is   --
-- weaker, `unlimited` lifts one quota and keeps the others, and a    --
-- quota on one operation implies nothing about another. Every        --
-- ordering is established by the decision procedure of the grade,    --
-- and every computation by reduction.                                --
------------------------------------------------------------------------

module Grades.Examples.Worked.Counts.AtMost where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Grades.Examples.Worked.Counts.Index using (Quota; ⟪_,_,_⟫ᵐ)

import Grades.Examples.Counts.AtMost as AtMost

open AtMost using (at-most-counts; upto; unlimited)

open AtMost using (_≾ᵛ_; _≾ᵛ?_; _·ᵛ_; _⊔ᵛ_; uᵛ; ⊤ᵛ)

holds : {c d : Quota} {p : True (c ≾ᵛ? d)} → c ≾ᵛ d
holds {p = p} = toWitness p

fails : {c d : Quota} {p : False (c ≾ᵛ? d)} → ¬ (c ≾ᵛ d)
fails {p = p} = toWitnessFalse p

-- `unlimited` leaves too little of a coordinate for the implicit
-- arguments to be found, so the grades are given explicitly where it
-- appears

holdsᵉ : (c d : Quota) {p : True (c ≾ᵛ? d)} → c ≾ᵛ d
holdsᵉ c d {p} = toWitness p

failsᵉ : (c d : Quota) {p : False (c ≾ᵛ? d)} → ¬ (c ≾ᵛ d)
failsᵉ c d {p} = toWitnessFalse p

-- one reading and two transmissions fit a limit of two of each, with
-- writes unrestricted

within-limit : ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ ≾ᵛ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ
within-limit = holdsᵉ ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ

-- a third transmission does not

over-limit : ¬ (⟪ upto 1 , upto 0 , upto 3 ⟫ᵐ ≾ᵛ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ)
over-limit = failsᵉ ⟪ upto 1 , upto 0 , upto 3 ⟫ᵐ ⟪ upto 2 , unlimited , upto 2 ⟫ᵐ

-- two readings and one transmission are incomparable: each quota
-- exceeds the other on one counter

reads-vs-sends : ¬ (⟪ upto 2 , upto 0 , upto 0 ⟫ᵐ ≾ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
reads-vs-sends = fails

sends-vs-reads : ¬ (⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ≾ᵛ ⟪ upto 2 , upto 0 , upto 0 ⟫ᵐ)
sends-vs-reads = fails

-- sequencing adds the quotas, `unlimited` absorbing

sequenced : ⟪ upto 1 , upto 0 , upto 1 ⟫ᵐ ·ᵛ ⟪ upto 1 , unlimited , upto 0 ⟫ᵐ
          ≡ ⟪ upto 2 , unlimited , upto 1 ⟫ᵐ
sequenced = refl

-- the join takes the greater quota on each counter, so it can exceed
-- both grades together

joined : ⟪ upto 2 , upto 0 , upto 0 ⟫ᵐ ⊔ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ
       ≡ ⟪ upto 2 , upto 0 , upto 1 ⟫ᵐ
joined = refl

-- the unit is least and `unlimited` everywhere is greatest

none-least : uᵛ ≾ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ
none-least = holds

unlimited-greatest : ⟪ upto 5 , unlimited , upto 9 ⟫ᵐ ≾ᵛ ⊤ᵛ
unlimited-greatest = holdsᵉ ⟪ upto 5 , unlimited , upto 9 ⟫ᵐ ⊤ᵛ
