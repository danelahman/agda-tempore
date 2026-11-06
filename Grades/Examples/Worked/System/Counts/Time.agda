------------------------------------------------------------------------
-- Worked instance: a cost model does not preserve the join.          --
--                                                                    --
-- Each counter is weighted by its worst-case execution time, 1, 3    --
-- and 6 ticks. A write weighs 3 and a transmission 6, but their      --
-- join, one of each, weighs 9, more than either.                     --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Counts.Time where

open import Data.Vec.Base using (Vec; []; _∷_)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Grades.Examples.Worked.Counts.Index using (⟪_,_,_⟫ᵐ)

open import Grades.Examples.Counts.AtMost using (upto; _⊔ᵛ_)
open import Grades.Examples.System.Counts.Time using (module WeighRight)
open WeighRight using (weigh)
open import Grades.Examples.Time.UpperBound using (_⊔ₒ_)

slow : Vec _ 3
slow = 1 ∷ 3 ∷ 6 ∷ []

a-write : weigh slow ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ≡ upto 3
a-write = refl

a-send : weigh slow ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ≡ upto 6
a-send = refl

join-of-images : weigh slow ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ₒ weigh slow ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ
               ≡ upto 6
join-of-images = refl

image-of-join : weigh slow (⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
              ≡ upto 9
image-of-join = refl

join-not-preserved :
  ¬ (weigh slow (⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ᵛ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
     ≡ weigh slow ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⊔ₒ weigh slow ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ)
join-not-preserved ()
