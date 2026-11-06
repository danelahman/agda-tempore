------------------------------------------------------------------------
-- Worked instances of at-most counts by name.                        --
--                                                                    --
-- The operations of the sensor node are the names 0, 1, 2 (`read`,   --
-- `write`, `send`); every other name is some other operation, all of --
-- them bounded by the default. A quota that names only `send` bounds --
-- every other operation by 0, and one with an unlimited default      --
-- leaves the unnamed operations free, so the default is compared as  --
-- well as the named entries. Restricted to the first three names, a  --
-- quota is the at-most quota of the node. Every ordering is          --
-- established by the decision procedure of the grade, and every      --
-- computation by reduction.                                          --
------------------------------------------------------------------------

module Grades.Examples.Worked.Counts.AtMost.ByName where

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import Grades.Examples.Worked.Counts.Index using (⟪_,_,_⟫ᵐ)
open import Grades.Examples.Counts.AtMost using (upto; unlimited)
open import Grades.Examples.Counts.AtMost.ByName using (at-most-counts-by-name; restrict)
open import Grades.Examples.Time.UpperBound using (𝕀ᵣ)

open Maps ℕ-names using (Map; _∣_; _!_)
open Grade at-most-counts-by-name using (_≾_; _≾?_; _·_; _⊔_; 𝟏; ⊤)

-- the operations as names

name : Op → ℕ
name read  = 0
name write = 1
name send  = 2

-- a quota: the bounds of the listed operations, and a default

quota : List (Op × 𝕀ᵣ) → 𝕀ᵣ → Map 𝕀ᵣ
quota es d = d ∣ entries es
  where
    entries : List (Op × 𝕀ᵣ) → List (ℕ × 𝕀ᵣ)
    entries []             = []
    entries ((o , k) ∷ es) = (name o , k) ∷ entries es

-- one listed operation and a default

single : Op → 𝕀ᵣ → 𝕀ᵣ → Map 𝕀ᵣ
single o k d = quota ((o , k) ∷ []) d

holds : (c d : Map 𝕀ᵣ) {p : True (c ≾? d)} → c ≾ d
holds c d {p} = toWitness p

fails : (c d : Map 𝕀ᵣ) {p : False (c ≾? d)} → ¬ (c ≾ d)
fails c d {p} = toWitnessFalse p

-- at most two transmissions and nothing else

two-sends : Map 𝕀ᵣ
two-sends = quota ((send , upto 2) ∷ []) (upto 0)

-- at most two transmissions, anything else

two-sends-free : Map 𝕀ᵣ
two-sends-free = quota ((send , upto 2) ∷ []) unlimited

-- a reading and a transmission fit two transmissions with the rest
-- free, but not two transmissions alone

read-send : Map 𝕀ᵣ
read-send = quota ((read , upto 1) ∷ (send , upto 1) ∷ []) (upto 0)

fits-free : read-send ≾ two-sends-free
fits-free = holds read-send two-sends-free

not-alone : ¬ (read-send ≾ two-sends)
not-alone = fails read-send two-sends

-- the defaults are compared: a free default is not below a zero one,
-- though the entries agree

free-not-below : ¬ (two-sends-free ≾ two-sends)
free-not-below = fails two-sends-free two-sends

zero-below : two-sends ≾ two-sends-free
zero-below = holds two-sends two-sends-free

-- sequencing adds the counts name by name, joining takes the greater

sequenced-send : (read-send · two-sends) ! name send ≡ upto 3
sequenced-send = refl

sequenced-other : (read-send · two-sends-free) ! 7 ≡ unlimited
sequenced-other = refl

joined-read : (read-send ⊔ two-sends) ! name read ≡ upto 1
joined-read = refl

-- the unit is least, unlimited everywhere greatest

none-least : 𝟏 ≾ read-send
none-least = holds 𝟏 read-send

all-greatest : two-sends-free ≾ ⊤
all-greatest = holds two-sends-free ⊤

-- restricted to the node's three operations, a quota is an at-most
-- quota

restricted : restrict 3 read-send ≡ ⟪ upto 1 , upto 0 , upto 1 ⟫ᵐ
restricted = refl

restricted-free : restrict 3 two-sends-free ≡ ⟪ unlimited , unlimited , upto 2 ⟫ᵐ
restricted-free = refl
