------------------------------------------------------------------------
-- Worked instances of the lattice grades.                            --
--                                                                    --
-- The two-point lattice `Low < High`, with the runs of the sensor    --
-- node graded by `touches`, and taint sets over `Fin 3`: orderings,  --
-- sequencing and the greatest grade, each established by the         --
-- decision procedure of the grade or by computation.                 --
------------------------------------------------------------------------

module Grades.Examples.Worked.Lattice where

open import Data.Fin.Base using (zero; suc)
open import Data.Vec.Base using ([]; _∷_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Durations using (Duration)
open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Lattice
  using (LowHigh; Low; High; two-point-levels; TaintSet; taint-sets;
         label; _∪ᵗ_)

open import Grades.Examples.Worked.Operations using (read; write; send)
open import Grades.Examples.Worked.Operations.Footprint using (touches)

------------------------------------------------------------------------
-- Checked orderings
--
-- Each runs the grade's own decision procedure, so an ordering
-- asserted the wrong way round does not typecheck.

module _ {D : Duration} {G : Grade D} where

  open Grade G

  ≾! : {c d : Carrier} {p : True (c ≾? d)} → c ≾ d
  ≾! {p = p} = toWitness p

  ⋠! : {c d : Carrier} {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! {p = p} = toWitnessFalse p

-- two points

module _ where

  open Grade (two-point-levels {ℕᴰ})

  -- a `Low` computation may be treated as `High`, not conversely

  low-⊑-high : Low ≾ High
  low-⊑-high = ≾! {G = two-point-levels {ℕᴰ}}

  high-⋢-low : ¬ (High ≾ Low)
  high-⋢-low = ⋠! {G = two-point-levels {ℕᴰ}}

  -- reading `High` data raises the label for the rest of the run

  read-up : High · Low ≡ High
  read-up = refl

  -- waiting does not

  idle : ι 5 · Low ≡ Low
  idle = refl

  -- at the sensor node, `logged` stays `Low` and `uplink`, which
  -- transmits, is `High`

  logged-low : touches read · touches write ≡ Low
  logged-low = refl

  uplink-high : touches read · ι 2 · touches send ≡ High
  uplink-high = refl

-- three taint labels: personal data, a key, the network

module _ where

  open Grade (taint-sets {ℕᴰ} 3)

  pii key net : TaintSet 3
  pii = label zero
  key = label (suc zero)
  net = label (suc (suc zero))

  pii-⊑-pii∪net : pii ≾ pii ∪ᵗ net
  pii-⊑-pii∪net = ≾! {G = taint-sets {ℕᴰ} 3}

  pii∪net-⋢-pii : ¬ (pii ∪ᵗ net ≾ pii)
  pii∪net-⋢-pii = ⋠! {G = taint-sets {ℕᴰ} 3}

  -- incomparable labels

  pii-⋢-key : ¬ (pii ≾ key)
  pii-⋢-key = ⋠! {G = taint-sets {ℕᴰ} 3}

  key-⋢-pii : ¬ (key ≾ pii)
  key-⋢-pii = ⋠! {G = taint-sets {ℕᴰ} 3}

  -- sequencing collects the taints

  collect : pii · key ≡ High ∷ High ∷ Low ∷ []
  collect = refl

  -- the greatest grade carries every label

  everything : ⊤ ≡ pii ∪ᵗ key ∪ᵗ net
  everything = refl
