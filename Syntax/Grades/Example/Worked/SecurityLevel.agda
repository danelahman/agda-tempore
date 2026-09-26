------------------------------------------------------------------------
-- Worked instances of the security-level grades.                     --
--                                                                    --
-- The two-point lattice `Low < High`, with the runs of the sensor    --
-- node graded by `touches`, and taint sets over `Fin 3`: orderings,  --
-- sequencing and the greatest grade, each established by the         --
-- decision procedure of the grade or by computation.                 --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.SecurityLevel where

open import Data.Fin.Base using (zero; suc)
open import Data.Vec.Base using ([]; _∷_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.SecurityLevel
  using (LowHigh; Low; High; two-point-levels; TaintSet; taint-sets;
         label; _∪ᵗ_)

open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Operations.Footprint using (touches)

------------------------------------------------------------------------
-- Checked orderings
--
-- Each runs the grade's own decision procedure, so an ordering
-- asserted the wrong way round does not typecheck.

module _ {G : Grade} where

  open Grade G

  ≾! : {c d : Carrier} {p : True (c ≾? d)} → c ≾ d
  ≾! {p = p} = toWitness p

  ⋠! : {c d : Carrier} {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! {p = p} = toWitnessFalse p

-- two points

module _ where

  open Grade two-point-levels

  -- a `Low` computation may be treated as `High`, not conversely

  low-⊑-high : Low ≾ High
  low-⊑-high = ≾! {two-point-levels}

  high-⋢-low : ¬ (High ≾ Low)
  high-⋢-low = ⋠! {two-point-levels}

  -- reading `High` data raises the label for the rest of the run

  read-up : High · Low ≡ High
  read-up = refl

  -- waiting does not

  idle : of-nat 5 · Low ≡ Low
  idle = refl

  -- at the sensor node, `logged` stays `Low` and `uplink`, which
  -- transmits, is `High`

  logged-low : touches read · touches write ≡ Low
  logged-low = refl

  uplink-high : touches read · of-nat 2 · touches send ≡ High
  uplink-high = refl

-- three taint labels: personal data, a key, the network

module _ where

  open Grade (taint-sets 3)

  pii key net : TaintSet 3
  pii = label zero
  key = label (suc zero)
  net = label (suc (suc zero))

  pii-⊑-pii∪net : pii ≾ pii ∪ᵗ net
  pii-⊑-pii∪net = ≾! {taint-sets 3}

  pii∪net-⋢-pii : ¬ (pii ∪ᵗ net ≾ pii)
  pii∪net-⋢-pii = ⋠! {taint-sets 3}

  -- incomparable labels

  pii-⋢-key : ¬ (pii ≾ key)
  pii-⋢-key = ⋠! {taint-sets 3}

  key-⋢-pii : ¬ (key ≾ pii)
  key-⋢-pii = ⋠! {taint-sets 3}

  -- sequencing collects the taints

  collect : pii · key ≡ High ∷ High ∷ Low ∷ []
  collect = refl

  -- the greatest grade carries every label

  everything : ⊤ ≡ pii ∪ᵗ key ∪ᵗ net
  everything = refl
