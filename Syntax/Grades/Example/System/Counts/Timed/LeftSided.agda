------------------------------------------------------------------------
-- A grade system in which the resource grades are certain counts.     --
--                                                                     --
-- Effect grades are the coverage floor: whatever a computation does,  --
-- one of the listed guarantees has been covered. Resource grades are  --
-- at-least counts.                                                    --
--                                                                     --
-- Coverage never buys an operation with time: every operation a       --
-- guarantee names occurs in the run that covers it. So a covering run --
-- draws on every counter at least as often as the guarantee, which is --
-- the one assumption `Lifted.LeftSided` asks for, and every field of  --
-- the projection is preserved.                                        --
--                                                                     --
-- As a resource grade, `atleast 3` on a `heartbeat` counter makes a   --
-- token available only once three heartbeats are certain.             --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Example.System.Counts.Timed.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → ℕ)
  {n : ℕ} (index : Op → Fin n) where

open import Data.Nat.Base using (_≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; +-monoʳ-≤; m≤n+m)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Coverage.Core Op costˡᵒ
open import Syntax.Grades.Traces.Coverage.AsOrder
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (coverageOrder)

open import Syntax.Grades.Example.Counts.Occurrences Op index

------------------------------------------------------------------------
-- A covering run performs every operation the guarantee names

occ-inj⁻ : (i : Fin n) (t⁻ : Trace⁻) → occ i (inj⁻ t⁻) ≡ occ⁻ i t⁻
occ-inj⁻ i ε⁻               = refl
occ-inj⁻ i (operation⁻ o t) = refl

occ-≼ᶜ : ∀ {k s t} → s ≼ᶜ[ k ] t → (i : Fin n) → occ i s ≤ occ i t
occ-≼ᶜ nil                               i = z≤n
occ-≼ᶜ (keep {o = o} p)                  i = +-monoʳ-≤ (hit i o) (occ-≼ᶜ p i)
occ-≼ᶜ (pay-op {o = o} {t = t} p)        i = ≤-trans (occ-≼ᶜ p i) (m≤n+m (occ i t) (hit i o))
occ-≼ᶜ (del-delay {t⁻ = t⁻} p)           i =
  ≤-trans (occ-≼ᶜ p i) (≤-reflexive (occ-inj⁻ i t⁻))
  where open import Data.Nat.Properties using (≤-reflexive)
occ-≼ᶜ (use-delay {s⁻ = s⁻} _ p)         i =
  ≤-trans (≤-reflexive (sym (occ-inj⁻ i s⁻))) (occ-≼ᶜ p i)
  where open import Data.Nat.Properties using (≤-reflexive)

------------------------------------------------------------------------
-- The projection, its grade morphism and the grade system

open import Syntax.Grades.Example.System.Counts.Lifted.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans coverageOrder index occ-≼ᶜ
  public
