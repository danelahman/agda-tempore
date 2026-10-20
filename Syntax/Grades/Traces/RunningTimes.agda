------------------------------------------------------------------------
-- Running times of operations, and the costs they give.              --
--                                                                    --
-- Each operation runs for a duration in an interval of the time      --
-- domain, each end open or closed, that admits some duration. Every  --
-- operation takes some time: its lower end lies at or above the cut  --
-- just above zero, so the interval admits positive durations only.   --
-- The trace orders read the hull of what the interval admits: an     --
-- operation is credited with its least running time, the infimum     --
-- `costˡᵒ`, and charged its most, the supremum `costʰⁱ`, so the      --
-- upper end must be finite. In a discrete time domain both are       --
-- running times; in a dense one they are the points of the ends.     --
------------------------------------------------------------------------

open import Syntax.Durations using (Duration; TimeDomain; Dense; Discrete)

module Syntax.Grades.Traces.RunningTimes
  {D : Duration} (T : TimeDomain D) (Op : Set) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (fromWitness)

open import Util.Equality

open import Syntax.Durations.Monus T
  using (Carrier; 0ᴰ; _≤ᴰ_; _<ᴰ_; ≤ᴰ-trans; ≤ᴰ-reflexive)
open import Syntax.Durations.Intervals T
open import Syntax.Durations.Intervals.Dense T
  using (_∈ⁱ_; ⊑⁻⇒<; inf-lb; inf-∈; inf-glb; sup-ub; sup-∈; sup-lub)
open import Syntax.Grades.Traces.Positive T using (D⁺; ⟨_⟩⁺; ∣_∣⁺)

-- an upper end that is a cut, not the absence of a bound

data Bounded : Hi → Set where
  fin : (c : Cut) → Bounded (fin c)

record RunningTimes : Set where
  field
    rt         : Op → Interval
    rt-bounded : (o : Op) → Bounded (hi (rt o))
    -- every operation takes some time: its lower end is above zero
    rt-positive : (o : Op) → 0⁺ ⊑ lo (rt o)
    -- and it can run: its interval admits a duration
    rt-inhabited : (o : Op) → Σ Carrier (_∈ⁱ rt o)

  -- so it admits positive durations only

  rt-pos : ∀ o {τ} → τ ∈ⁱ rt o → 0ᴰ <ᴰ τ
  rt-pos o (r , _) = ⊑⁻⇒< (⊑-trans (rt-positive o) r) refl

  -- a positive running time

  rt-inhabited⁺ : (o : Op) → Σ D⁺ (λ d → ∣ d ∣⁺ ∈ⁱ rt o)
  rt-inhabited⁺ o with rt-inhabited o
  ... | τ , m = ⟨ τ ⟩⁺ {fromWitness (rt-pos o m)} , m

  -- and its upper end is above zero

  rt-takes-time : (o : Op) → ¬ (hi (rt o) ⊑ʰ fin 0⁺)
  rt-takes-time o with hi (rt o) | lo◁hi (rt o)
  ... | fin c | p = λ q → ⊑-⊏-trans (rt-positive o) p q
  ... | ∞     | _ = λ ()

  -- the upper end, a cut

  hi-cut : Op → Cut
  hi-cut o with hi (rt o) | rt-bounded o
  ... | fin c | fin .c = c

  hi-cut-≡ : ∀ o → hi (rt o) ≡ fin (hi-cut o)
  hi-cut-≡ o with hi (rt o) | rt-bounded o
  ... | fin c | fin .c = refl

  -- the costs: the infimum and supremum of the running times

  costˡᵒ : Op → Carrier
  costˡᵒ o = inf (lo (rt o))

  costʰⁱ : Op → Carrier
  costʰⁱ o = sup (hi-cut o)

  costˡᵒ-≤ : ∀ o {τ} → τ ∈ⁱ rt o → costˡᵒ o ≤ᴰ τ
  costˡᵒ-≤ o = inf-lb {rt o}

  ≤-costʰⁱ : ∀ o {τ} → τ ∈ⁱ rt o → τ ≤ᴰ costʰⁱ o
  ≤-costʰⁱ o = sup-ub {rt o} (hi-cut-≡ o)

  costˡᵒ-glb : ∀ o {y} → (∀ {τ} → τ ∈ⁱ rt o → y ≤ᴰ τ) → y ≤ᴰ costˡᵒ o
  costˡᵒ-glb o = inf-glb {rt o} (proj₂ (rt-inhabited o))

  costʰⁱ-lub : ∀ o {y} → (∀ {τ} → τ ∈ⁱ rt o → τ ≤ᴰ y) → costʰⁱ o ≤ᴰ y
  costʰⁱ-lub o = sup-lub {rt o} (hi-cut-≡ o) (proj₂ (rt-inhabited o))

  -- in a discrete time domain they are running times

  costˡᵒ-∈ : Discrete T → ∀ o → costˡᵒ o ∈ⁱ rt o
  costˡᵒ-∈ δ o = inf-∈ δ {rt o} (proj₂ (rt-inhabited o))

  costʰⁱ-∈ : Discrete T → ∀ o → costʰⁱ o ∈ⁱ rt o
  costʰⁱ-∈ δ o = sup-∈ δ {rt o} (hi-cut-≡ o) (proj₂ (rt-inhabited o))

  -- in a dense one they are the points of the ends

  costˡᵒ-dense : Dense T → ∀ o → costˡᵒ o ≡ pt (lo (rt o))
  costˡᵒ-dense d o = inf-dense d (lo (rt o))

  costʰⁱ-dense : Dense T → ∀ o → costʰⁱ o ≡ pt (hi-cut o)
  costʰⁱ-dense d o = sup-dense d (hi-cut o)

  cost-≤ : (o : Op) → costˡᵒ o ≤ᴰ costʰⁱ o
  cost-≤ o with rt-inhabited o
  ... | τ , m = ≤ᴰ-trans (costˡᵒ-≤ o m) (≤-costʰⁱ o m)

  costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ 0ᴰ)
  costʰⁱ-pos o e with rt-inhabited o
  ... | τ , m = rt-pos o m (≤ᴰ-trans (≤-costʰⁱ o m) (≤ᴰ-reflexive e))
