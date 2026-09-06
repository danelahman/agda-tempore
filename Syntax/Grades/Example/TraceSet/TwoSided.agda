------------------------------------------------------------------------
-- Two-sided trace intervals as grades: the trace analogue of          --
-- `Interval.TwoSided`.                                                --
--                                                                     --
-- A grade is a *pair* of sets of traces, `[ lo , hi ]`, bounding a run --
-- from both sides by the sub-trace preorder:                          --
--                                                                     --
--   * `lo` is a floor -- the run must cover some trace of `lo`;       --
--   * `hi` is a cap  -- the run must fit inside some trace of `hi`.   --
--                                                                     --
-- This is exactly what the two endpoints of `[ min , max ]` do for     --
-- elapsed time, with `_≼_` in place of `_≤_`, and the consistency      --
-- field `lo≼hi` is the analogue of `min≤max`: it says the interval is  --
-- inhabited, since a trace of `lo` already fits inside one of `hi`.    --
--                                                                     --
-- The order weakens each endpoint outwards, again mirroring            --
-- `min i₂ ≤ min i₁ × max i₁ ≤ max i₂`:                                --
--                                                                     --
--   [ L₁ , U₁ ] ≾ [ L₂ , U₂ ]   iff   L₁ ≾ L₂ in `TraceSet.LeftSided` --
--                                and  U₁ ≼ˢ U₂                        --
--                                                                     --
-- so the floor may drop and the cap may rise. `unbox`'s premise        --
-- `ρ' ≾ᵣ ρ` therefore reads: what elapsed did at least what `ρ`'s      --
-- floor asks for, *and* no more than its cap allows.                   --
--                                                                     --
-- Only `TraceSet.Convex` also mentions both lifts, and it is a         --
-- different grade: it puts both on a single set and orients them the   --
-- same way, so it never caps (see its header).                         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.TraceSet.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.List.Relation.Unary.Any using (any?)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; _×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op cost using (_≼_; module DecSubtrace)
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost

-- each endpoint is ordered exactly as the corresponding one-sided
-- trace grade orders it

open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_)
open import Syntax.Grades.Example.TraceSet.RightSided Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_)

open WithDecEq _≟ₒ_ using (_≟ᴺ_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The carrier

record TraceInterval : Set where
  constructor [_,_,_]
  field
    lo : NeTraces
    hi : NeTraces
    -- the floor already fits inside the cap, so the interval is inhabited
    lo≼hi : traces lo ≼ˢ traces hi

open TraceInterval public

-- two intervals are equal as soon as their endpoints are: the
-- consistency witness is a `True`-of-a-decision, hence irrelevant

lo≼hi-irr : {L U : NeTraces} (p q : traces L ≼ˢ traces U) → p ≡ q
lo≼hi-irr {L} {U} p q =
  fun-ext (λ s → fun-ext (λ m →
    True-irr (any? (λ t → s ≼? t) (traces U)) (p s m) (q s m)))

eqᵗⁱ : {i₁ i₂ : TraceInterval} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᵗⁱ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (lo≼hi-irr {L} {U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᵗⁱ_

_·ᵗⁱ_ : TraceInterval → TraceInterval → TraceInterval
i₁ ·ᵗⁱ i₂ =
  [ lo i₁ · lo i₂
  , hi i₁ · hi i₂
  , ≼ˢ-·ˢ {traces (lo i₁)} {traces (hi i₁)} {traces (lo i₂)} {traces (hi i₂)}
          (lo≼hi i₁) (lo≼hi i₂)
  ]

uᵗⁱ : TraceInterval
uᵗⁱ = [ u , u , ≼ˢ-refl {traces u} ]

·ᵗⁱ-identityʳ : (i : TraceInterval) → (i ·ᵗⁱ uᵗⁱ) ≡ i
·ᵗⁱ-identityʳ i = eqᵗⁱ (·-identityʳ (lo i)) (·-identityʳ (hi i))

·ᵗⁱ-identityˡ : (i : TraceInterval) → (uᵗⁱ ·ᵗⁱ i) ≡ i
·ᵗⁱ-identityˡ i = eqᵗⁱ (·-identityˡ (lo i)) (·-identityˡ (hi i))

·ᵗⁱ-assoc : (i₁ i₂ i₃ : TraceInterval)
          → ((i₁ ·ᵗⁱ i₂) ·ᵗⁱ i₃) ≡ (i₁ ·ᵗⁱ (i₂ ·ᵗⁱ i₃))
·ᵗⁱ-assoc i₁ i₂ i₃ =
  eqᵗⁱ (·-assoc (lo i₁) (lo i₂) (lo i₃))
       (·-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: the floor drops, the cap rises

infix 5 _≾ᵗⁱ_

_≾ᵗⁱ_ : TraceInterval → TraceInterval → Set
i₁ ≾ᵗⁱ i₂ = (lo i₁ ≾ˡᵒ lo i₂) × (hi i₁ ≾ʰⁱ hi i₂)

≾ᵗⁱ-refl : {i : TraceInterval} → i ≾ᵗⁱ i
≾ᵗⁱ-refl {i} = ≽ˢ-refl {traces (lo i)} , ≼ˢ-refl {traces (hi i)}

≾ᵗⁱ-trans : {i₁ i₂ i₃ : TraceInterval} → i₁ ≾ᵗⁱ i₂ → i₂ ≾ᵗⁱ i₃ → i₁ ≾ᵗⁱ i₃
≾ᵗⁱ-trans {i₁} {i₂} {i₃} (l₁ , h₁) (l₂ , h₂) =
    ≽ˢ-trans {traces (lo i₃)} {traces (lo i₂)} {traces (lo i₁)} l₂ l₁
  , ≼ˢ-trans {traces (hi i₁)} {traces (hi i₂)} {traces (hi i₃)} h₁ h₂

-- the product is monotone endpoint by endpoint

·ᵗⁱ-monoˡ : {c i₁ i₂ : TraceInterval} → i₁ ≾ᵗⁱ i₂ → (i₁ ·ᵗⁱ c) ≾ᵗⁱ (i₂ ·ᵗⁱ c)
·ᵗⁱ-monoˡ {c} {i₁} {i₂} (l , h) =
    ≽ˢ-·ˢ {traces (lo i₂)} {traces (lo i₁)} {traces (lo c)} {traces (lo c)}
          l (≽ˢ-refl {traces (lo c)})
  , ≼ˢ-·ˢ {traces (hi i₁)} {traces (hi i₂)} {traces (hi c)} {traces (hi c)}
          h (≼ˢ-refl {traces (hi c)})

·ᵗⁱ-monoʳ : {c i₁ i₂ : TraceInterval} → i₁ ≾ᵗⁱ i₂ → (c ·ᵗⁱ i₁) ≾ᵗⁱ (c ·ᵗⁱ i₂)
·ᵗⁱ-monoʳ {c} {i₁} {i₂} (l , h) =
    ≽ˢ-·ˢ {traces (lo c)} {traces (lo c)} {traces (lo i₂)} {traces (lo i₁)}
          (≽ˢ-refl {traces (lo c)}) l
  , ≼ˢ-·ˢ {traces (hi c)} {traces (hi c)} {traces (hi i₁)} {traces (hi i₂)}
          (≼ˢ-refl {traces (hi c)}) h

------------------------------------------------------------------------
-- Zero-product property
--
-- Only the cap carries information at the unit: `[ L , U ] ≾ uᵗⁱ` asks
-- that every trace of `U` take no time, and durations add along
-- sequencing, so a product below the unit has both factors below it.
-- The floor half is vacuous, as it is in `TraceSet.LeftSided`.

≾ᵗⁱ-zero-productˡ : {i₁ i₂ : TraceInterval} → (i₁ ·ᵗⁱ i₂) ≾ᵗⁱ uᵗⁱ → i₁ ≾ᵗⁱ uᵗⁱ
≾ᵗⁱ-zero-productˡ {i₁} {i₂} (_ , h) =
    u-≽ˢ (traces (lo i₁))
  , ≼ˢ-zero-productˡ {traces (hi i₁)} {traces (hi i₂)} (nonempty (hi i₂)) h

≾ᵗⁱ-zero-productʳ : {i₁ i₂ : TraceInterval} → (i₁ ·ᵗⁱ i₂) ≾ᵗⁱ uᵗⁱ → i₂ ≾ᵗⁱ uᵗⁱ
≾ᵗⁱ-zero-productʳ {i₁} {i₂} (_ , h) =
    u-≽ˢ (traces (lo i₂))
  , ≼ˢ-zero-productʳ {traces (hi i₁)} {traces (hi i₂)} (nonempty (hi i₁)) h

-- both halves are decided, so the order is proof-irrelevant

≾ᵗⁱ-irrelevant : {i₁ i₂ : TraceInterval} → (p q : i₁ ≾ᵗⁱ i₂) → p ≡ q
≾ᵗⁱ-irrelevant {i₁} {i₂} (l , h) (l' , h') =
  cong₂ _,_
    (fun-ext (λ t → fun-ext (λ m →
       True-irr (any? (λ s → s ≼? t) (traces (lo i₂))) (l t m) (l' t m))))
    (fun-ext (λ s → fun-ext (λ m →
       True-irr (any? (λ t → s ≼? t) (traces (hi i₂))) (h s m) (h' s m))))

-- decidable equality, endpoint by endpoint

_≟ᵗⁱ_ : Decidable (_≡_ {A = TraceInterval})
i₁ ≟ᵗⁱ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqᵗⁱ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers
--
-- `n` time steps is the singleton interval at the pure delay `⟨ n ⟩`,
-- exactly as `of-nat n` is `[ n , n ]` for the two-sided time intervals.

of-natᵗⁱ : ℕ → TraceInterval
of-natᵗⁱ n = [ of-nat n , of-nat n , ≼ˢ-refl {traces (of-nat n)} ]

------------------------------------------------------------------------
-- The order is decidable, endpoint by endpoint

infix 5 _≾ᵗⁱ?_

_≾ᵗⁱ?_ : (i₁ i₂ : TraceInterval) → Dec (i₁ ≾ᵗⁱ i₂)
i₁ ≾ᵗⁱ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The grade of two-sided trace intervals

two-sided-traces : Grade
two-sided-traces = record
  { Carrier         = TraceInterval
  ; _·_             = _·ᵗⁱ_
  ; u               = uᵗⁱ
  ; ·-identityʳ     = ·ᵗⁱ-identityʳ
  ; ·-identityˡ     = ·ᵗⁱ-identityˡ
  ; ·-assoc         = ·ᵗⁱ-assoc
  ; _≾_             = _≾ᵗⁱ_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵗⁱ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵗⁱ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵗⁱ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵗⁱ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵗⁱ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗⁱ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗⁱ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵗⁱ-irrelevant {c} {d}
  ; of-nat          = of-natᵗⁱ
  ; of-nat-zero     = eqᵗⁱ of-nat-zero of-nat-zero
  ; of-nat-plus     = λ {m} {n} → eqᵗⁱ (of-nat-plus {m} {n}) (of-nat-plus {m} {n})
  }
