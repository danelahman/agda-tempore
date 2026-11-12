------------------------------------------------------------------------
-- Inter-arrival grades of one operation.                             --
--                                                                    --
-- A run is summarised as silent, calling the operation not at all,   --
-- or as active (`Act`): a count of calls, at least 1, a lead time    --
-- before the first call, the gaps between the starts of consecutive  --
-- calls, none with one call, and a tail from the start of the last   --
-- call to the end. A grade (`Entry`) bounds the silent durations by  --
-- an interval, and the active runs by intervals of their counts,     --
-- lead times, gaps and tails; a case, or the gaps, may be absent     --
-- (`nothing`, below every interval), but not both cases: an entry    --
-- admits some run.                                                   --
--                                                                    --
-- Sequencing adds the silent durations, and joins the active parts   --
-- from a silent part before an active one, its duration added to the --
-- lead time (`_▸_`), from an active part before a silent one, its    --
-- duration added to the tail (`_◂_`), and from two active parts, the --
-- counts added and the tail of the first with the lead time of the   --
-- second a new gap (`_⋈_`). The order compares the ends, case by     --
-- case and component by component; the join is the hull; the unit is --
-- silent for no time; the top admits every silent duration and every --
-- active run; and a delay by `τ` is silent for `τ`.                  --
--                                                                    --
-- Every law holds on the nose and the order is antisymmetric         --
-- (`entry-poset`). The joins of intervals are associative,           --
-- commutative and idempotent and the sums distribute over them, so   --
-- that both sides of the associativity and the distributivity laws   --
-- are joins of the same cases, which the solver for idempotent       --
-- commutative monoids regroups. The unit-product laws use that no    --
-- entry is empty: a product below the unit has no active part, so    --
-- neither factor has one. The top is greatest as counts are          --
-- positive. The closures are in `InterArrival.Closure`.              --
------------------------------------------------------------------------

open import Grades.Durations

module Grades.Examples.InterArrival.Entry {D : Duration} (T : TimeDomain D) where

open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _×-dec_; map′; recompute)

import Algebra.Solver.IdempotentCommutativeMonoid as ICM

open import Grades.Base
open import Grades.Examples.Time.Intervals T
import Grades.Examples.Time.Interval as C
open import Grades.Examples.InterArrival.Options

open import Util.Equality

open Duration D using () renaming (Carrier to 𝔻)

------------------------------------------------------------------------
-- The components: intervals of durations and of counts, their joins
-- associative, commutative and idempotent on the nose, and their sums
-- distributing over them

private
  module I = Grade domain-interval
  module K = Grade C.interval

  ≃ⁱ⇒≡ : ∀ {i j} → i I.≃ j → i ≡ j
  ≃ⁱ⇒≡ {i} {j} (p , q) = ⊆ⁱ-antisym {i} {j} p q

  ≃ᵏ⇒≡ : ∀ {k k'} → k K.≃ k' → k ≡ k'
  ≃ᵏ⇒≡ {k} {k'} (p , q) = C.≾ᵢ-antisym {k} {k'} p q

∪ⁱ-assoc : ∀ i j k → (i ∪ⁱ j) ∪ⁱ k ≡ i ∪ⁱ (j ∪ⁱ k)
∪ⁱ-assoc i j k = ≃ⁱ⇒≡ (I.⊔-assoc i j k)

∪ⁱ-comm : ∀ i j → i ∪ⁱ j ≡ j ∪ⁱ i
∪ⁱ-comm i j = ≃ⁱ⇒≡ (I.⊔-comm i j)

∪ⁱ-idem : ∀ i → i ∪ⁱ i ≡ i
∪ⁱ-idem i = ≃ⁱ⇒≡ (I.⊔-idem i)

⊕-distribˡ : ∀ i j k → i ⊕ (j ∪ⁱ k) ≡ (i ⊕ j) ∪ⁱ (i ⊕ k)
⊕-distribˡ i j k = ≃ⁱ⇒≡ (I.·-distribˡ-⊔ i j k)

⊕-distribʳ : ∀ i j k → (j ∪ⁱ k) ⊕ i ≡ (j ⊕ i) ∪ⁱ (k ⊕ i)
⊕-distribʳ i j k = ≃ⁱ⇒≡ (I.·-distribʳ-⊔ i j k)

⊔ᵏ-assoc : ∀ k k' k'' → (k C.⊔ᵢ k') C.⊔ᵢ k'' ≡ k C.⊔ᵢ (k' C.⊔ᵢ k'')
⊔ᵏ-assoc k k' k'' = ≃ᵏ⇒≡ (K.⊔-assoc k k' k'')

⊔ᵏ-comm : ∀ k k' → k C.⊔ᵢ k' ≡ k' C.⊔ᵢ k
⊔ᵏ-comm k k' = ≃ᵏ⇒≡ (K.⊔-comm k k')

⊔ᵏ-idem : ∀ k → k C.⊔ᵢ k ≡ k
⊔ᵏ-idem k = ≃ᵏ⇒≡ (K.⊔-idem k)

·ᵏ-distribˡ : ∀ k k' k'' → k C.·ᵢ (k' C.⊔ᵢ k'') ≡ (k C.·ᵢ k') C.⊔ᵢ (k C.·ᵢ k'')
·ᵏ-distribˡ k k' k'' = ≃ᵏ⇒≡ (K.·-distribˡ-⊔ k k' k'')

·ᵏ-distribʳ : ∀ k k' k'' → (k' C.⊔ᵢ k'') C.·ᵢ k ≡ (k' C.·ᵢ k) C.⊔ᵢ (k'' C.·ᵢ k)
·ᵏ-distribʳ k k' k'' = ≃ᵏ⇒≡ (K.·-distribʳ-⊔ k k' k'')

·ᵏ-mono : ∀ {k k' m m'} → k C.≾ᵢ k' → m C.≾ᵢ m' → (k C.·ᵢ m) C.≾ᵢ (k' C.·ᵢ m')
·ᵏ-mono {k} {k'} {m} {m'} p q =
  K.≾-trans {k C.·ᵢ m} {k' C.·ᵢ m} {k' C.·ᵢ m'}
    (K.·-monoˡ-≾ {m} {k} {k'} p) (K.·-monoʳ-≾ {k'} {m} {m'} q)

⊕-mono₂ : ∀ {i i' j j'} → i ⊆ⁱ i' → j ⊆ⁱ j' → i ⊕ j ⊆ⁱ i' ⊕ j'
⊕-mono₂ {i} {i'} {j} {j'} = ⊕-mono {i} {i'} {j} {j'}

-- possibly empty intervals: the gaps, and the silent durations

open Order _⊆ⁱ_ public using ()
  renaming (_⊑?_ to _⊆?_; ⊑?-refl to ⊆?-refl; ⊑?-trans to ⊆?-trans;
            ⊑?-antisym to ⊆?-antisym; ⊑?-irrelevant to ⊆?-irrelevant;
            ⊑?-dec to ⊆?-dec; ⊑?-nothing to ⊆?-nothing)
open Join _∪ⁱ_ public using ()
  renaming (_∨?_ to _∪?_; ∨?-identityʳ to ∪?-identityʳ;
            ∨?-nonemptyˡ to ∪?-nonemptyˡ; ∨?-nonemptyʳ to ∪?-nonemptyʳ)

private
  module JI = Join _∪ⁱ_
  module JOI = JoinOrder _⊆ⁱ_ _∪ⁱ_ (λ {i} → ⊆ⁱ-refl {i}) (λ {i} {j} {k} → ⊆ⁱ-trans {i} {j} {k})
                 ∪ⁱ-ubˡ ∪ⁱ-ubʳ (λ {i} {j} {k} → ∪ⁱ-lub {i} {j} {k})

∪?-assoc : ∀ u v w → (u ∪? v) ∪? w ≡ u ∪? (v ∪? w)
∪?-assoc = JI.∨?-assoc ∪ⁱ-assoc ∪ⁱ-comm ∪ⁱ-idem

∪?-comm : ∀ u v → u ∪? v ≡ v ∪? u
∪?-comm = JI.∨?-comm ∪ⁱ-assoc ∪ⁱ-comm ∪ⁱ-idem

∪?-idem : ∀ u → u ∪? u ≡ u
∪?-idem = JI.∨?-idem ∪ⁱ-assoc ∪ⁱ-comm ∪ⁱ-idem

∪?-mono : ∀ {u u' v v'} → u ⊆? u' → v ⊆? v' → u ∪? v ⊆? u' ∪? v'
∪?-mono {u} {u'} {v} {v'} = JOI.∨?-mono {u} {u'} {v} {v'}

private
  module GS = ICM (JI.∨?-icm ∪ⁱ-assoc ∪ⁱ-comm ∪ⁱ-idem)

------------------------------------------------------------------------
-- Active summaries: the bounds on the count, at least 1, the lead time,
-- the gaps, absent where there are none, and the tail

record Act : Set where
  constructor act
  field
    count : C.Interval∞
    lead  : Interval
    gaps  : Maybe Interval
    tail  : Interval
    .{positive} : True (1 ℕₚ.≤? C.min count)

open Act public

act-≡ : ∀ {k k' l l' g g' t t'} .{p : True (1 ℕₚ.≤? C.min k)} .{p' : True (1 ℕₚ.≤? C.min k')}
      → k ≡ k' → l ≡ l' → g ≡ g' → t ≡ t' → act k l g t {p} ≡ act k' l' g' t' {p'}
act-≡ refl refl refl refl = refl

private
  pos-⊔ : ∀ k k' → True (1 ℕₚ.≤? C.min k) → True (1 ℕₚ.≤? C.min k')
        → True (1 ℕₚ.≤? C.min (k C.⊔ᵢ k'))
  pos-⊔ k k' p p' = fromWitness (ℕₚ.⊓-glb (toWitness p) (toWitness p'))

  pos-· : ∀ k k' → True (1 ℕₚ.≤? C.min k) → True (1 ℕₚ.≤? C.min (k C.·ᵢ k'))
  pos-· k k' p = fromWitness (ℕₚ.≤-trans (toWitness p) (ℕₚ.m≤m+n (C.min k) (C.min k')))

infixl 6 _∨ᵃ_
infixr 7 _▸_
infixl 7 _◂_ _⋈_

-- the hull, component by component

_∨ᵃ_ : Act → Act → Act
act k l g t {p} ∨ᵃ act k' l' g' t' {p'} =
  act (k C.⊔ᵢ k') (l ∪ⁱ l') (g ∪? g') (t ∪ⁱ t') {pos-⊔ k k' p p'}

-- a silent duration before, added to the lead time

_▸_ : Interval → Act → Act
s ▸ act k l g t {p} = act k (s ⊕ l) g t {p}

-- a silent duration after, added to the tail

_◂_ : Act → Interval → Act
act k l g t {p} ◂ s = act k l g (t ⊕ s) {p}

-- two active parts: the counts added, and the tail of the first with
-- the lead time of the second a gap

_⋈_ : Act → Act → Act
act k l g t {p} ⋈ act k' l' g' t' {p'} =
  act (k C.·ᵢ k') l ((g ∪? g') ∪? just (t ⊕ l')) t' {pos-· k k' p}

-- any count of at least 1, and any durations

⊤ᵃ : Act
⊤ᵃ = act C.[ 1 , C.∞ ] ⊤ⁱ (just ⊤ⁱ) ⊤ⁱ

-- the order, component by component

infix 4 _⊑ᵃ_

record _⊑ᵃ_ (a a' : Act) : Set where
  constructor act-⊑
  field
    count-⊑ : count a C.≾ᵢ count a'
    lead-⊑  : lead a ⊆ⁱ lead a'
    gaps-⊑  : gaps a ⊆? gaps a'
    tail-⊑  : tail a ⊆ⁱ tail a'

open _⊑ᵃ_ public

------------------------------------------------------------------------
-- The laws of active summaries

⊑ᵃ-refl : ∀ {a} → a ⊑ᵃ a
⊑ᵃ-refl {a} = (act-⊑ (K.≾-refl {count a}) (⊆ⁱ-refl {lead a}) (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {gaps a}) (⊆ⁱ-refl {tail a}))

⊑ᵃ-trans : ∀ {a a' a''} → a ⊑ᵃ a' → a' ⊑ᵃ a'' → a ⊑ᵃ a''
⊑ᵃ-trans {a} {a'} {a''} (act-⊑ c l g t) (act-⊑ c' l' g' t') =
  (act-⊑ (K.≾-trans {count a} {count a'} {count a''} c c') (⊆ⁱ-trans {lead a} {lead a'} {lead a''} l l') (⊆?-trans (λ {i} {j} {k} → ⊆ⁱ-trans {i} {j} {k}) {gaps a} {gaps a'} {gaps a''} g g') (⊆ⁱ-trans {tail a} {tail a'} {tail a''} t t'))

⊑ᵃ-antisym : ∀ {a a'} → a ⊑ᵃ a' → a' ⊑ᵃ a → a ≡ a'
⊑ᵃ-antisym {act k l g t} {act k' l' g' t'} (act-⊑ c m h u) (act-⊑ c' m' h' u') =
  act-≡ (C.≾ᵢ-antisym {k} {k'} c c') (⊆ⁱ-antisym {l} {l'} m m')
        (⊆?-antisym (λ {i} {j} → ⊆ⁱ-antisym {i} {j}) {g} {g'} h h')
        (⊆ⁱ-antisym {t} {t'} u u')

⊑ᵃ-irrelevant : ∀ {a a'} (p q : a ⊑ᵃ a') → p ≡ q
⊑ᵃ-irrelevant {a} {a'} (act-⊑ c l g t) (act-⊑ c' l' g' t') =
  cong₂ (λ x y → x y) (cong₃ act-⊑ (C.≾ᵢ-irrelevant {count a} {count a'} c c')
                                         (⊆ⁱ-irrelevant {lead a} {lead a'} l l')
                                         (⊆?-irrelevant (λ {i} {j} → ⊆ⁱ-irrelevant {i} {j})
                                                        {gaps a} {gaps a'} g g'))
        (⊆ⁱ-irrelevant {tail a} {tail a'} t t')

⊑ᵃ-dec : Decidable _⊑ᵃ_
⊑ᵃ-dec a a' =
  map′ (λ (c , l , g , t) → (act-⊑ c l g t))
       (λ (act-⊑ c l g t) → c , l , g , t)
       (count a C.≾ᵢ? count a' ×-dec lead a ⊆ⁱ? lead a'
        ×-dec ⊆?-dec _⊆ⁱ?_ (gaps a) (gaps a') ×-dec tail a ⊆ⁱ? tail a')

∨ᵃ-ubˡ : ∀ a a' → a ⊑ᵃ a ∨ᵃ a'
∨ᵃ-ubˡ (act k l g t) (act k' l' g' t') =
  (act-⊑ (K.⊔-ubˡ k k') (∪ⁱ-ubˡ l l') (JOI.∨?-ubˡ g g') (∪ⁱ-ubˡ t t'))

∨ᵃ-ubʳ : ∀ a a' → a' ⊑ᵃ a ∨ᵃ a'
∨ᵃ-ubʳ (act k l g t) (act k' l' g' t') =
  (act-⊑ (K.⊔-ubʳ k k') (∪ⁱ-ubʳ l l') (JOI.∨?-ubʳ g g') (∪ⁱ-ubʳ t t'))

∨ᵃ-lub : ∀ {a a' a''} → a ⊑ᵃ a'' → a' ⊑ᵃ a'' → a ∨ᵃ a' ⊑ᵃ a''
∨ᵃ-lub {act k l g t} {act k' l' g' t'} {act k'' l'' g'' t''}
       (act-⊑ c m h u) (act-⊑ c' m' h' u') =
  (act-⊑ (K.⊔-lub {k} {k'} {k''} c c') (∪ⁱ-lub {l} {l'} {l''} m m') (JOI.∨?-lub {g} {g'} {g''} h h') (∪ⁱ-lub {t} {t'} {t''} u u'))

∨ᵃ-assoc : ∀ a a' a'' → (a ∨ᵃ a') ∨ᵃ a'' ≡ a ∨ᵃ (a' ∨ᵃ a'')
∨ᵃ-assoc (act k l g t) (act k' l' g' t') (act k'' l'' g'' t'') =
  act-≡ (⊔ᵏ-assoc k k' k'') (∪ⁱ-assoc l l' l'') (∪?-assoc g g' g'') (∪ⁱ-assoc t t' t'')

∨ᵃ-comm : ∀ a a' → a ∨ᵃ a' ≡ a' ∨ᵃ a
∨ᵃ-comm (act k l g t) (act k' l' g' t') =
  act-≡ (⊔ᵏ-comm k k') (∪ⁱ-comm l l') (∪?-comm g g') (∪ⁱ-comm t t')

∨ᵃ-idem : ∀ a → a ∨ᵃ a ≡ a
∨ᵃ-idem (act k l g t) = act-≡ (⊔ᵏ-idem k) (∪ⁱ-idem l) (∪?-idem g) (∪ⁱ-idem t)

⊑ᵃ-⊤ : ∀ a → a ⊑ᵃ ⊤ᵃ
⊑ᵃ-⊤ (act k l g t {p}) =
  (act-⊑ ((recompute (1 ℕₚ.≤? C.min k) (toWitness p) , C.≤∞-∞ (C.max k))) (⊆ⁱ-⊤ l) (gaps-⊤ g) (⊆ⁱ-⊤ t))
  where
    gaps-⊤ : ∀ g → g ⊆? just ⊤ⁱ
    gaps-⊤ (just i) = ⊆ⁱ-⊤ i
    gaps-⊤ nothing  = tt

-- the silent durations before and after: their units, their
-- distributivity over the hulls, and their monotonicity

▸-identity : ∀ a → 0ⁱ ▸ a ≡ a
▸-identity (act k l g t) = act-≡ refl (⊕-identityˡ l) refl refl

◂-identity : ∀ a → a ◂ 0ⁱ ≡ a
◂-identity (act k l g t) = act-≡ refl refl refl (⊕-identityʳ t)

▸-distribˡ : ∀ s s' a → (s ∪ⁱ s') ▸ a ≡ (s ▸ a) ∨ᵃ (s' ▸ a)
▸-distribˡ s s' (act k l g t) =
  act-≡ (sym (⊔ᵏ-idem k)) (⊕-distribʳ l s s') (sym (∪?-idem g)) (sym (∪ⁱ-idem t))

▸-distribʳ : ∀ s a a' → s ▸ (a ∨ᵃ a') ≡ (s ▸ a) ∨ᵃ (s ▸ a')
▸-distribʳ s (act k l g t) (act k' l' g' t') = act-≡ refl (⊕-distribˡ s l l') refl refl

◂-distribˡ : ∀ a a' s → (a ∨ᵃ a') ◂ s ≡ (a ◂ s) ∨ᵃ (a' ◂ s)
◂-distribˡ (act k l g t) (act k' l' g' t') s = act-≡ refl refl refl (⊕-distribʳ s t t')

◂-distribʳ : ∀ a s s' → a ◂ (s ∪ⁱ s') ≡ (a ◂ s) ∨ᵃ (a ◂ s')
◂-distribʳ (act k l g t) s s' =
  act-≡ (sym (⊔ᵏ-idem k)) (sym (∪ⁱ-idem l)) (sym (∪?-idem g)) (⊕-distribˡ t s s')

⋈-distribˡ : ∀ a a' b → (a ∨ᵃ a') ⋈ b ≡ (a ⋈ b) ∨ᵃ (a' ⋈ b)
⋈-distribˡ (act k l g t) (act k' l' g' t') (act m n h u) =
  act-≡ (·ᵏ-distribʳ m k k') refl
        (trans (cong (λ x → ((g ∪? g') ∪? h) ∪? just x) (⊕-distribʳ n t t'))
               (GS.solve 5 (λ x x' y z z' → ((x GS.⊕ x') GS.⊕ y) GS.⊕ (z GS.⊕ z')
                                            GS.⊜ ((x GS.⊕ y) GS.⊕ z) GS.⊕ ((x' GS.⊕ y) GS.⊕ z'))
                           refl g g' h (just (t ⊕ n)) (just (t' ⊕ n))))
        (sym (∪ⁱ-idem u))

⋈-distribʳ : ∀ a b b' → a ⋈ (b ∨ᵃ b') ≡ (a ⋈ b) ∨ᵃ (a ⋈ b')
⋈-distribʳ (act k l g t) (act m n h u) (act m' n' h' u') =
  act-≡ (·ᵏ-distribˡ k m m') (sym (∪ⁱ-idem l))
        (trans (cong (λ x → (g ∪? (h ∪? h')) ∪? just x) (⊕-distribˡ t n n'))
               (GS.solve 5 (λ x y y' z z' → (x GS.⊕ (y GS.⊕ y')) GS.⊕ (z GS.⊕ z')
                                            GS.⊜ ((x GS.⊕ y) GS.⊕ z) GS.⊕ ((x GS.⊕ y') GS.⊕ z'))
                           refl g h h' (just (t ⊕ n)) (just (t ⊕ n'))))
        refl

▸-mono : ∀ {s s' a a'} → s ⊆ⁱ s' → a ⊑ᵃ a' → s ▸ a ⊑ᵃ s' ▸ a'
▸-mono {s} {s'} {act k l g t} {act k' l' g' t'} p (act-⊑ c m h u) =
  (act-⊑ c (⊕-mono₂ {s} {s'} {l} {l'} p m) h u)

◂-mono : ∀ {a a' s s'} → a ⊑ᵃ a' → s ⊆ⁱ s' → a ◂ s ⊑ᵃ a' ◂ s'
◂-mono {act k l g t} {act k' l' g' t'} {s} {s'} (act-⊑ c m h u) p =
  (act-⊑ c m h (⊕-mono₂ {t} {t'} {s} {s'} u p))

⋈-mono : ∀ {a a' b b'} → a ⊑ᵃ a' → b ⊑ᵃ b' → a ⋈ b ⊑ᵃ a' ⋈ b'
⋈-mono {act k l g t} {act k' l' g' t'} {act m n h u} {act m' n' h' u'}
       (act-⊑ c p q r) (act-⊑ c' p' q' r') =
  (act-⊑ (·ᵏ-mono {k} {k'} {m} {m'} c c') p (∪?-mono {g ∪? h} {g' ∪? h'} {just (t ⊕ n)} {just (t' ⊕ n')}
              (∪?-mono {g} {g'} {h} {h'} q q') (⊕-mono₂ {t} {t'} {n} {n'} r p')) r')

-- the associativity of the actions and of `_⋈_`

▸-▸ : ∀ s s' a → (s ⊕ s') ▸ a ≡ s ▸ (s' ▸ a)
▸-▸ s s' (act k l g t) = act-≡ refl (⊕-assoc s s' l) refl refl

▸-◂ : ∀ s a s' → (s ▸ a) ◂ s' ≡ s ▸ (a ◂ s')
▸-◂ s (act k l g t) s' = refl

◂-◂ : ∀ a s s' → (a ◂ s) ◂ s' ≡ a ◂ (s ⊕ s')
◂-◂ (act k l g t) s s' = act-≡ refl refl refl (⊕-assoc t s s')

⋈-◂ : ∀ a a' s → (a ⋈ a') ◂ s ≡ a ⋈ (a' ◂ s)
⋈-◂ (act k l g t) (act k' l' g' t') s = refl

▸-⋈ : ∀ s a a' → (s ▸ a) ⋈ a' ≡ s ▸ (a ⋈ a')
▸-⋈ s (act k l g t) (act k' l' g' t') = refl

◂-⋈ : ∀ a s a' → (a ◂ s) ⋈ a' ≡ a ⋈ (s ▸ a')
◂-⋈ (act k l g t) s (act k' l' g' t') =
  act-≡ refl refl (cong (λ x → (g ∪? g') ∪? just x) (⊕-assoc t s l')) refl

⋈-⋈ : ∀ a a' a'' → (a ⋈ a') ⋈ a'' ≡ a ⋈ (a' ⋈ a'')
⋈-⋈ (act k l g t) (act k' l' g' t') (act k'' l'' g'' t'') =
  act-≡ (C.·ᵢ-assoc k k' k'') refl
        (GS.solve 5 (λ x x' y x'' y' → (((x GS.⊕ x') GS.⊕ y) GS.⊕ x'') GS.⊕ y'
                                       GS.⊜ (x GS.⊕ ((x' GS.⊕ x'') GS.⊕ y')) GS.⊕ y)
                    refl g g' (just (t ⊕ l')) g'' (just (t' ⊕ l'')))
        refl

------------------------------------------------------------------------
-- Possibly absent active summaries

open Order _⊑ᵃ_ public using ()
  renaming (_⊑?_ to _⊑ᵃ?_; ⊑?-nothing to ⊑ᵃ?-nothing)
open Join _∨ᵃ_ public using ()
  renaming (_∨?_ to _∨ᵃ?_; ∨?-identityʳ to ∨ᵃ?-identityʳ;
            ∨?-nonemptyˡ to ∨ᵃ?-nonemptyˡ; ∨?-nonemptyʳ to ∨ᵃ?-nonemptyʳ;
            ∨?-nothingˡ to ∨ᵃ?-nothingˡ; ∨?-nothingʳ to ∨ᵃ?-nothingʳ)

private
  module OA = Order _⊑ᵃ_
  module JA = Join _∨ᵃ_
  module JOA = JoinOrder _⊑ᵃ_ _∨ᵃ_ ⊑ᵃ-refl ⊑ᵃ-trans ∨ᵃ-ubˡ ∨ᵃ-ubʳ ∨ᵃ-lub
  module AS = ICM (JA.∨?-icm ∨ᵃ-assoc ∨ᵃ-comm ∨ᵃ-idem)

------------------------------------------------------------------------
-- Entries: the silent durations, and the active summaries, not both
-- absent

Inhabited : Maybe Interval → Maybe Act → Set
Inhabited nothing nothing = ⊥
Inhabited _       _       = Unit

record Entry : Set where
  constructor entry
  field
    silent : Maybe Interval
    active : Maybe Act
    .{inhabited} : Inhabited silent active

open Entry public

entry-≡ : ∀ {s s' a a'} .{p : Inhabited s a} .{p' : Inhabited s' a'}
        → s ≡ s' → a ≡ a' → entry s a {p} ≡ entry s' a' {p'}
entry-≡ refl refl = refl

private
  inhabitedˢ : ∀ s a → NonEmpty s → Inhabited s a
  inhabitedˢ (just _) _ _ = tt

  inhabitedᵃ : ∀ s a → NonEmpty a → Inhabited s a
  inhabitedᵃ (just _) _        _ = tt
  inhabitedᵃ nothing  (just _) _ = tt

-- the silent durations and the active summaries of a product

silent· : Maybe Interval → Maybe Interval → Maybe Interval
silent· = lift₂ _⊕_

active· : Maybe Interval → Maybe Act → Maybe Interval → Maybe Act → Maybe Act
active· s a s' a' = (lift₂ _▸_ s a' ∨ᵃ? lift₂ _◂_ a s') ∨ᵃ? lift₂ _⋈_ a a'

private
  inhabited-· : ∀ s a s' a' → Inhabited s a → Inhabited s' a'
              → Inhabited (silent· s s') (active· s a s' a')
  inhabited-· (just x) a (just y) a' _ _ = tt
  inhabited-· (just x) a nothing (just b) _ _ =
    inhabitedᵃ nothing (active· (just x) a nothing (just b))
      (∨ᵃ?-nonemptyˡ (lift₂ _▸_ (just x) (just b) ∨ᵃ? lift₂ _◂_ a nothing) (lift₂ _⋈_ a (just b))
        (∨ᵃ?-nonemptyˡ (just (x ▸ b)) (lift₂ _◂_ a nothing) tt))
  inhabited-· nothing (just a) s' (just b) _ _ =
    inhabitedᵃ nothing (active· nothing (just a) s' (just b))
      (∨ᵃ?-nonemptyʳ (lift₂ _◂_ (just a) s') (just (a ⋈ b)) tt)
  inhabited-· nothing (just a) (just y) nothing _ _ =
    inhabitedᵃ nothing (active· nothing (just a) (just y) nothing)
      (∨ᵃ?-nonemptyˡ (just (a ◂ y)) nothing tt)

  inhabited-⊔ : ∀ s a s' a' → Inhabited s a → Inhabited s' a'
              → Inhabited (s ∪? s') (a ∨ᵃ? a')
  inhabited-⊔ (just x) a s' a' _ _ = inhabitedˢ (just x ∪? s') _ (∪?-nonemptyˡ (just x) s' tt)
  inhabited-⊔ nothing (just b) s' a' _ _ = inhabitedᵃ s' _ (∨ᵃ?-nonemptyˡ (just b) a' tt)

infixl 7 _·ᵉ_
infixl 6 _⊔ᵉ_
infix  4 _⊑ᵉ_

-- sequencing: the silent durations added, and an active part from a
-- silent part before an active one, an active part before a silent
-- one, or two active parts

_·ᵉ_ : Entry → Entry → Entry
entry s a {p} ·ᵉ entry s' a' {p'} =
  entry (silent· s s') (active· s a s' a') {inhabited-· s a s' a' p p'}

-- the join: the hulls, case by case

_⊔ᵉ_ : Entry → Entry → Entry
entry s a {p} ⊔ᵉ entry s' a' {p'} = entry (s ∪? s') (a ∨ᵃ? a') {inhabited-⊔ s a s' a' p p'}

-- the unit, silent for no time; the top; and a delay, silent for it

𝟏ᵉ : Entry
𝟏ᵉ = entry (just 0ⁱ) nothing

⊤ᵉ : Entry
⊤ᵉ = entry (just ⊤ⁱ) (just ⊤ᵃ)

ιᵉ : 𝔻 → Entry
ιᵉ τ = entry (just (pointⁱ τ)) nothing

-- the order: comparison of the ends, case by case

record _⊑ᵉ_ (e e' : Entry) : Set where
  constructor entry-⊑
  field
    silent-⊑ : silent e ⊆? silent e'
    active-⊑ : active e ⊑ᵃ? active e'

open _⊑ᵉ_ public

------------------------------------------------------------------------
-- The laws of entries

⊑ᵉ-refl : ∀ {e} → e ⊑ᵉ e
⊑ᵉ-refl {e} = entry-⊑ (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {silent e}) (OA.⊑?-refl ⊑ᵃ-refl {active e})

⊑ᵉ-trans : ∀ {e e' e''} → e ⊑ᵉ e' → e' ⊑ᵉ e'' → e ⊑ᵉ e''
⊑ᵉ-trans {e} {e'} {e''} (entry-⊑ p q) (entry-⊑ p' q') =
  entry-⊑ (⊆?-trans (λ {i} {j} {k} → ⊆ⁱ-trans {i} {j} {k}) {silent e} {silent e'} {silent e''} p p')
          (OA.⊑?-trans ⊑ᵃ-trans {active e} {active e'} {active e''} q q')

⊑ᵉ-antisym : ∀ {e e'} → e ⊑ᵉ e' → e' ⊑ᵉ e → e ≡ e'
⊑ᵉ-antisym {entry s a} {entry s' a'} (entry-⊑ p q) (entry-⊑ p' q') =
  entry-≡ (⊆?-antisym (λ {i} {j} → ⊆ⁱ-antisym {i} {j}) {s} {s'} p p')
          (OA.⊑?-antisym ⊑ᵃ-antisym {a} {a'} q q')

⊑ᵉ-irrelevant : ∀ {e e'} (p q : e ⊑ᵉ e') → p ≡ q
⊑ᵉ-irrelevant {e} {e'} (entry-⊑ p q) (entry-⊑ p' q') =
  cong₂ entry-⊑ (⊆?-irrelevant (λ {i} {j} → ⊆ⁱ-irrelevant {i} {j}) {silent e} {silent e'} p p')
                (OA.⊑?-irrelevant ⊑ᵃ-irrelevant {active e} {active e'} q q')

_⊑ᵉ?_ : Decidable _⊑ᵉ_
e ⊑ᵉ? e' =
  map′ (λ (p , q) → entry-⊑ p q) (λ (entry-⊑ p q) → p , q)
       (⊆?-dec _⊆ⁱ?_ (silent e) (silent e') ×-dec OA.⊑?-dec ⊑ᵃ-dec (active e) (active e'))

⊑ᵉ-⊤ : ∀ e → e ⊑ᵉ ⊤ᵉ
⊑ᵉ-⊤ (entry s a) = entry-⊑ (silent-⊤ s) (active-⊤ a)
  where
    silent-⊤ : ∀ s → s ⊆? just ⊤ⁱ
    silent-⊤ (just i) = ⊆ⁱ-⊤ i
    silent-⊤ nothing  = tt
    active-⊤ : ∀ a → a ⊑ᵃ? just ⊤ᵃ
    active-⊤ (just b) = ⊑ᵃ-⊤ b
    active-⊤ nothing  = tt

⊔ᵉ-ubˡ : ∀ e e' → e ⊑ᵉ e ⊔ᵉ e'
⊔ᵉ-ubˡ (entry s a) (entry s' a') = entry-⊑ (JOI.∨?-ubˡ s s') (JOA.∨?-ubˡ a a')

⊔ᵉ-ubʳ : ∀ e e' → e' ⊑ᵉ e ⊔ᵉ e'
⊔ᵉ-ubʳ (entry s a) (entry s' a') = entry-⊑ (JOI.∨?-ubʳ s s') (JOA.∨?-ubʳ a a')

⊔ᵉ-lub : ∀ {e e' e''} → e ⊑ᵉ e'' → e' ⊑ᵉ e'' → e ⊔ᵉ e' ⊑ᵉ e''
⊔ᵉ-lub {entry s a} {entry s' a'} {entry s'' a''} (entry-⊑ p q) (entry-⊑ p' q') =
  entry-⊑ (JOI.∨?-lub {s} {s'} {s''} p p') (JOA.∨?-lub {a} {a'} {a''} q q')

-- monotonicity

private
  silent-mono : ∀ {s s' t t'} → s ⊆? s' → t ⊆? t' → silent· s t ⊆? silent· s' t'
  silent-mono {s} {s'} {t} {t'} =
    lift₂-mono {_⊑ᴬ_ = _⊆ⁱ_} {_⊆ⁱ_} {_⊆ⁱ_} _⊕_ (λ {i} {i'} {j} {j'} → ⊕-mono₂ {i} {i'} {j} {j'})
               {s} {s'} {t} {t'}

  active-mono : ∀ {s s' a a' t t' b b'} → s ⊆? s' → a ⊑ᵃ? a' → t ⊆? t' → b ⊑ᵃ? b'
              → active· s a t b ⊑ᵃ? active· s' a' t' b'
  active-mono {s} {s'} {a} {a'} {t} {t'} {b} {b'} p q r u =
    JOA.∨?-mono {lift₂ _▸_ s b ∨ᵃ? lift₂ _◂_ a t} {lift₂ _▸_ s' b' ∨ᵃ? lift₂ _◂_ a' t'}
                {lift₂ _⋈_ a b} {lift₂ _⋈_ a' b'}
      (JOA.∨?-mono {lift₂ _▸_ s b} {lift₂ _▸_ s' b'} {lift₂ _◂_ a t} {lift₂ _◂_ a' t'}
         (lift₂-mono {_⊑ᴬ_ = _⊆ⁱ_} {_⊑ᵃ_} {_⊑ᵃ_} _▸_ ▸-mono {s} {s'} {b} {b'} p u)
         (lift₂-mono {_⊑ᴬ_ = _⊑ᵃ_} {_⊆ⁱ_} {_⊑ᵃ_} _◂_ ◂-mono {a} {a'} {t} {t'} q r))
      (lift₂-mono {_⊑ᴬ_ = _⊑ᵃ_} {_⊑ᵃ_} {_⊑ᵃ_} _⋈_ ⋈-mono {a} {a'} {b} {b'} q u)

·ᵉ-mono : ∀ {e e' f f'} → e ⊑ᵉ e' → f ⊑ᵉ f' → e ·ᵉ f ⊑ᵉ e' ·ᵉ f'
·ᵉ-mono {entry s a} {entry s' a'} {entry t b} {entry t' b'} (entry-⊑ p q) (entry-⊑ r u) =
  entry-⊑ (silent-mono {s} {s'} {t} {t'} p r) (active-mono {s} {s'} {a} {a'} {t} {t'} {b} {b'} p q r u)

-- the unit laws

·ᵉ-identityˡ : ∀ e → 𝟏ᵉ ·ᵉ e ≡ e
·ᵉ-identityˡ (entry s a) =
  entry-≡ (lift₂-identityˡ _⊕_ ⊕-identityˡ s)
          (trans (∨ᵃ?-identityʳ (lift₂ _▸_ (just 0ⁱ) a ∨ᵃ? nothing))
                 (trans (∨ᵃ?-identityʳ (lift₂ _▸_ (just 0ⁱ) a))
                        (lift₂-identityˡ _▸_ ▸-identity a)))

·ᵉ-identityʳ : ∀ e → e ·ᵉ 𝟏ᵉ ≡ e
·ᵉ-identityʳ (entry s a) =
  entry-≡ (lift₂-identityʳ _⊕_ ⊕-identityʳ s)
          (begin
             (lift₂ _▸_ s nothing ∨ᵃ? lift₂ _◂_ a (just 0ⁱ)) ∨ᵃ? lift₂ _⋈_ a nothing
           ≡⟨ cong₂ (λ x y → (x ∨ᵃ? lift₂ _◂_ a (just 0ⁱ)) ∨ᵃ? y)
                    (lift₂-nothingʳ _▸_ s) (lift₂-nothingʳ _⋈_ a) ⟩
             lift₂ _◂_ a (just 0ⁱ) ∨ᵃ? nothing
           ≡⟨ ∨ᵃ?-identityʳ _ ⟩
             lift₂ _◂_ a (just 0ⁱ)
           ≡⟨ lift₂-identityʳ _◂_ ◂-identity a ⟩
             a
           ∎)

-- associativity: the active parts of both sides are joins of the same
-- seven cases

private
  ◂-dist = lift₂-distribˡ {_∨ᴬ_ = _∨ᵃ_} {_∪ⁱ_} {_∨ᵃ_} _◂_ ◂-distribˡ
  ⋈-distˡ = lift₂-distribˡ {_∨ᴬ_ = _∨ᵃ_} {_∨ᵃ_} {_∨ᵃ_} _⋈_ ⋈-distribˡ
  ▸-dist = lift₂-distribʳ {_∨ᴬ_ = _∪ⁱ_} {_∨ᵃ_} {_∨ᵃ_} _▸_ ▸-distribʳ
  ⋈-distʳ = lift₂-distribʳ {_∨ᴬ_ = _∨ᵃ_} {_∨ᵃ_} {_∨ᵃ_} _⋈_ ⋈-distribʳ

  cong₇ : ∀ {A B : Set} (f : A → A → A → A → A → A → A → B)
          {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ x₆ y₆ x₇ y₇}
        → x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ → x₅ ≡ y₅ → x₆ ≡ y₆ → x₇ ≡ y₇
        → f x₁ x₂ x₃ x₄ x₅ x₆ x₇ ≡ f y₁ y₂ y₃ y₄ y₅ y₆ y₇
  cong₇ f refl refl refl refl refl refl refl = refl

  active-assoc : ∀ s a s' a' s'' a''
               → active· (silent· s s') (active· s a s' a') s'' a''
               ≡ active· s a (silent· s' s'') (active· s' a' s'' a'')
  active-assoc s a s' a' s'' a'' =
    begin
      (lift₂ _▸_ (silent· s s') a'' ∨ᵃ? lift₂ _◂_ ((P ∨ᵃ? Q) ∨ᵃ? R) s'')
        ∨ᵃ? lift₂ _⋈_ ((P ∨ᵃ? Q) ∨ᵃ? R) a''
    ≡⟨ cong₂ (λ x y → (lift₂ _▸_ (silent· s s') a'' ∨ᵃ? x) ∨ᵃ? y)
             (trans (◂-dist (P ∨ᵃ? Q) R s'') (cong (_∨ᵃ? lift₂ _◂_ R s'') (◂-dist P Q s'')))
             (trans (⋈-distˡ (P ∨ᵃ? Q) R a'') (cong (_∨ᵃ? lift₂ _⋈_ R a'') (⋈-distˡ P Q a''))) ⟩
      F (lift₂ _▸_ (silent· s s') a'') (lift₂ _◂_ P s'') (lift₂ _◂_ Q s'') (lift₂ _◂_ R s'')
        (lift₂ _⋈_ P a'') (lift₂ _⋈_ Q a'') (lift₂ _⋈_ R a'')
    ≡⟨ cong₇ F (lift₂-assoc _⊕_ _▸_ _▸_ _▸_ ▸-▸ s s' a'')
               (lift₂-assoc _▸_ _◂_ _▸_ _◂_ ▸-◂ s a' s'')
               (lift₂-assoc _◂_ _◂_ _◂_ _⊕_ ◂-◂ a s' s'')
               (lift₂-assoc _⋈_ _◂_ _⋈_ _◂_ ⋈-◂ a a' s'')
               (lift₂-assoc _▸_ _⋈_ _▸_ _⋈_ ▸-⋈ s a' a'')
               (lift₂-assoc _◂_ _⋈_ _⋈_ _▸_ ◂-⋈ a s' a'')
               (lift₂-assoc _⋈_ _⋈_ _⋈_ _⋈_ ⋈-⋈ a a' a'') ⟩
      F u₁ u₂ u₃ u₄ u₅ u₆ u₇
    ≡⟨ AS.solve 7 (λ x₁ x₂ x₃ x₄ x₅ x₆ x₇ →
                     (x₁ AS.⊕ ((x₂ AS.⊕ x₃) AS.⊕ x₄)) AS.⊕ ((x₅ AS.⊕ x₆) AS.⊕ x₇)
                     AS.⊜ ((((x₁ AS.⊕ x₂) AS.⊕ x₅) AS.⊕ x₃) AS.⊕ ((x₆ AS.⊕ x₄) AS.⊕ x₇)))
                  refl u₁ u₂ u₃ u₄ u₅ u₆ u₇ ⟩
      (((u₁ ∨ᵃ? u₂) ∨ᵃ? u₅) ∨ᵃ? u₃) ∨ᵃ? ((u₆ ∨ᵃ? u₄) ∨ᵃ? u₇)
    ≡⟨ sym (cong₂ (λ x y → (x ∨ᵃ? u₃) ∨ᵃ? y)
                  (trans (▸-dist s (P' ∨ᵃ? Q') R') (cong (_∨ᵃ? u₅) (▸-dist s P' Q')))
                  (trans (⋈-distʳ a (P' ∨ᵃ? Q') R') (cong (_∨ᵃ? u₇) (⋈-distʳ a P' Q')))) ⟩
      (lift₂ _▸_ s ((P' ∨ᵃ? Q') ∨ᵃ? R') ∨ᵃ? lift₂ _◂_ a (silent· s' s''))
        ∨ᵃ? lift₂ _⋈_ a ((P' ∨ᵃ? Q') ∨ᵃ? R')
    ∎
    where
      P = lift₂ _▸_ s a'
      Q = lift₂ _◂_ a s'
      R = lift₂ _⋈_ a a'
      P' = lift₂ _▸_ s' a''
      Q' = lift₂ _◂_ a' s''
      R' = lift₂ _⋈_ a' a''
      u₁ = lift₂ _▸_ s P'
      u₂ = lift₂ _▸_ s Q'
      u₃ = lift₂ _◂_ a (silent· s' s'')
      u₄ = lift₂ _⋈_ a Q'
      u₅ = lift₂ _▸_ s R'
      u₆ = lift₂ _⋈_ a P'
      u₇ = lift₂ _⋈_ a R'
      F : (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : Maybe Act) → Maybe Act
      F x₁ x₂ x₃ x₄ x₅ x₆ x₇ = (x₁ ∨ᵃ? ((x₂ ∨ᵃ? x₃) ∨ᵃ? x₄)) ∨ᵃ? ((x₅ ∨ᵃ? x₆) ∨ᵃ? x₇)

·ᵉ-assoc : ∀ e e' e'' → (e ·ᵉ e') ·ᵉ e'' ≡ e ·ᵉ (e' ·ᵉ e'')
·ᵉ-assoc (entry s a) (entry s' a') (entry s'' a'') =
  entry-≡ (lift₂-assoc _⊕_ _⊕_ _⊕_ _⊕_ ⊕-assoc s s' s'') (active-assoc s a s' a' s'' a'')

-- distributivity over the join, on the nose

private
  ▸-distˡ = lift₂-distribˡ {_∨ᴬ_ = _∪ⁱ_} {_∨ᵃ_} {_∨ᵃ_} _▸_ ▸-distribˡ
  ◂-distʳ = lift₂-distribʳ {_∨ᴬ_ = _∨ᵃ_} {_∪ⁱ_} {_∨ᵃ_} _◂_ ◂-distribʳ
  ⊕-distˡ = lift₂-distribʳ {_∨ᴬ_ = _∪ⁱ_} {_∪ⁱ_} {_∪ⁱ_} _⊕_ ⊕-distribˡ
  ⊕-distʳ = lift₂-distribˡ {_∨ᴬ_ = _∪ⁱ_} {_∪ⁱ_} {_∪ⁱ_} _⊕_ (λ i i' j → ⊕-distribʳ j i i')

  -- a join of three pairs of cases, regrouped by pairs

  regroup : ∀ x x' y y' z z'
          → ((x ∨ᵃ? x') ∨ᵃ? (y ∨ᵃ? y')) ∨ᵃ? (z ∨ᵃ? z') ≡ ((x ∨ᵃ? y) ∨ᵃ? z) ∨ᵃ? ((x' ∨ᵃ? y') ∨ᵃ? z')
  regroup = AS.solve 6 (λ x x' y y' z z' →
                          ((x AS.⊕ x') AS.⊕ (y AS.⊕ y')) AS.⊕ (z AS.⊕ z')
                          AS.⊜ ((x AS.⊕ y) AS.⊕ z) AS.⊕ ((x' AS.⊕ y') AS.⊕ z'))
                       refl

·ᵉ-distribˡ : ∀ e f g → e ·ᵉ (f ⊔ᵉ g) ≡ (e ·ᵉ f) ⊔ᵉ (e ·ᵉ g)
·ᵉ-distribˡ (entry s a) (entry t b) (entry t' b') =
  entry-≡ (⊕-distˡ s t t')
          (trans (cong₃ (λ x y z → (x ∨ᵃ? y) ∨ᵃ? z) (▸-dist s b b') (◂-distʳ a t t') (⋈-distʳ a b b'))
                 (regroup (lift₂ _▸_ s b) (lift₂ _▸_ s b') (lift₂ _◂_ a t) (lift₂ _◂_ a t')
                          (lift₂ _⋈_ a b) (lift₂ _⋈_ a b')))

·ᵉ-distribʳ : ∀ e f g → (f ⊔ᵉ g) ·ᵉ e ≡ (f ·ᵉ e) ⊔ᵉ (g ·ᵉ e)
·ᵉ-distribʳ (entry s a) (entry t b) (entry t' b') =
  entry-≡ (⊕-distʳ t t' s)
          (trans (cong₃ (λ x y z → (x ∨ᵃ? y) ∨ᵃ? z) (▸-distˡ t t' a) (◂-dist b b' s) (⋈-distˡ b b' a))
                 (regroup (lift₂ _▸_ t a) (lift₂ _▸_ t' a) (lift₂ _◂_ b s) (lift₂ _◂_ b' s)
                          (lift₂ _⋈_ b a) (lift₂ _⋈_ b' a)))

-- the unit-product laws: a product below the unit has no active part,
-- so none of its three cases contributes one; as no entry is empty,
-- neither factor has an active part, and the silent durations of both
-- lie within those of the unit

private
  zero-ˡ : ∀ s a t b → .(Inhabited s a) → .(Inhabited t b) → silent· s t ⊆? just 0ⁱ
         → lift₂ _▸_ s b ≡ nothing → lift₂ _◂_ a t ≡ nothing → lift₂ _⋈_ a b ≡ nothing
         → (s ⊆? just 0ⁱ) × (a ⊑ᵃ? nothing)
  zero-ˡ s        (just a) t        (just b) _ _ _  _ _ ()
  zero-ˡ s        (just a) (just y) nothing  _ _ _  _ () _
  zero-ˡ s        (just a) nothing  nothing  _ q _  _ _ _ = ⊥-elim-irr q
  zero-ˡ nothing  nothing  t        b        _ _ _  _ _ _ = tt , tt
  zero-ˡ (just x) nothing  (just y) b        _ _ hs _ _ _ = ⊆ⁱ-0ⁱ-sumˡ x y hs , tt
  zero-ˡ (just x) nothing  nothing  (just b) _ _ _  () _ _
  zero-ˡ (just x) nothing  nothing  nothing  _ q _  _ _ _ = ⊥-elim-irr q

  zero-ʳ : ∀ s a t b → .(Inhabited s a) → .(Inhabited t b) → silent· s t ⊆? just 0ⁱ
         → lift₂ _▸_ s b ≡ nothing → lift₂ _◂_ a t ≡ nothing → lift₂ _⋈_ a b ≡ nothing
         → (t ⊆? just 0ⁱ) × (b ⊑ᵃ? nothing)
  zero-ʳ (just x) a        t        (just b) _ _ _  () _ _
  zero-ʳ nothing  (just a) t        (just b) _ _ _  _ _ ()
  zero-ʳ nothing  nothing  t        (just b) p _ _  _ _ _ = ⊥-elim-irr p
  zero-ʳ s        a        nothing  nothing  _ _ _  _ _ _ = tt , tt
  zero-ʳ (just x) a        (just y) nothing  _ _ hs _ _ _ = ⊆ⁱ-0ⁱ-sumʳ x y hs , tt
  zero-ʳ nothing  (just a) (just y) nothing  _ _ _  _ () _
  zero-ʳ nothing  nothing  (just y) nothing  p _ _  _ _ _ = ⊥-elim-irr p

  -- the three cases of an absent active part are absent

  cases-absent : ∀ s a t b → active· s a t b ≡ nothing
               → (lift₂ _▸_ s b ≡ nothing) × (lift₂ _◂_ a t ≡ nothing) × (lift₂ _⋈_ a b ≡ nothing)
  cases-absent s a t b n =
      ∨ᵃ?-nothingˡ P Q (∨ᵃ?-nothingˡ (P ∨ᵃ? Q) R n)
    , ∨ᵃ?-nothingʳ P Q (∨ᵃ?-nothingˡ (P ∨ᵃ? Q) R n)
    , ∨ᵃ?-nothingʳ (P ∨ᵃ? Q) R n
    where
      P = lift₂ _▸_ s b
      Q = lift₂ _◂_ a t
      R = lift₂ _⋈_ a b

⊑ᵉ-zero-productˡ : ∀ {e f} → e ·ᵉ f ⊑ᵉ 𝟏ᵉ → e ⊑ᵉ 𝟏ᵉ
⊑ᵉ-zero-productˡ {entry s a {p}} {entry t b {q}} (entry-⊑ hs ha)
  with cases-absent s a t b (⊑ᵃ?-nothing (active· s a t b) ha)
... | e₁ , e₂ , e₃ with zero-ˡ s a t b p q hs e₁ e₂ e₃
...   | r , r' = entry-⊑ r r'

⊑ᵉ-zero-productʳ : ∀ {e f} → e ·ᵉ f ⊑ᵉ 𝟏ᵉ → f ⊑ᵉ 𝟏ᵉ
⊑ᵉ-zero-productʳ {entry s a {p}} {entry t b {q}} (entry-⊑ hs ha)
  with cases-absent s a t b (⊑ᵃ?-nothing (active· s a t b) ha)
... | e₁ , e₂ , e₃ with zero-ʳ s a t b p q hs e₁ e₂ e₃
...   | r , r' = entry-⊑ r r'

------------------------------------------------------------------------
-- The grade of one operation

⊑ᵉ-reflexive : ∀ {e e'} → e ≡ e' → e ⊑ᵉ e'
⊑ᵉ-reflexive {e} refl = ⊑ᵉ-refl {e}

·ᵉ-distribˡ-⊑ : ∀ e f g → e ·ᵉ (f ⊔ᵉ g) ⊑ᵉ (e ·ᵉ f) ⊔ᵉ (e ·ᵉ g)
·ᵉ-distribˡ-⊑ e f g = ⊑ᵉ-reflexive (·ᵉ-distribˡ e f g)

·ᵉ-distribʳ-⊑ : ∀ e f g → (f ⊔ᵉ g) ·ᵉ e ⊑ᵉ (f ·ᵉ e) ⊔ᵉ (g ·ᵉ e)
·ᵉ-distribʳ-⊑ e f g = ⊑ᵉ-reflexive (·ᵉ-distribʳ e f g)

entry-poset : PosetGrade D
entry-poset = record
  { Carrier         = Entry
  ; _≾_             = _⊑ᵉ_
  ; 𝟏               = 𝟏ᵉ
  ; _·_             = _·ᵉ_
  ; ⊤               = ⊤ᵉ
  ; _⊔_             = _⊔ᵉ_
  ; ι               = ιᵉ
  ; ·-identityˡ     = ·ᵉ-identityˡ
  ; ·-identityʳ     = ·ᵉ-identityʳ
  ; ·-assoc         = ·ᵉ-assoc
  ; ≾-refl          = ⊑ᵉ-refl
  ; ≾-trans         = ⊑ᵉ-trans
  ; ≾-antisym       = ⊑ᵉ-antisym
  ; ≾-irrelevant    = ⊑ᵉ-irrelevant
  ; _≾?_            = _⊑ᵉ?_
  ; ≾-⊤             = ⊑ᵉ-⊤
  ; ⊔-ubˡ           = ⊔ᵉ-ubˡ
  ; ⊔-ubʳ           = ⊔ᵉ-ubʳ
  ; ⊔-lub           = ⊔ᵉ-lub
  ; ·-monoˡ-≾       = λ {g} p → ·ᵉ-mono p (⊑ᵉ-refl {g})
  ; ·-monoʳ-≾       = λ {g} p → ·ᵉ-mono (⊑ᵉ-refl {g}) p
  ; ·-distribˡ-⊔-≾  = ·ᵉ-distribˡ-⊑
  ; ·-distribʳ-⊔-≾  = ·ᵉ-distribʳ-⊑
  ; ≾-zero-productˡ = λ {e} {f} → ⊑ᵉ-zero-productˡ {e} {f}
  ; ≾-zero-productʳ = λ {e} {f} → ⊑ᵉ-zero-productʳ {e} {f}
  ; ι-zero          = refl
  ; ι-plus          = λ {τ} {τ'} → entry-≡ (cong just (pointⁱ-+ τ τ')) refl
  }

entryᵍ : Grade D
entryᵍ = posetᵍ entry-poset
