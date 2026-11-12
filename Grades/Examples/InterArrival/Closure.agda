------------------------------------------------------------------------
-- Closures of the inter-arrival grades of one operation.             --
--                                                                    --
-- The closure of an entry (`_⁺ᵉ`) has as its silent durations the    --
-- closure of those of the entry, `S` (`i⁺`: the same lower end, and  --
-- an upper end unbounded unless it is zero). Its active runs come    --
-- from those of the entry with silent parts between and around them  --
-- (`act⁺`): the count at least the least count of the entry, and     --
-- unbounded above; the reflexive closure `star S` of the silent      --
-- durations, zero or their closure, added to the lead time and to    --
-- the tail; and the tail, `star S` and the lead time a new gap.      --
--                                                                    --
-- It is above the entry, absorbs its own iteration, is the least     --
-- entry doing both, and satisfies both induction laws (`plusᵉ`). The --
-- hints of the grade of one operation (`entryʰ`) declare these       --
-- closures, the unit not least and the product not commutative.      --
------------------------------------------------------------------------

open import Grades.Durations

module Grades.Examples.InterArrival.Closure {D : Duration} (T : TimeDomain D) where

open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Nullary.Decidable using (True; toWitness; recompute)

open import Grades.Base
open import Grades.Hints using (GradeHints)
open import Grades.Examples.Time.Intervals T
import Grades.Examples.Time.Interval as C
open import Grades.Examples.InterArrival.Options
open import Grades.Examples.InterArrival.Entry T

open import Util.Equality using (_≡_; refl; sym; trans; cong; subst; isEquivalence)

------------------------------------------------------------------------
-- Reasoning about intervals

private
  ℐ : Preorder 0ℓ 0ℓ 0ℓ
  ℐ = record
    { Carrier    = Interval
    ; _≈_        = _≡_
    ; _≲_        = _⊆ⁱ_
    ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ { {i} refl → ⊆ⁱ-refl {i} }
      ; trans         = λ {i} {j} {k} → ⊆ⁱ-trans {i} {j} {k} } }

open import Relation.Binary.Reasoning.Preorder ℐ

private
  module JOI = JoinOrder _⊆ⁱ_ _∪ⁱ_ (λ {i} → ⊆ⁱ-refl {i}) (λ {i} {j} {k} → ⊆ⁱ-trans {i} {j} {k})
                 ∪ⁱ-ubˡ ∪ⁱ-ubʳ (λ {i} {j} {k} → ∪ⁱ-lub {i} {j} {k})
  module OA = Order _⊑ᵃ_
  module JOA = JoinOrder _⊑ᵃ_ _∨ᵃ_ ⊑ᵃ-refl ⊑ᵃ-trans ∨ᵃ-ubˡ ∨ᵃ-ubʳ ∨ᵃ-lub

  ⊆-≡ : ∀ {i j} → i ≡ j → i ⊆ⁱ j
  ⊆-≡ {i} refl = ⊆ⁱ-refl {i}

  tr? : ∀ u v w → u ⊆? v → v ⊆? w → u ⊆? w
  tr? u v w = ⊆?-trans (λ {i} {j} {k} → ⊆ⁱ-trans {i} {j} {k}) {u} {v} {w}

  trᵃ? : ∀ u v w → u ⊑ᵃ? v → v ⊑ᵃ? w → u ⊑ᵃ? w
  trᵃ? u v w = OA.⊑?-trans ⊑ᵃ-trans {u} {v} {w}

  -- the three parts of a join of three below a bound

  split₃ : ∀ x y z c → (x ∪? y) ∪? z ⊆? c → (x ⊆? c) × (y ⊆? c) × (z ⊆? c)
  split₃ x y z c h =
      tr? x (x ∪? y) c (JOI.∨?-ubˡ x y) xy
    , tr? y (x ∪? y) c (JOI.∨?-ubʳ x y) xy
    , tr? z ((x ∪? y) ∪? z) c (JOI.∨?-ubʳ (x ∪? y) z) h
    where
      xy = tr? (x ∪? y) ((x ∪? y) ∪? z) c (JOI.∨?-ubˡ (x ∪? y) z) h

  join₃ : ∀ x y z c → x ⊆? c → y ⊆? c → z ⊆? c → (x ∪? y) ∪? z ⊆? c
  join₃ x y z c p q r = JOI.∨?-lub {x ∪? y} {z} {c} (JOI.∨?-lub {x} {y} {c} p q) r

  splitᵃ₃ : ∀ x y z c → (x ∨ᵃ? y) ∨ᵃ? z ⊑ᵃ? c → (x ⊑ᵃ? c) × (y ⊑ᵃ? c) × (z ⊑ᵃ? c)
  splitᵃ₃ x y z c h =
      trᵃ? x (x ∨ᵃ? y) c (JOA.∨?-ubˡ x y) xy
    , trᵃ? y (x ∨ᵃ? y) c (JOA.∨?-ubʳ x y) xy
    , trᵃ? z ((x ∨ᵃ? y) ∨ᵃ? z) c (JOA.∨?-ubʳ (x ∨ᵃ? y) z) h
    where
      xy = trᵃ? (x ∨ᵃ? y) ((x ∨ᵃ? y) ∨ᵃ? z) c (JOA.∨?-ubˡ (x ∨ᵃ? y) z) h

  joinᵃ₃ : ∀ x y z c → x ⊑ᵃ? c → y ⊑ᵃ? c → z ⊑ᵃ? c → (x ∨ᵃ? y) ∨ᵃ? z ⊑ᵃ? c
  joinᵃ₃ x y z c p q r = JOA.∨?-lub {x ∨ᵃ? y} {z} {c} (JOA.∨?-lub {x} {y} {c} p q) r

------------------------------------------------------------------------
-- The closure of the silent durations, and their reflexive closure
-- `star`, which a silent part of a power may add to a lead time, a gap
-- or a tail

private
  module P (s : Interval) = Plus (plusⁱ s)

star : Maybe Interval → Interval
star nothing  = 0ⁱ
star (just s) = 0ⁱ ∪ⁱ i⁺ s

private
  0-star : ∀ S → 0ⁱ ⊆ⁱ star S
  0-star nothing  = ⊆ⁱ-refl {0ⁱ}
  0-star (just s) = ∪ⁱ-ubˡ 0ⁱ (i⁺ s)

  -- `star S` is absorbed where every silent duration of `S` is

  star-indˡ : ∀ S d → lift₂ _⊕_ S (just d) ⊆? just d → star S ⊕ d ⊆ⁱ d
  star-indˡ nothing  d _ = ⊆-≡ (⊕-identityˡ d)
  star-indˡ (just s) d h = begin
    (0ⁱ ∪ⁱ i⁺ s) ⊕ d        ≡⟨ ⊕-distribʳ d 0ⁱ (i⁺ s) ⟩
    (0ⁱ ⊕ d) ∪ⁱ (i⁺ s ⊕ d)  ≲⟨ ∪ⁱ-lub {0ⁱ ⊕ d} {i⁺ s ⊕ d} {d} (⊆-≡ (⊕-identityˡ d)) (P.⁺-indˡ s {d} h) ⟩
    d                       ∎

  star-indʳ : ∀ S d → lift₂ _⊕_ (just d) S ⊆? just d → d ⊕ star S ⊆ⁱ d
  star-indʳ nothing  d _ = ⊆-≡ (⊕-identityʳ d)
  star-indʳ (just s) d h = begin
    d ⊕ (0ⁱ ∪ⁱ i⁺ s)        ≡⟨ ⊕-distribˡ d 0ⁱ (i⁺ s) ⟩
    (d ⊕ 0ⁱ) ∪ⁱ (d ⊕ i⁺ s)  ≲⟨ ∪ⁱ-lub {d ⊕ 0ⁱ} {d ⊕ i⁺ s} {d} (⊆-≡ (⊕-identityʳ d)) (P.⁺-indʳ s {d} h) ⟩
    d                       ∎

  -- a silent duration of `S` is absorbed by `star S`

  s-star : ∀ s → s ⊕ star (just s) ⊆ⁱ star (just s)
  s-star s = begin
    s ⊕ (0ⁱ ∪ⁱ i⁺ s)        ≡⟨ ⊕-distribˡ s 0ⁱ (i⁺ s) ⟩
    (s ⊕ 0ⁱ) ∪ⁱ (s ⊕ i⁺ s)  ≲⟨ ∪ⁱ-lub {s ⊕ 0ⁱ} {s ⊕ i⁺ s} {i⁺ s}
                                (⊆ⁱ-trans {s ⊕ 0ⁱ} {s} {i⁺ s} (⊆-≡ (⊕-identityʳ s)) (P.≾-c⁺ s))
                                (⊆ⁱ-trans {s ⊕ i⁺ s} {i⁺ s ⊕ i⁺ s} {i⁺ s}
                                   (⊕-mono₂ {s} {i⁺ s} {i⁺ s} {i⁺ s} (P.≾-c⁺ s) (⊆ⁱ-refl {i⁺ s}))
                                   (P.c⁺-iter s)) ⟩
    i⁺ s                    ≲⟨ ∪ⁱ-ubʳ 0ⁱ (i⁺ s) ⟩
    0ⁱ ∪ⁱ i⁺ s              ∎

  star-s : ∀ s → star (just s) ⊕ s ⊆ⁱ star (just s)
  star-s s = subst (_⊆ⁱ star (just s)) (⊕-comm s (star (just s))) (s-star s)

  i⁺-star : ∀ s → i⁺ s ⊕ star (just s) ⊆ⁱ star (just s)
  i⁺-star s = P.⁺-indˡ s {star (just s)} (s-star s)

  star-i⁺ : ∀ s → star (just s) ⊕ i⁺ s ⊆ⁱ star (just s)
  star-i⁺ s = P.⁺-indʳ s {star (just s)} (star-s s)

  star-iter : ∀ S → star S ⊕ star S ⊆ⁱ star S
  star-iter S = star-indˡ S (star S) (h S)
    where
      h : ∀ S → lift₂ _⊕_ S (just (star S)) ⊆? just (star S)
      h nothing  = tt
      h (just s) = s-star s

  -- a bound absorbing the silent durations of a larger `S'` absorbs
  -- those of `S`

  absˡ-mono : ∀ S S' d → S ⊆? S' → lift₂ _⊕_ S' (just d) ⊆? just d → lift₂ _⊕_ S (just d) ⊆? just d
  absˡ-mono (just s) (just s') d p h =
    ⊆ⁱ-trans {s ⊕ d} {s' ⊕ d} {d} (⊕-mono₂ {s} {s'} {d} {d} p (⊆ⁱ-refl {d})) h
  absˡ-mono nothing  _         d _ _ = tt

  absʳ-mono : ∀ S S' d → S ⊆? S' → lift₂ _⊕_ (just d) S' ⊆? just d → lift₂ _⊕_ (just d) S ⊆? just d
  absʳ-mono (just s) (just s') d p h =
    ⊆ⁱ-trans {d ⊕ s} {d ⊕ s'} {d} (⊕-mono₂ {d} {d} {s} {s'} (⊆ⁱ-refl {d}) p) h
  absʳ-mono nothing  _         d _ _ = tt

------------------------------------------------------------------------
-- Counts: the closure of a count is unbounded above

count⁺ : C.Interval∞ → C.Interval∞
count⁺ k = C.[ C.min k , C.∞ ]

private
  -- a count added to which `m` does not grow, and which is positive,
  -- leaves `m` unbounded above

  +∞-absorbs : ∀ a b → (a C.+∞ b) C.≤∞ b → C.↑ 1 C.≤∞ a → b ≡ C.∞
  +∞-absorbs (C.↑ j) (C.↑ n) p q = ⊥-elim (ℕₚ.1+n≰n (ℕₚ.≤-trans (ℕₚ.+-monoˡ-≤ n q) p))
  +∞-absorbs C.∞     (C.↑ n) () _
  +∞-absorbs _       C.∞     _ _ = refl

  max-positive : ∀ k → 1 ℕ.≤ C.min k → C.↑ 1 C.≤∞ C.max k
  max-positive k p = C.≤∞-trans {C.↑ 1} {C.↑ C.min k} {C.max k} p (C.min≤max k)

  unboundedˡ : ∀ k m → (k C.·ᵢ m) C.≾ᵢ m → 1 ℕ.≤ C.min k → C.max m ≡ C.∞
  unboundedˡ k m h p = +∞-absorbs (C.max k) (C.max m) (proj₂ h) (max-positive k p)

  unboundedʳ : ∀ k m → (m C.·ᵢ k) C.≾ᵢ m → 1 ℕ.≤ C.min k → C.max m ≡ C.∞
  unboundedʳ k m h p =
    +∞-absorbs (C.max k) (C.max m)
      (subst (C._≤∞ C.max m) (C.+∞-comm (C.max m) (C.max k)) (proj₂ h)) (max-positive k p)

  ≤∞-∞ : ∀ {a} → a ≡ C.∞ → C.∞ C.≤∞ a
  ≤∞-∞ refl = tt

  count-⁺ : ∀ k → k C.≾ᵢ count⁺ k
  count-⁺ k = ℕₚ.≤-refl , C.≤∞-∞ (C.max k)

  count⁺-iter : ∀ k → (count⁺ k C.·ᵢ count⁺ k) C.≾ᵢ count⁺ k
  count⁺-iter k = ℕₚ.m≤m+n (C.min k) (C.min k) , tt

  count⁺-⊆ : ∀ k m → C.min m ℕ.≤ C.min k → C.max m ≡ C.∞ → count⁺ k C.≾ᵢ m
  count⁺-⊆ k m p e = p , ≤∞-∞ e

  count⁺-·ˡ : ∀ k m → C.max m ≡ C.∞ → (count⁺ k C.·ᵢ m) C.≾ᵢ m
  count⁺-·ˡ k m e = ℕₚ.m≤n+m (C.min m) (C.min k) , ≤∞-∞ e

  count⁺-·ʳ : ∀ k m → C.max m ≡ C.∞ → (m C.·ᵢ count⁺ k) C.≾ᵢ m
  count⁺-·ʳ k m e =
    ℕₚ.m≤m+n (C.min m) (C.min k) , subst (C._≤∞ C.max m) (C.+∞-comm C.∞ (C.max m)) (≤∞-∞ e)

  pos : ∀ {k} → .(True (1 ℕₚ.≤? C.min k)) → 1 ℕ.≤ C.min k
  pos {k} p = recompute (1 ℕₚ.≤? C.min k) (toWitness p)

------------------------------------------------------------------------
-- The closure of an active summary, under the silent durations `S`:
-- the counts unbounded above, `star S` added to the lead time and to
-- the tail, and the tail, `star S` and the lead time a gap

act⁺ : Maybe Interval → Act → Act
act⁺ S (act k l g t {p}) =
  act (count⁺ k) (star S ⊕ l) (g ∪? just ((t ⊕ star S) ⊕ l)) (t ⊕ star S) {p}

private
  -- the components of a closure below those of `b`

  lead⁺-⊆ : ∀ S l n → l ⊆ⁱ n → lift₂ _⊕_ S (just n) ⊆? just n → star S ⊕ l ⊆ⁱ n
  lead⁺-⊆ S l n p h = begin
    star S ⊕ l  ≲⟨ ⊕-mono₂ {star S} {star S} {l} {n} (⊆ⁱ-refl {star S}) p ⟩
    star S ⊕ n  ≲⟨ star-indˡ S n h ⟩
    n           ∎

  tail⁺-⊆ : ∀ S t u → t ⊆ⁱ u → lift₂ _⊕_ (just u) S ⊆? just u → t ⊕ star S ⊆ⁱ u
  tail⁺-⊆ S t u p h = begin
    t ⊕ star S  ≲⟨ ⊕-mono₂ {t} {u} {star S} {star S} p (⊆ⁱ-refl {star S}) ⟩
    u ⊕ star S  ≲⟨ star-indʳ S u h ⟩
    u           ∎

  -- a new gap within the gaps `h` of `b`, from the lead time or from
  -- the tail

  gap⁺-⊆ˡ : ∀ S t l n h → just (t ⊕ n) ⊆? h → star S ⊕ l ⊆ⁱ n → just ((t ⊕ star S) ⊕ l) ⊆? h
  gap⁺-⊆ˡ S t l n h q p =
    tr? (just ((t ⊕ star S) ⊕ l)) (just (t ⊕ n)) h
      (begin
         (t ⊕ star S) ⊕ l  ≡⟨ ⊕-assoc t (star S) l ⟩
         t ⊕ (star S ⊕ l)  ≲⟨ ⊕-mono₂ {t} {t} {star S ⊕ l} {n} (⊆ⁱ-refl {t}) p ⟩
         t ⊕ n             ∎)
      q

  gap⁺-⊆ʳ : ∀ S t l u h → just (u ⊕ l) ⊆? h → t ⊕ star S ⊆ⁱ u → just ((t ⊕ star S) ⊕ l) ⊆? h
  gap⁺-⊆ʳ S t l u h q p =
    tr? (just ((t ⊕ star S) ⊕ l)) (just (u ⊕ l)) h
      (⊕-mono₂ {t ⊕ star S} {u} {l} {l} p (⊆ⁱ-refl {l})) q

  gaps⁺-⊆ : ∀ g x h → g ⊆? h → just x ⊆? h → g ∪? just x ⊆? h
  gaps⁺-⊆ g x h p q = JOI.∨?-lub {g} {just x} {h} p q

  -- a silent part before or after `b` absorbed by it

  ▸-absorbs : ∀ S b → lift₂ _▸_ S (just b) ⊑ᵃ? just b → lift₂ _⊕_ S (just (lead b)) ⊆? just (lead b)
  ▸-absorbs (just w) (act k l g t) h = lead-⊑ h
  ▸-absorbs nothing  b             _ = tt

  ◂-absorbs : ∀ b S → lift₂ _◂_ (just b) S ⊑ᵃ? just b → lift₂ _⊕_ (just (tail b)) S ⊆? just (tail b)
  ◂-absorbs (act k l g t) (just w) h = tail-⊑ h
  ◂-absorbs b             nothing  _ = tt

  -- the gaps of `b ⋈ b'` below those of `c`

  ⋈-gaps : ∀ b b' c → b ⋈ b' ⊑ᵃ c
         → (gaps b ⊆? gaps c) × (gaps b' ⊆? gaps c) × (just (tail b ⊕ lead b') ⊆? gaps c)
  ⋈-gaps (act k l g t) (act k' l' g' t') c h = split₃ g g' (just (t ⊕ l')) (gaps c) (gaps-⊑ h)

  -- an active summary is below its closure

  ⊑-act⁺ : ∀ S a → a ⊑ᵃ act⁺ S a
  ⊑-act⁺ S (act k l g t) =
    act-⊑ (count-⁺ k)
          (begin l ≡⟨ sym (⊕-identityˡ l) ⟩ 0ⁱ ⊕ l
                   ≲⟨ ⊕-mono₂ {0ⁱ} {star S} {l} {l} (0-star S) (⊆ⁱ-refl {l}) ⟩ star S ⊕ l ∎)
          (JOI.∨?-ubˡ g (just ((t ⊕ star S) ⊕ l)))
          (begin t ≡⟨ sym (⊕-identityʳ t) ⟩ t ⊕ 0ⁱ
                   ≲⟨ ⊕-mono₂ {t} {t} {0ⁱ} {star S} (⊆ⁱ-refl {t}) (0-star S) ⟩ t ⊕ star S ∎)

  -- the closure absorbs its own silent durations and its own iteration

  i⁺-▸-act⁺ : ∀ s a → i⁺ s ▸ act⁺ (just s) a ⊑ᵃ act⁺ (just s) a
  i⁺-▸-act⁺ s (act k l g t) =
    act-⊑ (ℕₚ.≤-refl , tt)
          (begin
             i⁺ s ⊕ (star (just s) ⊕ l)  ≡⟨ sym (⊕-assoc (i⁺ s) (star (just s)) l) ⟩
             (i⁺ s ⊕ star (just s)) ⊕ l  ≲⟨ ⊕-mono₂ {i⁺ s ⊕ star (just s)} {star (just s)} {l} {l}
                                               (i⁺-star s) (⊆ⁱ-refl {l}) ⟩
             star (just s) ⊕ l           ∎)
          (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {g ∪? just ((t ⊕ star (just s)) ⊕ l)})
          (⊆ⁱ-refl {t ⊕ star (just s)})

  act⁺-◂-i⁺ : ∀ s a → act⁺ (just s) a ◂ i⁺ s ⊑ᵃ act⁺ (just s) a
  act⁺-◂-i⁺ s (act k l g t) =
    act-⊑ (ℕₚ.≤-refl , tt)
          (⊆ⁱ-refl {star (just s) ⊕ l})
          (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {g ∪? just ((t ⊕ star (just s)) ⊕ l)})
          (begin
             (t ⊕ star (just s)) ⊕ i⁺ s  ≡⟨ ⊕-assoc t (star (just s)) (i⁺ s) ⟩
             t ⊕ (star (just s) ⊕ i⁺ s)  ≲⟨ ⊕-mono₂ {t} {t} {star (just s) ⊕ i⁺ s} {star (just s)}
                                               (⊆ⁱ-refl {t}) (star-i⁺ s) ⟩
             t ⊕ star (just s)           ∎)

  act⁺-⋈-act⁺ : ∀ S a → act⁺ S a ⋈ act⁺ S a ⊑ᵃ act⁺ S a
  act⁺-⋈-act⁺ S (act k l g t) =
    act-⊑ (count⁺-iter k)
          (⊆ⁱ-refl {star S ⊕ l})
          (join₃ g⁺ g⁺ (just ((t ⊕ star S) ⊕ (star S ⊕ l))) g⁺
                 (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {g⁺}) (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {g⁺})
                 (tr? (just ((t ⊕ star S) ⊕ (star S ⊕ l))) (just ((t ⊕ star S) ⊕ l)) g⁺
                      (begin
                         (t ⊕ star S) ⊕ (star S ⊕ l)  ≡⟨ ⊕-assoc t (star S) (star S ⊕ l) ⟩
                         t ⊕ (star S ⊕ (star S ⊕ l))  ≡⟨ cong (t ⊕_) (sym (⊕-assoc (star S) (star S) l)) ⟩
                         t ⊕ ((star S ⊕ star S) ⊕ l)  ≲⟨ ⊕-mono₂ {t} {t} {(star S ⊕ star S) ⊕ l} {star S ⊕ l}
                                                            (⊆ⁱ-refl {t})
                                                            (⊕-mono₂ {star S ⊕ star S} {star S} {l} {l}
                                                               (star-iter S) (⊆ⁱ-refl {l})) ⟩
                         t ⊕ (star S ⊕ l)             ≡⟨ sym (⊕-assoc t (star S) l) ⟩
                         (t ⊕ star S) ⊕ l             ∎)
                      (JOI.∨?-ubʳ g (just ((t ⊕ star S) ⊕ l)))))
          (⊆ⁱ-refl {t ⊕ star S})
    where
      g⁺ = g ∪? just ((t ⊕ star S) ⊕ l)

------------------------------------------------------------------------
-- The closure of an entry: the closure of its silent durations, and
-- the closure of its active summaries under them

private
  inhabited⁺ : ∀ S A → .(Inhabited S A) → Inhabited (mapᴹ i⁺ S) (mapᴹ (act⁺ S) A)
  inhabited⁺ (just _) _        _ = tt
  inhabited⁺ nothing  (just _) _ = tt

_⁺ᵉ : Entry → Entry
entry S A {p} ⁺ᵉ = entry (mapᴹ i⁺ S) (mapᴹ (act⁺ S) A) {inhabited⁺ S A p}

-- it is above the entry

⊑ᵉ-⁺ : ∀ e → e ⊑ᵉ e ⁺ᵉ
⊑ᵉ-⁺ (entry S A) = entry-⊑ (silent⁺ S) (active⁺ A)
  where
    silent⁺ : ∀ S → S ⊆? mapᴹ i⁺ S
    silent⁺ (just s) = P.≾-c⁺ s
    silent⁺ nothing  = tt
    active⁺ : ∀ A → A ⊑ᵃ? mapᴹ (act⁺ S) A
    active⁺ (just a) = ⊑-act⁺ S a
    active⁺ nothing  = tt

-- it absorbs its own iteration

⁺ᵉ-iter : ∀ e → e ⁺ᵉ ·ᵉ e ⁺ᵉ ⊑ᵉ e ⁺ᵉ
⁺ᵉ-iter (entry (just s) (just a)) =
  entry-⊑ (P.c⁺-iter s) (∨ᵃ-lub (∨ᵃ-lub (i⁺-▸-act⁺ s a) (act⁺-◂-i⁺ s a)) (act⁺-⋈-act⁺ (just s) a))
⁺ᵉ-iter (entry (just s) nothing)  = entry-⊑ (P.c⁺-iter s) tt
⁺ᵉ-iter (entry nothing  (just a)) = entry-⊑ tt (act⁺-⋈-act⁺ nothing a)
⁺ᵉ-iter (entry nothing  nothing)  = entry-⊑ tt tt

-- it is the least entry above `e` absorbing its own iteration

⁺ᵉ-least : ∀ e {v} → e ⊑ᵉ v → v ·ᵉ v ⊑ᵉ v → e ⁺ᵉ ⊑ᵉ v
⁺ᵉ-least (entry S A) {entry Sv Av} (entry-⊑ hs ha) (entry-⊑ vs va) =
  entry-⊑ (sil S Sv hs vs) (actv S A Sv Av hs ha va)
  where
    sil : ∀ S Sv → S ⊆? Sv → silent· Sv Sv ⊆? Sv → mapᴹ i⁺ S ⊆? Sv
    sil (just s) (just w) p q = P.c⁺-least s {w} p q
    sil (just s) nothing  () _
    sil nothing  _        _ _ = tt

    actv : ∀ S A Sv Av → S ⊆? Sv → A ⊑ᵃ? Av → active· Sv Av Sv Av ⊑ᵃ? Av
           → mapᴹ (act⁺ S) A ⊑ᵃ? Av
    actv S nothing  Sv Av      _ _  _ = tt
    actv S (just _) Sv nothing _ () _
    actv S (just (act k l g t)) Sv (just (act m n h u {q})) p (act-⊑ c₁ l₁ g₁ t₁) va =
      act-⊑ (count⁺-⊆ k m (proj₁ c₁) (unboundedˡ m m (count-⊑ v⋈v) (pos {m} q)))
            (lead⁺-⊆ S l n l₁ absˡ)
            (gaps⁺-⊆ g ((t ⊕ star S) ⊕ l) h g₁
               (gap⁺-⊆ˡ S t l n h
                  (tr? (just (t ⊕ n)) (just (u ⊕ n)) h
                       (⊕-mono₂ {t} {u} {n} {n} t₁ (⊆ⁱ-refl {n})) (proj₂ (proj₂ (⋈-gaps c c c v⋈v))))
                  (lead⁺-⊆ S l n l₁ absˡ)))
            (tail⁺-⊆ S t u t₁ absʳ)
      where
        c = act m n h u {q}
        parts = splitᵃ₃ (lift₂ _▸_ Sv (just c)) (lift₂ _◂_ (just c) Sv) (just (c ⋈ c)) (just c) va
        v⋈v : c ⋈ c ⊑ᵃ c
        v⋈v = proj₂ (proj₂ parts)
        absˡ : lift₂ _⊕_ S (just n) ⊆? just n
        absˡ = absˡ-mono S Sv n p (▸-absorbs Sv c (proj₁ parts))
        absʳ : lift₂ _⊕_ (just u) S ⊆? just u
        absʳ = absʳ-mono S Sv u p (◂-absorbs c Sv (proj₁ (proj₂ parts)))

-- induction: an entry that `e` does not move, on either side, its
-- closure does not move either

⁺ᵉ-indˡ : ∀ e {d} → e ·ᵉ d ⊑ᵉ d → e ⁺ᵉ ·ᵉ d ⊑ᵉ d
⁺ᵉ-indˡ (entry S A) {entry Sd Ad} (entry-⊑ hs ha) =
  entry-⊑ (sil S Sd hs)
          (joinᵃ₃ (lift₂ _▸_ (mapᴹ i⁺ S) Ad) (lift₂ _◂_ (mapᴹ (act⁺ S) A) Sd)
                  (lift₂ _⋈_ (mapᴹ (act⁺ S) A) Ad) Ad
                  (pre S Ad h▸) (post S A Sd Ad hs h▸ h◂ h⋈) (both S A Ad h▸ h⋈))
  where
    parts = splitᵃ₃ (lift₂ _▸_ S Ad) (lift₂ _◂_ A Sd) (lift₂ _⋈_ A Ad) Ad ha
    h▸ = proj₁ parts
    h◂ = proj₁ (proj₂ parts)
    h⋈ = proj₂ (proj₂ parts)

    sil : ∀ S Sd → silent· S Sd ⊆? Sd → silent· (mapᴹ i⁺ S) Sd ⊆? Sd
    sil (just s) (just w) h = P.⁺-indˡ s {w} h
    sil (just s) nothing  _ = tt
    sil nothing  _        _ = tt

    -- the silent durations of the closure before an active part of `d`

    pre : ∀ S Ad → lift₂ _▸_ S Ad ⊑ᵃ? Ad → lift₂ _▸_ (mapᴹ i⁺ S) Ad ⊑ᵃ? Ad
    pre (just s) (just (act m n h u)) p =
      act-⊑ (ℕₚ.≤-refl , C.≤∞-refl {C.max m}) (P.⁺-indˡ s {n} (lead-⊑ p))
            (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {h}) (⊆ⁱ-refl {u})
    pre (just s) nothing _ = tt
    pre nothing  _       _ = tt

    -- an active part of the closure before a silent part of `d`

    post : ∀ S A Sd Ad → silent· S Sd ⊆? Sd → lift₂ _▸_ S Ad ⊑ᵃ? Ad
         → lift₂ _◂_ A Sd ⊑ᵃ? Ad → lift₂ _⋈_ A Ad ⊑ᵃ? Ad
         → lift₂ _◂_ (mapᴹ (act⁺ S) A) Sd ⊑ᵃ? Ad
    post S (just (act k l g t {p})) (just w) (just (act m n h u {q})) hs p▸ p◂ p⋈ =
      act-⊑ (count⁺-⊆ k m (proj₁ (count-⊑ p◂)) (unboundedˡ k m (count-⊑ p⋈) (pos {k} p)))
            lead⁺
            (gaps⁺-⊆ g ((t ⊕ star S) ⊕ l) h (gaps-⊑ p◂)
               (gap⁺-⊆ˡ S t l n h (proj₂ (proj₂ (⋈-gaps a c c p⋈))) lead⁺))
            (begin
               (t ⊕ star S) ⊕ w  ≡⟨ ⊕-assoc t (star S) w ⟩
               t ⊕ (star S ⊕ w)  ≲⟨ ⊕-mono₂ {t} {t} {star S ⊕ w} {w} (⊆ⁱ-refl {t}) (star-indˡ S w hs) ⟩
               t ⊕ w             ≲⟨ tail-⊑ p◂ ⟩
               u                 ∎)
      where
        a = act k l g t {p}
        c = act m n h u {q}
        lead⁺ : star S ⊕ l ⊆ⁱ n
        lead⁺ = lead⁺-⊆ S l n (lead-⊑ p◂) (▸-absorbs S c p▸)
    post S nothing  _        _        _ _ _  _ = tt
    post S (just _) nothing  _        _ _ _  _ = tt
    post S (just _) (just _) nothing  _ _ () _

    -- an active part of the closure before an active part of `d`

    both : ∀ S A Ad → lift₂ _▸_ S Ad ⊑ᵃ? Ad → lift₂ _⋈_ A Ad ⊑ᵃ? Ad
         → lift₂ _⋈_ (mapᴹ (act⁺ S) A) Ad ⊑ᵃ? Ad
    both S (just (act k l g t {p})) (just (act m n h u {q})) p▸ p⋈ =
      act-⊑ (count⁺-·ˡ k m (unboundedˡ k m (count-⊑ p⋈) (pos {k} p)))
            lead⁺
            (join₃ (g ∪? just ((t ⊕ star S) ⊕ l)) h (just ((t ⊕ star S) ⊕ n)) h
                   (gaps⁺-⊆ g ((t ⊕ star S) ⊕ l) h (proj₁ gs) (gap⁺-⊆ˡ S t l n h tn lead⁺))
                   (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {h})
                   (gap⁺-⊆ˡ S t n n h tn (star-indˡ S n absˡ)))
            (⊆ⁱ-refl {u})
      where
        a = act k l g t {p}
        c = act m n h u {q}
        absˡ = ▸-absorbs S c p▸
        lead⁺ : star S ⊕ l ⊆ⁱ n
        lead⁺ = lead⁺-⊆ S l n (lead-⊑ p⋈) absˡ
        gs = ⋈-gaps a c c p⋈
        tn = proj₂ (proj₂ gs)
    both S nothing  _        _ _ = tt
    both S (just _) nothing  _ _ = tt

⁺ᵉ-indʳ : ∀ e {d} → d ·ᵉ e ⊑ᵉ d → d ·ᵉ e ⁺ᵉ ⊑ᵉ d
⁺ᵉ-indʳ (entry S A) {entry Sd Ad} (entry-⊑ hs ha) =
  entry-⊑ (sil S Sd hs)
          (joinᵃ₃ (lift₂ _▸_ Sd (mapᴹ (act⁺ S) A)) (lift₂ _◂_ Ad (mapᴹ i⁺ S))
                  (lift₂ _⋈_ Ad (mapᴹ (act⁺ S) A)) Ad
                  (pre S A Sd Ad hs h▸ h◂ h⋈) (post S Ad h◂) (both S A Ad h◂ h⋈))
  where
    parts = splitᵃ₃ (lift₂ _▸_ Sd A) (lift₂ _◂_ Ad S) (lift₂ _⋈_ Ad A) Ad ha
    h▸ = proj₁ parts
    h◂ = proj₁ (proj₂ parts)
    h⋈ = proj₂ (proj₂ parts)

    sil : ∀ S Sd → silent· Sd S ⊆? Sd → silent· Sd (mapᴹ i⁺ S) ⊆? Sd
    sil (just s) (just w) h = P.⁺-indʳ s {w} h
    sil (just s) nothing  _ = tt
    sil nothing  (just w) _ = tt
    sil nothing  nothing  _ = tt

    -- a silent part of `d` before an active part of the closure

    pre : ∀ S A Sd Ad → silent· Sd S ⊆? Sd → lift₂ _▸_ Sd A ⊑ᵃ? Ad
        → lift₂ _◂_ Ad S ⊑ᵃ? Ad → lift₂ _⋈_ Ad A ⊑ᵃ? Ad
        → lift₂ _▸_ Sd (mapᴹ (act⁺ S) A) ⊑ᵃ? Ad
    pre S (just (act k l g t {p})) (just w) (just (act m n h u {q})) hs p▸ p◂ p⋈ =
      act-⊑ (count⁺-⊆ k m (proj₁ (count-⊑ p▸)) (unboundedʳ k m (count-⊑ p⋈) (pos {k} p)))
            (begin
               w ⊕ (star S ⊕ l)  ≡⟨ sym (⊕-assoc w (star S) l) ⟩
               (w ⊕ star S) ⊕ l  ≲⟨ ⊕-mono₂ {w ⊕ star S} {w} {l} {l} (star-indʳ S w hs) (⊆ⁱ-refl {l}) ⟩
               w ⊕ l             ≲⟨ lead-⊑ p▸ ⟩
               n                 ∎)
            (gaps⁺-⊆ g ((t ⊕ star S) ⊕ l) h (gaps-⊑ p▸)
               (gap⁺-⊆ʳ S t l u h (proj₂ (proj₂ (⋈-gaps c a c p⋈))) tail⁺))
            tail⁺
      where
        a = act k l g t {p}
        c = act m n h u {q}
        tail⁺ : t ⊕ star S ⊆ⁱ u
        tail⁺ = tail⁺-⊆ S t u (tail-⊑ p▸) (◂-absorbs c S p◂)
    pre S nothing  (just _) _       _ _  _ _ = tt
    pre S nothing  nothing  _       _ _  _ _ = tt
    pre S (just _) nothing  _       _ _  _ _ = tt
    pre S (just _) (just _) nothing _ () _ _

    -- an active part of `d` before the silent durations of the closure

    post : ∀ S Ad → lift₂ _◂_ Ad S ⊑ᵃ? Ad → lift₂ _◂_ Ad (mapᴹ i⁺ S) ⊑ᵃ? Ad
    post (just s) (just (act m n h u)) p =
      act-⊑ (ℕₚ.≤-refl , C.≤∞-refl {C.max m}) (⊆ⁱ-refl {n})
            (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {h}) (P.⁺-indʳ s {u} (tail-⊑ p))
    post (just s) nothing  _ = tt
    post nothing  (just _) _ = tt
    post nothing  nothing  _ = tt

    -- an active part of `d` before an active part of the closure

    both : ∀ S A Ad → lift₂ _◂_ Ad S ⊑ᵃ? Ad → lift₂ _⋈_ Ad A ⊑ᵃ? Ad
         → lift₂ _⋈_ Ad (mapᴹ (act⁺ S) A) ⊑ᵃ? Ad
    both S (just (act k l g t {p})) (just (act m n h u {q})) p◂ p⋈ =
      act-⊑ (count⁺-·ʳ k m (unboundedʳ k m (count-⊑ p⋈) (pos {k} p)))
            (⊆ⁱ-refl {n})
            (join₃ h (g ∪? just ((t ⊕ star S) ⊕ l)) (just (u ⊕ (star S ⊕ l))) h
                   (⊆?-refl (λ {i} → ⊆ⁱ-refl {i}) {h})
                   (gaps⁺-⊆ g ((t ⊕ star S) ⊕ l) h (proj₁ (proj₂ gs)) (gap⁺-⊆ʳ S t l u h ul tail⁺))
                   (tr? (just (u ⊕ (star S ⊕ l))) (just ((u ⊕ star S) ⊕ l)) h
                        (⊆-≡ (sym (⊕-assoc u (star S) l)))
                        (gap⁺-⊆ʳ S u l u h ul (tail⁺-⊆ S u u (⊆ⁱ-refl {u}) absʳ))))
            tail⁺
      where
        a = act k l g t {p}
        c = act m n h u {q}
        gs = ⋈-gaps c a c p⋈
        ul = proj₂ (proj₂ gs)
        absʳ = ◂-absorbs c S p◂
        tail⁺ : t ⊕ star S ⊆ⁱ u
        tail⁺ = tail⁺-⊆ S t u (tail-⊑ p⋈) absʳ
    both S nothing  (just _) _ _ = tt
    both S nothing  nothing  _ _ = tt
    both S (just _) nothing  _ _ = tt

------------------------------------------------------------------------
-- The closures, and the hints of the grade of one operation: the unit
-- is not least and the product does not commute
-- (`Grades.Examples.Worked.InterArrival`)

plusᵉ : (e : Entry) → Plus _·ᵉ_ _⊑ᵉ_ e
plusᵉ e = plus (e ⁺ᵉ) (⊑ᵉ-⁺ e) (⁺ᵉ-iter e) (λ {v} → ⁺ᵉ-least e {v})
               (λ {d} → ⁺ᵉ-indˡ e {d}) (λ {d} → ⁺ᵉ-indʳ e {d})

entryʰ : GradeHints entryᵍ
entryʰ = record { 𝟏-least? = nothing ; ·-comm? = nothing ; plus? = λ e → just (plusᵉ e) }
