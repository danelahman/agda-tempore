------------------------------------------------------------------------
-- What the ends of an interval say about the durations it admits.    --
--                                                                    --
-- A duration `x` lies in an interval (`x ∈ⁱ i`) when the lower end   --
-- is below the cut `x ∣ ⁻` and the cut `x ∣ ⁺` below the upper end.  --
-- In any time domain the order of the ends is sound for containment  --
-- (`⊆ⁱ-sound`) and the sum of two intervals admits the sums of what   --
-- they admit (`⊕-sound`).                                            --
--                                                                    --
-- In a dense time domain with a positive duration both are exact:     --
-- every interval admits some duration (`inhabited`), containment is   --
-- the order of the ends (`⊆ⁱ-complete`), and whatever the sum admits  --
-- splits as a sum of what the summands admit (`⊕-complete`). So there --
-- an interval is determined by the durations it admits, and the sum   --
-- of intervals is their Minkowski sum.                                --
------------------------------------------------------------------------

open import Syntax.Durations

module Syntax.Durations.Intervals.Dense {D : Duration} (T : TimeDomain D) where

open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T

------------------------------------------------------------------------
-- Membership

infix 4 _∈ⁱ_

_∈ⁱ_ : Carrier → Interval → Set
x ∈ⁱ i = lo i ⊑ (x ∣ ⁻) × fin (x ∣ ⁺) ⊑ʰ hi i

-- the order of the ends is sound for containment

⊆ⁱ-sound : ∀ {i j} → i ⊆ⁱ j → ∀ {x} → x ∈ⁱ i → x ∈ⁱ j
⊆ⁱ-sound (p , q) (r , r') = ⊑-trans p r , ⊑ʰ-trans r' q

-- the sum admits the sums of what the summands admit

⊕-sound : ∀ {i j x y} → x ∈ⁱ i → y ∈ⁱ j → (x +ᴰ y) ∈ⁱ (i ⊕ j)
⊕-sound (p , q) (p' , q') = +ˡ-mono p p' , +ʰ-mono q q'

-- a point admits itself, and nothing else

∈-pointⁱ : ∀ w → w ∈ⁱ pointⁱ w
∈-pointⁱ w = ⊑-refl , ⊑-refl

pointⁱ-∈ : ∀ {x w} → x ∈ⁱ pointⁱ w → x ≡ w
pointⁱ-∈ (r , r') = ≤ᴰ-antisym (⊑⇒≤ r') (⊑⇒≤ r)

-- an interval shifted by `w` admits `w` moved on by what it admits

shift-∈ : ∀ {w i τ} → τ ∈ⁱ i → (w +ᴰ τ) ∈ⁱ (pointⁱ w ⊕ i)
shift-∈ {w} {i} r = ⊕-sound {pointⁱ w} {i} (∈-pointⁱ w) r

------------------------------------------------------------------------
-- Cuts and points

-- the cut just above a point is not below the cut just below it

⁺⋢⁻ : ∀ {x} → ¬ ((x ∣ ⁺) ⊑ (x ∣ ⁻))
⁺⋢⁻ (by-pt a)      = ⊥-elim-irr (<-irrefl a)
⁺⋢⁻ (by-side _ ())

-- below the cut just below a point is strictly below the point

⊑⁻⇒< : ∀ {p s q} → (p ∣ s) ⊑ (q ∣ ⁻) → s ≡ ⁺ → p <ᴰ q
⊑⁻⇒< {p} {s} {q} r refl with q ≤ᴰ? p
... | no ¬b = ¬b
⊑⁻⇒< (by-pt a)      refl | yes b = ⊥-elim-irr (a b)
⊑⁻⇒< (by-side _ ()) refl | yes b

-- the cut just below zero lies strictly below every cut just above a point

0⁻⊏⁺ : ∀ w → 0⁻ ⊏ (w ∣ ⁺)
0⁻⊏⁺ w with compare 0ᴰ w
... | tri< a = ⊏-by-pt a
... | tri≈ e = ⊏-by-side e
... | tri> a = ⊥-elim (a (0ᴰ-least w))

------------------------------------------------------------------------
-- Arithmetic of differences

private
  variable
    x z q r : Carrier

  -- `x` fits under `z ∸ q` exactly when `q` fits under `z ∸ x`
  swap-∸ : q ≤ᴰ z → x ≤ᴰ z → x ≤ᴰ z ∸ᴰ q → q ≤ᴰ z ∸ᴰ x
  swap-∸ {q} {z} {x} q≤z x≤z p =
    +-≤-∸ x≤z (≤ᴰ-trans (≤ᴰ-reflexive (+ᴰ-comm x q))
                        (≤ᴰ-trans (+ᴰ-monoʳ-≤ q p) (≤ᴰ-reflexive (+-∸ q≤z))))

  -- `z ∸ r` below `x` puts `z ∸ x` below `r`
  ∸-flip : z ∸ᴰ r ≤ᴰ x → z ∸ᴰ x ≤ᴰ r
  ∸-flip {z} {r} {x} p =
    ∸-≤-+ (≤ᴰ-trans (≤-+-∸ z r)
                    (≤ᴰ-trans (+ᴰ-monoʳ-≤ r p) (≤ᴰ-reflexive (+ᴰ-comm r x))))

  -- a sum strictly below `z` leaves a summand strictly below the
  -- difference
  <-∸ : x +ᴰ q <ᴰ z → x <ᴰ z ∸ᴰ q
  <-∸ {x} {q} {z} a b =
    a (≤ᴰ-trans (≤-+-∸ z q)
                (≤ᴰ-trans (+ᴰ-monoʳ-≤ q b) (≤ᴰ-reflexive (+ᴰ-comm q x))))

  -- and `z` strictly below a sum leaves the difference strictly below
  -- the other summand
  ∸-< : r ≤ᴰ z → z <ᴰ x +ᴰ r → z ∸ᴰ r <ᴰ x
  ∸-< {r} {z} {x} r≤z a b =
    a (≤ᴰ-trans (+ᴰ-monoˡ-≤ r b) (≤ᴰ-reflexive (∸-+ r≤z)))

  -- subtracting from `z` reverses a strict comparison below `z`
  ∸-anti-< : r ≤ᴰ z → q <ᴰ r → z ∸ᴰ r <ᴰ z ∸ᴰ q
  ∸-anti-< {r} {z} {q} r≤z a b =
    a (+ᴰ-cancelʳ-≤ (z ∸ᴰ r)
         (≤ᴰ-trans (≤ᴰ-reflexive (trans (+-∸ r≤z) (sym (+-∸ q≤z))))
                   (+ᴰ-monoʳ-≤ q b)))
    where
      q≤z : q ≤ᴰ z
      q≤z = ≤ᴰ-trans (<⇒≤ a) r≤z

  -- a difference is positive when the subtrahend is strictly smaller
  ∸-pos : q <ᴰ z → 0ᴰ <ᴰ z ∸ᴰ q
  ∸-pos {q} {z} a b =
    a (≤ᴰ-trans (≤-+-∸ z q)
                (≤ᴰ-trans (+ᴰ-monoʳ-≤ q b) (≤ᴰ-reflexive (+ᴰ-identityʳ q))))


------------------------------------------------------------------------
-- Splitting a sum: the bounds the summands put on one part of it

-- the other side

flip : Side → Side
flip ⁻ = ⁺
flip ⁺ = ⁻

private
  -- a cut below the one just below `z`, and one just above `z` below a cut
  lo-split : ∀ {p s z} → (p ∣ s) ⊑ (z ∣ ⁻) → p <ᴰ z ⊎ (p ≡ z × s ≡ ⁻)
  lo-split {p} {s} {z} r with compare p z
  ... | tri< a = inj₁ a
  ... | tri> a = ⊥-elim (a (⊑⇒≤ r))
  lo-split (by-pt a)      | tri≈ e = ⊥-elim-irr (<⇒≢ a e)
  lo-split (by-side _ ⁻≤) | tri≈ e = inj₂ (e , refl)

  hi-split : ∀ {p s z} → (z ∣ ⁺) ⊑ (p ∣ s) → z <ᴰ p ⊎ (z ≡ p × s ≡ ⁺)
  hi-split {p} {s} {z} r with compare z p
  ... | tri< a = inj₁ a
  ... | tri> a = ⊥-elim (a (⊑⇒≤ r))
  hi-split (by-pt a)       | tri≈ e = ⊥-elim-irr (<⇒≢ a e)
  hi-split (by-side _ ⁺≤⁺) | tri≈ e = inj₂ (e , refl)

-- The bound on the first summand `x` of a split of `z` that an upper
-- end `h` on the second puts: `z ∸ x` below `h` asks `x` to be above
-- the returned cut.

data LoBound (z : Carrier) : Hi → Cut → Set where
  none : LoBound z ∞ 0⁻
  far  : ∀ {r u} → z <ᴰ r → LoBound z (fin (r ∣ u)) 0⁻
  near : ∀ {r u} → r ≤ᴰ z → LoBound z (fin (r ∣ u)) ((z ∸ᴰ r) ∣ flip u)

lo-bound : ∀ z h → Σ Cut (LoBound z h)
lo-bound z ∞ = 0⁻ , none
lo-bound z (fin (r ∣ u)) with r ≤ᴰ? z
... | yes b = _ , near b
... | no ¬b = _ , far ¬b

private
  -- the lower end of the first summand lies below the bound the lower
  -- end of the second puts on it
  C1 : ∀ {p s q t z} → ((p +ᴰ q) ∣ (s ∨ˢ t)) ⊑ (z ∣ ⁻)
     → (p ∣ s) ⊏ ((z ∸ᴰ q) ∣ flip t)
  C1 {p} {s} {q} {t} r with lo-split r
  ... | inj₁ a = ⊏-by-pt (<-∸ a)
  ... | inj₂ (e , sv) rewrite ∨ˢ-⁻ˡ {s} {t} sv | ∨ˢ-⁻ʳ {s} {t} sv =
    ⊏-by-side (sym (∸-unique (trans (+ᴰ-comm q p) e)))

  -- the bound from the upper end of the second summand lies below the
  -- upper end of the first
  C2 : ∀ {a b d z L} → a ◁ b → LoBound z d L → fin (z ∣ ⁺) ⊑ʰ b +ʰ d → L ◁ b
  C2 {a} {b} a◁b none _ = ⊑-◁-trans (0⁻-least a) a◁b
  C2 {a} {b} a◁b (far _) _ = ⊑-◁-trans (0⁻-least a) a◁b
  C2 {b = ∞} _ (near _) _ = tt
  C2 {b = fin (p' ∣ s')} {fin (r ∣ u)} _ (near r≤z) H2 with hi-split H2
  ... | inj₁ a = ⊏-by-pt (∸-< r≤z a)
  ... | inj₂ (e , sv) rewrite ∧ˢ-⁺ˡ {s'} {u} sv | ∧ˢ-⁺ʳ {s'} {u} sv =
    ⊏-by-side (∸-unique (trans (+ᴰ-comm r p') (sym e)))

  -- the two bounds on the first summand are consistent
  C3 : ∀ {p s q t d z L} → ((p +ᴰ q) ∣ (s ∨ˢ t)) ⊑ (z ∣ ⁻) → (q ∣ t) ◁ d
     → LoBound z d L → L ⊏ ((z ∸ᴰ q) ∣ flip t)
  C3 {p} {s} {q} {t} {z = z} H1 _ none = zero-case {p} {s} {q} {t} {z} H1
    where
      zero-case : ∀ {p s q t z} → ((p +ᴰ q) ∣ (s ∨ˢ t)) ⊑ (z ∣ ⁻)
                → 0⁻ ⊏ ((z ∸ᴰ q) ∣ flip t)
      zero-case {p} {s} {q} {t} {z} r with lo-split r
      ... | inj₁ a = ⊏-by-pt (∸-pos (≤-<-trans (≤ᴰ-+ˡ q p) a))
      ... | inj₂ (_ , sv) rewrite ∨ˢ-⁻ʳ {s} {t} sv = 0⁻⊏⁺ (z ∸ᴰ q)
  C3 {p} {s} {q} {t} {z = z} H1 _ (far _) with lo-split H1
  ... | inj₁ a = ⊏-by-pt (∸-pos (≤-<-trans (≤ᴰ-+ˡ q p) a))
  ... | inj₂ (_ , sv) rewrite ∨ˢ-⁻ʳ {s} {t} sv = 0⁻⊏⁺ (z ∸ᴰ q)
  C3 {q = q} {t} {z = z} _ c◁d (near {r} {u} r≤z) with ⊏-cases c◁d
  ... | inj₁ a = ⊏-by-pt (∸-anti-< r≤z a)
  ... | inj₂ (e , refl , refl) = ⊏-by-side (cong (z ∸ᴰ_) (sym e))

  -- the bounds, met by `x`, put `z ∸ x` within the second summand
  F2 : ∀ {q t z x} → q ≤ᴰ z → x ≤ᴰ z → (x ∣ ⁺) ⊑ ((z ∸ᴰ q) ∣ flip t)
     → (q ∣ t) ⊑ ((z ∸ᴰ x) ∣ ⁻)
  F2 {t = ⁻} q≤z x≤z r = ≤⇒⁻⊑⁻ (swap-∸ q≤z x≤z (⊑⇒≤ r))
  F2 {q} {⁺} {z} {x} q≤z x≤z r = by-pt (λ b → ⊑⁻⇒< r refl (∸-flip b))

  F3 : ∀ {d z x L} → x ≤ᴰ z → LoBound z d L → L ⊑ (x ∣ ⁻)
     → fin ((z ∸ᴰ x) ∣ ⁺) ⊑ʰ d
  F3 _ none _ = tt
  F3 {z = z} {x} _ (far z<r) _ = by-pt (≤-<-trans (∸-≤-self z x) z<r)
  F3 {fin (r ∣ ⁺)} _ (near r≤z) r' = ≤⇒⁺⊑⁺ (∸-flip (⊑⇒≤ r'))
  F3 {fin (r ∣ ⁻)} {z} {x} x≤z (near r≤z) r' =
    by-pt (λ b → ⊑⁻⇒< r' refl (swap-∸ x≤z r≤z b))

-- an upper end not below a cut is above it

fin⊑ʰ : ∀ {c h} → ¬ (h ⊑ʰ fin c) → fin c ⊑ʰ h
fin⊑ʰ {c} {fin c'} n = ⊏⇒⊑ n
fin⊑ʰ {c} {∞}      _ = tt

-- the larger of two lower ends below an upper end is below it

⊔-◁ : ∀ {c c' h} → c ◁ h → c' ◁ h → c ⊔ᶜ c' ◁ h
⊔-◁ {c} {c'} {h} u v with ⊔ᶜ-sel c c'
... | inj₁ e = subst (_◁ h) (sym e) u
... | inj₂ e = subst (_◁ h) (sym e) v

------------------------------------------------------------------------
-- In a dense time domain with a positive duration

module Exact (dense : Dense T) (κ : Carrier) (κ-pos : 0ᴰ <ᴰ κ) where

  -- between a lower end and an upper end strictly above it lies a point

  between : ∀ {c h} → c ◁ h → Σ Carrier (λ x → c ⊑ (x ∣ ⁻) × fin (x ∣ ⁺) ⊑ʰ h)
  between {p ∣ s} {fin (p' ∣ s')} r with ⊏-cases r
  ... | inj₁ a with dense a
  ...   | x , b , b' = x , by-pt b , by-pt b'
  between {p ∣ s} {fin (p' ∣ s')} r | inj₂ (e , refl , refl) =
    p , ⊑-refl , by-side e ⁺≤⁺
  between {p ∣ s} {∞} _ = p +ᴰ κ , by-pt (<-+ κ-pos) , tt

  inhabited : ∀ i → Σ Carrier (_∈ⁱ i)
  inhabited i = between {lo i} {hi i} (lo◁hi i)

  -- containment is the order of the ends

  ⊆ⁱ-complete : ∀ {i j} → (∀ {x} → x ∈ⁱ i → x ∈ⁱ j) → i ⊆ⁱ j
  ⊆ⁱ-complete {i} {j} f = lo-part , hi-part
    where
      lo-part : lo j ⊑ lo i
      lo-part with lo j ⊑? lo i
      ... | yes p = p
      ... | no ¬p with hi i ⊑ʰ? fin (lo j)
      ...   | yes q with between {lo i} {hi i} (lo◁hi i)
      ...     | x , r , r' = ⊥-elim (⁺⋢⁻ (⊑-trans (⊑ʰ-trans' r' q) (proj₁ (f (r , r')))))
        where
          ⊑ʰ-trans' : ∀ {c h} → fin c ⊑ʰ h → h ⊑ʰ fin (lo j) → c ⊑ lo j
          ⊑ʰ-trans' {h = fin _} a b = ⊑-trans a b
          ⊑ʰ-trans' {h = ∞}     _ ()
      lo-part | no ¬p | no ¬q with between {lo i} {fin (lo j)} ¬p
      ...     | x , r , r' =
        ⊥-elim (⁺⋢⁻ (⊑-trans r' (proj₁ (f (r , ⊑ʰ-trans {fin (x ∣ ⁺)} {fin (lo j)} {hi i}
                                                 r' (fin⊑ʰ ¬q))))))

      hi-part : hi i ⊑ʰ hi j
      hi-part with hi i ⊑ʰ? hi j
      ... | yes q = q
      hi-part | no ¬q with hi j
      ... | ∞ = ⊑ʰ-∞ (hi i)
      ... | fin c' with ⊔ᶜ-sel (lo i) c' | between {lo i ⊔ᶜ c'} {hi i} (⊔◁ (⊔ᶜ-sel (lo i) c'))
        where
          c'◁ : c' ◁ hi i
          c'◁ with hi i
          ... | fin c'' = λ r → ¬q r
          ... | ∞       = tt
          ⊔◁ : lo i ⊔ᶜ c' ≡ lo i ⊎ lo i ⊔ᶜ c' ≡ c' → lo i ⊔ᶜ c' ◁ hi i
          ⊔◁ (inj₁ e) = subst (_◁ hi i) (sym e) (lo◁hi i)
          ⊔◁ (inj₂ e) = subst (_◁ hi i) (sym e) c'◁
      ... | _ | x , r , r' =
        ⊥-elim (⁺⋢⁻ (⊑-trans (proj₂ (f (⊑-trans (⊔ᶜ-ubˡ (lo i) c') r , r')))
                             (⊑-trans (⊔ᶜ-ubʳ (lo i) c') r)))

  -- whatever a sum admits splits as a sum of what the summands admit

  private
    Split : Cut → Hi → Cut → Hi → Carrier → Set
    Split a b c d z =
      Σ Carrier (λ x → Σ Carrier (λ y →
        (a ⊑ (x ∣ ⁻) × fin (x ∣ ⁺) ⊑ʰ b) × (c ⊑ (y ∣ ⁻) × fin (y ∣ ⁺) ⊑ʰ d)
        × x +ᴰ y ≡ z))

    -- a point meeting both bounds on the first summand gives the split
    finish : ∀ {p s q t b d z L} → q ≤ᴰ z → LoBound z d L → (x : Carrier)
           → (p ∣ s) ⊔ᶜ L ⊑ (x ∣ ⁻) → (x ∣ ⁺) ⊑ ((z ∸ᴰ q) ∣ flip t)
           → fin (x ∣ ⁺) ⊑ʰ b → Split (p ∣ s) b (q ∣ t) d z
    finish {p} {s} {q} {t} {b} {d} {z} {L} q≤z lb x r xU xb =
      x , z ∸ᴰ x , (⊑-trans (⊔ᶜ-ubˡ (p ∣ s) L) r , xb)
        , (F2 q≤z x≤z xU , F3 x≤z lb (⊑-trans (⊔ᶜ-ubʳ (p ∣ s) L) r)) , +-∸ x≤z
      where
        x≤z : x ≤ᴰ z
        x≤z = ≤ᴰ-trans (⊑⇒≤ xU) (∸-≤-self z q)

    split : ∀ {p s q t} b d z → (p ∣ s) ◁ b → (q ∣ t) ◁ d
          → ((p +ᴰ q) ∣ (s ∨ˢ t)) ⊑ (z ∣ ⁻) → fin (z ∣ ⁺) ⊑ʰ b +ʰ d
          → Split (p ∣ s) b (q ∣ t) d z
    split {p} {s} {q} {t} b d z a◁b c◁d H1 H2 with lo-bound z d
    ... | L , lb with b ⊑ʰ? fin ((z ∸ᴰ q) ∣ flip t)
    ...   | yes bU with between {(p ∣ s) ⊔ᶜ L} {b}
                          (⊔-◁ {p ∣ s} {L} {b} a◁b (C2 {p ∣ s} {b} a◁b lb H2))
    ...     | x , r , xb =
      finish q≤z lb x r (⊑ʰ-trans {fin (x ∣ ⁺)} {b} {fin ((z ∸ᴰ q) ∣ flip t)} xb bU) xb
      where
        q≤z : q ≤ᴰ z
        q≤z = ≤ᴰ-trans (≤ᴰ-+ˡ q p) (⊑⇒≤ H1)
    split {p} {s} {q} {t} b d z a◁b c◁d H1 H2 | L , lb | no ¬bU
      with between {(p ∣ s) ⊔ᶜ L} {fin ((z ∸ᴰ q) ∣ flip t)}
             (⊔-◁ {p ∣ s} {L} {fin ((z ∸ᴰ q) ∣ flip t)} (C1 H1) (C3 H1 c◁d lb))
    ... | x , r , xU =
      finish q≤z lb x r xU (⊑ʰ-trans {fin (x ∣ ⁺)} {fin ((z ∸ᴰ q) ∣ flip t)} {b} xU (fin⊑ʰ ¬bU))
      where
        q≤z : q ≤ᴰ z
        q≤z = ≤ᴰ-trans (≤ᴰ-+ˡ q p) (⊑⇒≤ H1)

  ⊕-complete : ∀ {i j z} → z ∈ⁱ (i ⊕ j)
             → Σ Carrier (λ x → Σ Carrier (λ y → x ∈ⁱ i × y ∈ⁱ j × x +ᴰ y ≡ z))
  ⊕-complete {i} {j} {z} (H1 , H2) =
    split (hi i) (hi j) z (lo◁hi i) (lo◁hi j) H1 H2

  -- and an interval shifted by `w` admits only `w` moved on by what it
  -- admits

  ∈-shift : ∀ {w i w'} → w' ∈ⁱ (pointⁱ w ⊕ i) → Σ Carrier (λ τ → τ ∈ⁱ i × w +ᴰ τ ≡ w')
  ∈-shift {w} {i} r with ⊕-complete {pointⁱ w} {i} r
  ... | x , τ , x∈ , τ∈ , e = τ , τ∈ , trans (cong (_+ᴰ τ) (sym (pointⁱ-∈ x∈))) e
