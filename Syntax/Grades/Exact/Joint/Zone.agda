------------------------------------------------------------------------
-- Zones of one clock: the durations between a lower and an upper     --
-- end.                                                               --
--                                                                    --
-- A zone is a lower end and an upper end, possibly admitting nothing.--
-- The joint walk tracks the time the piece in progress has run as a  --
-- zone, and needs, besides intersection,                             --
--                                                                    --
--   Z ⊕ W   the sums of what `Z` and `W` admit (`Intervals.Dense`),  --
--   C ⊖ I   the positive `t` with `e + t` in `C` for an `e` in `I`:  --
--           its lower end is `0⁺` or the lower end of `C` less the   --
--           upper end of `I`, its upper end the upper end of `C`     --
--           less the lower end of `I`, an end open when either end   --
--           it comes from is.                                        --
--                                                                    --
-- Each is sound in any time domain and exact in a dense one, where   --
-- every inhabited zone admits a duration.                            --
------------------------------------------------------------------------

open import Syntax.Durations using (Duration; TimeDomain; Dense)

module Syntax.Grades.Exact.Joint.Zone {D : Duration} (T : TimeDomain D) where

open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (fromWitness)

open import Util.Equality

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
open import Syntax.Durations.Intervals.Dense T using (_∈ⁱ_; flip; ⊑⁻⇒<; ⊔-◁; fin⊑ʰ; module Exact)

------------------------------------------------------------------------
-- Zones

record Zone : Set where
  constructor ⟨_,_⟩ᶻ
  field
    loᶻ : Cut
    hiᶻ : Hi

open Zone public

infix 4 _∈ᶻ_

_∈ᶻ_ : Carrier → Zone → Set
x ∈ᶻ Z = loᶻ Z ⊑ (x ∣ ⁻) × fin (x ∣ ⁺) ⊑ʰ hiᶻ Z

_∈ᶻ?_ : ∀ x Z → Dec (x ∈ᶻ Z)
x ∈ᶻ? Z with loᶻ Z ⊑? (x ∣ ⁻) | fin (x ∣ ⁺) ⊑ʰ? hiᶻ Z
... | yes r | yes r′ = yes (r , r′)
... | no ¬r | _      = no λ m → ¬r (proj₁ m)
... | _     | no ¬r′ = no λ m → ¬r′ (proj₂ m)

-- inhabited: the lower end strictly below the upper end

Inh : Zone → Set
Inh Z = loᶻ Z ◁ hiᶻ Z

Inh? : ∀ Z → Dec (Inh Z)
Inh? Z = loᶻ Z ◁? hiᶻ Z

∈⇒Inh : ∀ {x Z} → x ∈ᶻ Z → Inh Z
∈⇒Inh {x} {⟨ c , fin c′ ⟩ᶻ} (r , r′) = ⊑-⊏-trans r (⊑-⊏-trans′ r′)
  where
    ⊑-⊏-trans′ : (x ∣ ⁺) ⊑ c′ → (x ∣ ⁻) ⊏ c′
    ⊑-⊏-trans′ q = ⊏-⊑-trans (⊏-by-side refl) q
∈⇒Inh {x} {⟨ c , ∞ ⟩ᶻ} _ = tt

-- as an interval

toⁱ : ∀ Z → Inh Z → Interval
toⁱ Z i = ⟪ loᶻ Z , hiᶻ Z ⟫ {fromWitness i}

------------------------------------------------------------------------
-- Reading the ends

data Lo (a : Carrier) : Side → Carrier → Set where
  lo⁻ : ∀ {x} → a ≤ᴰ x → Lo a ⁻ x
  lo⁺ : ∀ {x} → a <ᴰ x → Lo a ⁺ x

lo-read : ∀ {a s x} → (a ∣ s) ⊑ (x ∣ ⁻) → Lo a s x
lo-read {s = ⁻} r = lo⁻ (⊑⇒≤ r)
lo-read {s = ⁺} r = lo⁺ (⊑⁻⇒< r refl)

lo-write : ∀ {a s x} → Lo a s x → (a ∣ s) ⊑ (x ∣ ⁻)
lo-write (lo⁻ b) = ≤⇒⁻⊑⁻ b
lo-write (lo⁺ b) = by-pt b

data Up (x : Carrier) : Carrier → Side → Set where
  up⁺ : ∀ {b} → x ≤ᴰ b → Up x b ⁺
  up⁻ : ∀ {b} → x <ᴰ b → Up x b ⁻

up-read : ∀ {x b s} → (x ∣ ⁺) ⊑ (b ∣ s) → Up x b s
up-read {s = ⁺} r = up⁺ (⊑⇒≤ r)
up-read {s = ⁻} r = up⁻ (⊑⁻⇒< r refl)

up-write : ∀ {x b s} → Up x b s → (x ∣ ⁺) ⊑ (b ∣ s)
up-write (up⁺ b) = ≤⇒⁺⊑⁺ b
up-write (up⁻ b) = by-pt b

------------------------------------------------------------------------
-- Arithmetic

private
  ≮⇒≥ : ∀ {p d} → ¬ (p <ᴰ d) → d ≤ᴰ p
  ≮⇒≥ {p} {d} ¬p with d ≤ᴰ? p
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

  -- below a sum, past one summand

  ∸-≤′ : ∀ {p q t} → p ≤ᴰ q +ᴰ t → p ∸ᴰ q ≤ᴰ t
  ∸-≤′ = ∸-≤-+

  ∸-<′ : ∀ {p q t} → 0ᴰ <ᴰ t → p <ᴰ q +ᴰ t → p ∸ᴰ q <ᴰ t
  ∸-<′ {p} {q} {t} pt r = case (q ≤ᴰ? p)
    where
      case : Dec (q ≤ᴰ p) → p ∸ᴰ q <ᴰ t
      case (yes q≤p) = λ b → r (≤ᴰ-trans (+ᴰ-monoʳ-≤ q b) (≤ᴰ-reflexive (+-∸ q≤p)))
      case (no ¬q≤p) = subst (_<ᴰ t) (sym (∸-≤ (<⇒≤ ¬q≤p))) pt

  -- a sum past a difference

  le-∸ : ∀ {p q t} → p ∸ᴰ q ≤ᴰ t → p ≤ᴰ t +ᴰ q
  le-∸ {p} {q} {t} r =
    ≤ᴰ-trans (≤-+-∸ p q) (≤ᴰ-trans (+ᴰ-monoʳ-≤ q r) (≤ᴰ-reflexive (+ᴰ-comm q t)))

  lt-∸ : ∀ {p q t} → p ∸ᴰ q <ᴰ t → p <ᴰ t +ᴰ q
  lt-∸ {p} {q} {t} r b =
    r (+-≤-∸ (≤ᴰ-trans (≤ᴰ-+ˡ q t) b) (≤ᴰ-trans (≤ᴰ-reflexive (+ᴰ-comm q t)) b))

  -- under a difference

  le-under : ∀ {p r t} → p +ᴰ t ≤ᴰ r → t ≤ᴰ r ∸ᴰ p
  le-under {p} {r} {t} b = +-≤-∸ (≤ᴰ-trans (≤ᴰ-+ p t) b) b

  lt-under : ∀ {p r t} → p +ᴰ t <ᴰ r → t <ᴰ r ∸ᴰ p
  lt-under {p} {r} {t} b c =
    b (≤ᴰ-trans (≤-+-∸ r p) (+ᴰ-monoʳ-≤ p c))

  over-le : ∀ {p r t} → 0ᴰ <ᴰ t → t ≤ᴰ r ∸ᴰ p → t +ᴰ p ≤ᴰ r
  over-le {p} {r} {t} pt b = case (p ≤ᴰ? r)
    where
      case : Dec (p ≤ᴰ r) → t +ᴰ p ≤ᴰ r
      case (yes p≤r) = ≤ᴰ-trans (+ᴰ-monoˡ-≤ p b) (≤ᴰ-reflexive (trans (+ᴰ-comm _ p) (+-∸ p≤r)))
      case (no ¬p≤r) = ⊥-elim (pt (subst (t ≤ᴰ_) (∸-≤ (<⇒≤ ¬p≤r)) b))

  over-lt : ∀ {p r t} → t <ᴰ r ∸ᴰ p → t +ᴰ p <ᴰ r
  over-lt {p} {r} {t} b c = b (∸-≤-+ (≤ᴰ-trans c (≤ᴰ-reflexive (+ᴰ-comm t p))))

------------------------------------------------------------------------
-- Differences of ends

infixl 6 _−ₗ_ _−ₕ_

-- the lower end of `C ⊖ I`, before positivity: the lower end of `C`
-- less the upper end of `I`

_−ₗ_ : Cut → Hi → Cut
(p ∣ s) −ₗ fin (q ∣ u) = (p ∸ᴰ q) ∣ (s ∨ˢ flip u)
(p ∣ s) −ₗ ∞           = 0⁻

-- the upper end of `C ⊖ I`: the upper end of `C` less the lower end
-- of `I`

_−ₕ_ : Hi → Cut → Hi
fin (r ∣ s′) −ₕ (p ∣ s) = fin ((r ∸ᴰ p) ∣ (s′ ∧ˢ flip s))
∞            −ₕ _       = ∞

private
  -- a bound on `e + t` and one on `e` bound `t`
  L1 : ∀ {p s e t h} → Lo p s (e +ᴰ t) → fin (e ∣ ⁺) ⊑ʰ h → 0ᴰ <ᴰ t → (p ∣ s) −ₗ h ⊑ (t ∣ ⁻)
  L1 {h = ∞} _ _ _ = 0⁻-least _
  L1 {p} {s} {e} {t} {fin (q ∣ u)} lo hi pt = lo-write (go lo (up-read hi))
    where
      go : Lo p s (e +ᴰ t) → Up e q u → Lo (p ∸ᴰ q) (s ∨ˢ flip u) t
      go (lo⁻ a) (up⁺ b) = lo⁻ (∸-≤′ (≤ᴰ-trans a (+ᴰ-monoˡ-≤ t b)))
      go (lo⁺ a) (up⁺ b) = lo⁺ (∸-<′ pt (<-≤-trans a (+ᴰ-monoˡ-≤ t b)))
      go (lo⁻ a) (up⁻ b) = lo⁺ (∸-<′ pt (≤-<-trans a (+ᴰ-monoˡ-< t b)))
      go (lo⁺ a) (up⁻ b) = lo⁺ (∸-<′ pt (<-trans a (+ᴰ-monoˡ-< t b)))

  -- and the bound on `t` puts the lower end of `C` below `t` plus the
  -- upper end of `I`
  L2 : ∀ {p s q u t} → (p ∣ s) −ₗ fin (q ∣ u) ⊑ (t ∣ ⁻) → (p ∣ s) ◁ fin ((t +ᴰ q) ∣ u)
  L2 {p} {s} {q} {u} {t} r = go s u (lo-read r)
    where
      go : ∀ s u → Lo (p ∸ᴰ q) (s ∨ˢ flip u) t → (p ∣ s) ⊏ ((t +ᴰ q) ∣ u)
      go ⁻ ⁺ (lo⁻ b) with compare p (t +ᴰ q)
      ... | tri< a = ⊏-by-pt a
      ... | tri≈ e = ⊏-by-side e
      ... | tri> a = ⊥-elim (a (le-∸ b))
      go ⁺ _ (lo⁺ b) = ⊏-by-pt (lt-∸ b)
      go ⁻ ⁻ (lo⁺ b) = ⊏-by-pt (lt-∸ b)

  -- a bound on `e` and one on `e + t` bound `t`
  H1 : ∀ {p s e t h} → Lo p s e → fin ((e +ᴰ t) ∣ ⁺) ⊑ʰ h → fin (t ∣ ⁺) ⊑ʰ h −ₕ (p ∣ s)
  H1 {h = ∞} _ _ = tt
  H1 {p} {s} {e} {t} {fin (r ∣ s′)} lo hi = up-write (go lo (up-read hi))
    where
      go : Lo p s e → Up (e +ᴰ t) r s′ → Up t (r ∸ᴰ p) (s′ ∧ˢ flip s)
      go (lo⁻ a) (up⁺ b) = up⁺ (le-under (≤ᴰ-trans (+ᴰ-monoˡ-≤ t a) b))
      go (lo⁺ a) (up⁺ b) = up⁻ (lt-under (<-≤-trans (+ᴰ-monoˡ-< t a) b))
      go (lo⁻ a) (up⁻ b) = up⁻ (lt-under (≤-<-trans (+ᴰ-monoˡ-≤ t a) b))
      go (lo⁺ a) (up⁻ b) = up⁻ (lt-under (<-trans (+ᴰ-monoˡ-< t a) b))

  -- and the bound on `t` puts `t` plus the lower end of `I` below the
  -- upper end of `C`
  H2 : ∀ {p s t h} → 0ᴰ <ᴰ t → fin (t ∣ ⁺) ⊑ʰ h −ₕ (p ∣ s) → ((t +ᴰ p) ∣ s) ◁ h
  H2 {h = ∞} _ _ = tt
  H2 {p} {s} {t} {fin (r ∣ s′)} pt hi = go s s′ (up-read hi)
    where
      go : ∀ s s′ → Up t (r ∸ᴰ p) (s′ ∧ˢ flip s) → ((t +ᴰ p) ∣ s) ⊏ (r ∣ s′)
      go ⁻ ⁺ (up⁺ b) with compare (t +ᴰ p) r
      ... | tri< a = ⊏-by-pt a
      ... | tri≈ e = ⊏-by-side e
      ... | tri> a = ⊥-elim (a (over-le pt b))
      go ⁺ ⁺ (up⁻ b) = ⊏-by-pt (over-lt b)
      go ⁺ ⁻ (up⁻ b) = ⊏-by-pt (over-lt b)
      go ⁻ ⁻ (up⁻ b) = ⊏-by-pt (over-lt b)

  -- the lower end of `C` below `t` plus the upper end of `I`
  lo-◁ : ∀ {p s t} h → 0⁺ ⊔ᶜ ((p ∣ s) −ₗ h) ⊑ (t ∣ ⁻) → (p ∣ s) ◁ fin (t ∣ ⁺) +ʰ h
  lo-◁ ∞           _ = tt
  lo-◁ {p} {s} (fin (q ∣ u)) r = L2 (⊑-trans (⊔ᶜ-ubʳ 0⁺ ((p ∣ s) −ₗ fin (q ∣ u))) r)

------------------------------------------------------------------------
-- The operations

infixl 6 _⊕ᶻ_ _⊖ᶻ_
infixl 7 _∩ᶻ_

_⊕ᶻ_ : Zone → Zone → Zone
Z ⊕ᶻ W = ⟨ loᶻ Z +ˡ loᶻ W , hiᶻ Z +ʰ hiᶻ W ⟩ᶻ

_⊖ᶻ_ : Zone → Zone → Zone
C ⊖ᶻ I = ⟨ 0⁺ ⊔ᶜ (loᶻ C −ₗ hiᶻ I) , hiᶻ C −ₕ loᶻ I ⟩ᶻ

-- the smaller upper end

infixl 7 _⊓ʰ_

_⊓ʰ_ : Hi → Hi → Hi
fin c ⊓ʰ fin c′ = fin (c ⊓ᶜ c′)
fin c ⊓ʰ ∞      = fin c
∞     ⊓ʰ h      = h

⊓ʰ-glb : ∀ {h h′ k} → k ⊑ʰ h → k ⊑ʰ h′ → k ⊑ʰ h ⊓ʰ h′
⊓ʰ-glb {fin _} {fin _} {fin _} p q = ⊓ᶜ-glb p q
⊓ʰ-glb {fin _} {∞}     {fin _} p _ = p
⊓ʰ-glb {∞}     {_}     {_}     _ q = q
⊓ʰ-glb {fin _} {_}     {∞}     () _

⊓ʰ-lbˡ : ∀ h h′ → h ⊓ʰ h′ ⊑ʰ h
⊓ʰ-lbˡ (fin c) (fin c′) = ⊓ᶜ-lbˡ c c′
⊓ʰ-lbˡ (fin c) ∞        = ⊑-refl
⊓ʰ-lbˡ ∞       h′       = ⊑ʰ-∞ h′

⊓ʰ-lbʳ : ∀ h h′ → h ⊓ʰ h′ ⊑ʰ h′
⊓ʰ-lbʳ (fin c) (fin c′) = ⊓ᶜ-lbʳ c c′
⊓ʰ-lbʳ (fin c) ∞        = tt
⊓ʰ-lbʳ ∞       h′       = ⊑ʰ-refl

◁-⊓ʰ : ∀ {c h h′} → c ◁ h → c ◁ h′ → c ◁ h ⊓ʰ h′
◁-⊓ʰ {c} {fin a} {fin b} p q with ⊓ᶜ-sel a b
... | inj₁ e = subst (λ z → c ⊏ z) (sym e) p
... | inj₂ e = subst (λ z → c ⊏ z) (sym e) q
◁-⊓ʰ {c} {fin a} {∞}     p _ = p
◁-⊓ʰ {c} {∞}     {_}     _ q = q

_∩ᶻ_ : Zone → Zone → Zone
Z ∩ᶻ W = ⟨ loᶻ Z ⊔ᶜ loᶻ W , hiᶻ Z ⊓ʰ hiᶻ W ⟩ᶻ

-- an upper end raised to `∞` once past a lower end

raise : Cut → Hi → Hi
raise c h with c ◁? h
... | yes _ = ∞
... | no _  = h

------------------------------------------------------------------------
-- Soundness

⊕ᶻ-sound : ∀ {x y Z W} → x ∈ᶻ Z → y ∈ᶻ W → (x +ᴰ y) ∈ᶻ (Z ⊕ᶻ W)
⊕ᶻ-sound (p , q) (p′ , q′) = +ˡ-mono p p′ , +ʰ-mono q q′

∩ᶻ-sound : ∀ {x Z W} → x ∈ᶻ Z → x ∈ᶻ W → x ∈ᶻ (Z ∩ᶻ W)
∩ᶻ-sound (p , q) (p′ , q′) = ⊔ᶜ-lub p p′ , ⊓ʰ-glb q q′

∩ᶻ-elim : ∀ {x Z W} → x ∈ᶻ (Z ∩ᶻ W) → x ∈ᶻ Z × x ∈ᶻ W
∩ᶻ-elim {x} {Z} {W} (p , q) =
  (⊑-trans (⊔ᶜ-ubˡ (loᶻ Z) (loᶻ W)) p , ⊑ʰ-trans {fin (x ∣ ⁺)} q (⊓ʰ-lbˡ (hiᶻ Z) (hiᶻ W))) ,
  (⊑-trans (⊔ᶜ-ubʳ (loᶻ Z) (loᶻ W)) p , ⊑ʰ-trans {fin (x ∣ ⁺)} q (⊓ʰ-lbʳ (hiᶻ Z) (hiᶻ W)))

⊖ᶻ-sound : ∀ {e t C I} → e ∈ᶻ I → (e +ᴰ t) ∈ᶻ C → 0ᴰ <ᴰ t → t ∈ᶻ (C ⊖ᶻ I)
⊖ᶻ-sound {C = ⟨ p ∣ s , hC ⟩ᶻ} {⟨ pI ∣ sI , hI ⟩ᶻ} (r , r′) (c , c′) pt =
  ⊔ᶜ-lub (lo-write (lo⁺ pt)) (L1 (lo-read c) r′ pt) , H1 (lo-read r) c′

⊖ᶻ-pos : ∀ {t C I} → t ∈ᶻ (C ⊖ᶻ I) → 0ᴰ <ᴰ t
⊖ᶻ-pos {t} {C} {I} (r , _) with lo-read (⊑-trans (⊔ᶜ-ubˡ 0⁺ (loᶻ C −ₗ hiᶻ I)) r)
... | lo⁺ a = a

------------------------------------------------------------------------
-- Exactness, in a dense time domain

module Exactᶻ (dense : Dense T) (κ : Carrier) (κ-pos : 0ᴰ <ᴰ κ) where

  open Exact dense κ κ-pos using (between; ⊕-complete)

  inhabited : ∀ {Z} → Inh Z → Σ Carrier (_∈ᶻ Z)
  inhabited {Z} i = between {loᶻ Z} {hiᶻ Z} i

  ⊕ᶻ-complete : ∀ {z Z W} → Inh Z → Inh W → z ∈ᶻ (Z ⊕ᶻ W)
              → Σ Carrier λ x → Σ Carrier λ y → x ∈ᶻ Z × y ∈ᶻ W × x +ᴰ y ≡ z
  ⊕ᶻ-complete {z} {Z} {W} iZ iW m = ⊕-complete {toⁱ Z iZ} {toⁱ W iW} {z} m

  ⊖ᶻ-complete : ∀ {t C I} → Inh C → Inh I → t ∈ᶻ (C ⊖ᶻ I)
              → Σ Carrier λ e → e ∈ᶻ I × (e +ᴰ t) ∈ᶻ C
  ⊖ᶻ-complete {t} {C@(⟨ p ∣ s , hC ⟩ᶻ)} {I@(⟨ pI ∣ sI , hI ⟩ᶻ)} iC iI m@(r , r′)
    with inhabited {W} (⊔-◁ {lW} {p ∣ s} {hW} (◁-⊓ʰ {lW} {hT} {hC} lW◁hT lW◁hC)
                                             (◁-⊓ʰ {p ∣ s} {hT} {hC} c◁hT iC))
    where
      t-pos = ⊖ᶻ-pos {t} {C} {I} m
      lW : Cut
      lW = (t ∣ ⁻) +ˡ (pI ∣ sI)
      hT : Hi
      hT = fin (t ∣ ⁺) +ʰ hI
      hW : Hi
      hW = hT ⊓ʰ hC
      W : Zone
      W = ⟨ lW ⊔ᶜ (p ∣ s) , hW ⟩ᶻ
      lW◁hT : lW ◁ hT
      lW◁hT = +-◁ {t ∣ ⁻} {pI ∣ sI} {fin (t ∣ ⁺)} {hI} (⊏-by-side refl) iI
      lW◁hC : lW ◁ hC
      lW◁hC = H2 {pI} {sI} {t} {hC} t-pos r′
      c◁hT : (p ∣ s) ◁ hT
      c◁hT = lo-◁ hI r
  ... | z , zl , zh
    with ⊕-complete {pointⁱ t} {toⁱ I iI} {z}
           (⊑-trans (⊔ᶜ-ubˡ ((t ∣ ⁻) +ˡ (pI ∣ sI)) (p ∣ s)) zl ,
            ⊑ʰ-trans {fin (z ∣ ⁺)} zh (⊓ʰ-lbˡ (fin (t ∣ ⁺) +ʰ hI) hC))
  ... | x , e , (a , b) , e∈ , xe =
    e , e∈ ,
    subst (_∈ᶻ C) (trans (sym xe) (trans (cong (_+ᴰ e) x≡t) (+ᴰ-comm t e)))
      (⊑-trans (⊔ᶜ-ubʳ ((t ∣ ⁻) +ˡ (pI ∣ sI)) (p ∣ s)) zl ,
       ⊑ʰ-trans {fin (z ∣ ⁺)} zh (⊓ʰ-lbʳ (fin (t ∣ ⁺) +ʰ hI) hC))
    where
      x≡t : x ≡ t
      x≡t = ≤ᴰ-antisym (⊑⇒≤ b) (⊑⇒≤ a)
