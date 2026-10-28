------------------------------------------------------------------------
-- The gap of a chain, in whole steps.                                --
--                                                                    --
-- The reader compares the sum of the weights poured into a chain     --
-- with the sum of its bounds. In whole steps the comparison depends  --
-- only on their difference and the two sides, so the pair of sums is --
-- summarised by a gap: an integer and two sides, or one of the       --
-- unbounded cases. Adding a weight or a bound acts on the gap, and   --
-- the comparison is read off it:                                     --
--                                                                    --
--   upper: the gap is bounds minus weights; the chain fits when it   --
--          is positive, or zero with the sides in order; an          --
--          unbounded bound fits everything (`open∞`), an unbounded   --
--          weight nothing finite (`stuck∞`);                         --
--   lower: the gap is weights minus bounds until the bounds are met, --
--          and a met chain stays met (`sat`), more weight keeping it --
--          met.                                                      --
------------------------------------------------------------------------

module Grades.Exact.Regular.Gap where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; +[1+_]; _⊖_; _-_)
import Data.Integer.Properties as ℤ
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.List.Base using (List; []; _∷_; foldr)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)
open import Grades.Durations.Intervals ℕᵀ

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Sums

sumʰ : List Hi → Hi
sumʰ = foldr _+ʰ_ (fin 0⁺)

sumˡ : List Cut → Cut
sumˡ = foldr _+ˡ_ 0⁻

------------------------------------------------------------------------
-- A cut below another, by the difference of their points

Above : ℤ → Side → Side → Set
Above +[1+ _ ] _ _ = ⊤
Above (+ 0)    s t = s ≤ˢ t
Above -[1+ _ ] _ _ = ⊥

Above? : ∀ d s t → Dec (Above d s t)
Above? +[1+ _ ] _ _ = yes tt
Above? (+ 0)    s t = s ≤ˢ? t
Above? -[1+ _ ] _ _ = no λ ()

⊑⇔Above : ∀ x s y t → ((x ∣ s) ⊑ (y ∣ t)) ⇔ Above (y ⊖ x) s t
⊑⇔Above x s y t with ℕ.<-cmp x y
... | tri< x<y _ _ = mk⇔ (λ _ → pos) (λ _ → by-pt (ℕ.<⇒≱ x<y))
  where
    pos : Above (y ⊖ x) s t
    pos rewrite ℤ.≤-⊖ (ℕ.<⇒≤ x<y) with y ℕ.∸ x in e
    ... | zero  = ⊥-elim (ℕ.<⇒≱ x<y (ℕ.m∸n≡0⇒m≤n e))
    ... | suc _ = tt
... | tri≈ _ refl _ = mk⇔ to′ from′
  where
    to′ : (x ∣ s) ⊑ (x ∣ t) → Above (x ⊖ x) s t
    to′ (by-pt r)    = ⊥-elim-irr′ r
      where ⊥-elim-irr′ : .(¬ (x ℕ.≤ x)) → Above (x ⊖ x) s t
            ⊥-elim-irr′ r = ⊥-elim (Data.Empty.⊥-elim-irr (r ℕ.≤-refl))
    to′ (by-side _ q) rewrite ℤ.n⊖n≡0 x = q
    from′ : Above (x ⊖ x) s t → (x ∣ s) ⊑ (x ∣ t)
    from′ a rewrite ℤ.n⊖n≡0 x = by-side refl a
... | tri> _ _ y<x = mk⇔ to′ (λ a → ⊥-elim (neg a))
  where
    neg : ¬ Above (y ⊖ x) s t
    neg rewrite ℤ.⊖-< y<x with x ℕ.∸ y in e
    ... | zero  = λ _ → ℕ.<⇒≱ y<x (ℕ.m∸n≡0⇒m≤n e)
    ... | suc _ = λ ()
    to′ : (x ∣ s) ⊑ (y ∣ t) → Above (y ⊖ x) s t
    to′ (by-pt r)        = ⊥-elim (Data.Empty.⊥-elim-irr (r (ℕ.<⇒≤ y<x)))
    to′ (by-side refl _) = ⊥-elim (ℕ.<-irrefl refl y<x)

-- the sign of a difference

above-⊖ : ∀ k j {s t} → Above (k ⊖ j) s t → j ℕ.≤ k
above-⊖ k j {s} {t} a with j ℕ.≤? k
... | yes r = r
... | no ¬r = ⊥-elim (neg (j ℕ.∸ k) refl (subst (λ d → Above d s t) (ℤ.⊖-< (ℕ.≰⇒> ¬r)) a))
  where
    neg : ∀ x → j ℕ.∸ k ≡ x → Above (ℤ.- (+ x)) s t → ⊥
    neg ℕ.zero    e _ = ¬r (ℕ.m∸n≡0⇒m≤n e)
    neg (ℕ.suc _) _ ()

¬above-⊖ : ∀ k j {s t} → ¬ Above (k ⊖ j) s t → k ℕ.≤ j
¬above-⊖ k j {s} {t} ¬a with k ℕ.≤? j
... | yes r = r
... | no ¬r = ⊥-elim (pos (k ℕ.∸ j) refl (λ h → ¬a (subst (λ d → Above d s t) (sym (ℤ.⊖-≥ (ℕ.<⇒≤ (ℕ.≰⇒> ¬r)))) h)))
  where
    pos : ∀ x → k ℕ.∸ j ≡ x → ¬ Above (+ x) s t → ⊥
    pos ℕ.zero    e _  = ¬r (ℕ.m∸n≡0⇒m≤n e)
    pos (ℕ.suc _) _ ¬h = ¬h tt

private
  -- arithmetic of differences
  ⊖-+ʳ : ∀ y x w → y ⊖ (x ℕ.+ w) ≡ (y ⊖ x) - + w
  ⊖-+ʳ y x w =
    trans (sym (ℤ.[+m]-[+n]≡m⊖n y (x ℕ.+ w)))
      (trans (cong (λ z → + y - z) (ℤ.pos-+ x w))
        (trans (lemma (+ y) (+ x) (+ w)) (cong (_- + w) (ℤ.[+m]-[+n]≡m⊖n y x))))
    where
      lemma : ∀ a b c → a - (b ℤ.+ c) ≡ (a - b) - c
      lemma = solve-∀

  ⊖-+ˡ : ∀ y c x → (y ℕ.+ c) ⊖ x ≡ (y ⊖ x) ℤ.+ + c
  ⊖-+ˡ y c x =
    trans (sym (ℤ.[+m]-[+n]≡m⊖n (y ℕ.+ c) x))
      (trans (cong (_- + x) (ℤ.pos-+ y c))
        (trans (lemma (+ y) (+ c) (+ x)) (cong (ℤ._+ + c) (ℤ.[+m]-[+n]≡m⊖n y x))))
    where
      lemma : ∀ a b c → (a ℤ.+ b) - c ≡ (a - c) ℤ.+ b
      lemma = solve-∀

------------------------------------------------------------------------
-- The upper gap

data Gᵁ : Set where
  gap    : ℤ → Side → Side → Gᵁ
  open∞  : Gᵁ
  stuck∞ : Gᵁ

-- the gap of a sum of weights against a sum of bounds

normᵁ : Hi → Hi → Gᵁ
normᵁ _                ∞               = open∞
normᵁ ∞                (fin _)         = stuck∞
normᵁ (fin (x ∣ s))    (fin (y ∣ t))   = gap (y ⊖ x) s t

-- a weight poured, a bound added

addpᵁ : Gᵁ → Hi → Gᵁ
addpᵁ (gap d s t) (fin (w ∣ u)) = gap (d - + w) (s ∧ˢ u) t
addpᵁ (gap _ _ _) ∞             = stuck∞
addpᵁ open∞       _             = open∞
addpᵁ stuck∞      _             = stuck∞

addcᵁ : Gᵁ → Hi → Gᵁ
addcᵁ (gap d s t) (fin (c ∣ u)) = gap (d ℤ.+ + c) s (t ∧ˢ u)
addcᵁ (gap _ _ _) ∞             = open∞
addcᵁ open∞       _             = open∞
addcᵁ stuck∞      (fin _)       = stuck∞
addcᵁ stuck∞      ∞             = open∞

fitsᵁ : Gᵁ → Set
fitsᵁ (gap d s t) = Above d s t
fitsᵁ open∞       = ⊤
fitsᵁ stuck∞      = ⊥

fitsᵁ? : ∀ g → Dec (fitsᵁ g)
fitsᵁ? (gap d s t) = Above? d s t
fitsᵁ? open∞       = yes tt
fitsᵁ? stuck∞      = no λ ()

normᵁ-addp : ∀ a b h → normᵁ (a +ʰ h) b ≡ addpᵁ (normᵁ a b) h
normᵁ-addp (fin (x ∣ s)) (fin (y ∣ t)) (fin (w ∣ u)) = cong (λ d → gap d (s ∧ˢ u) t) (⊖-+ʳ y x w)
normᵁ-addp (fin _) (fin _) ∞ = refl
normᵁ-addp (fin (_ ∣ _)) ∞ (fin (_ ∣ _)) = refl
normᵁ-addp (fin _) ∞ ∞ = refl
normᵁ-addp ∞ (fin _) _ = refl
normᵁ-addp ∞ ∞ _ = refl

normᵁ-addc : ∀ a b h → normᵁ a (b +ʰ h) ≡ addcᵁ (normᵁ a b) h
normᵁ-addc (fin (x ∣ s)) (fin (y ∣ t)) (fin (c ∣ u)) = cong (λ d → gap d s (t ∧ˢ u)) (⊖-+ˡ y c x)
normᵁ-addc (fin (_ ∣ _)) (fin (_ ∣ _)) ∞ = refl
normᵁ-addc (fin _) ∞ _ = refl
normᵁ-addc ∞ (fin (_ ∣ _)) (fin (_ ∣ _)) = refl
normᵁ-addc ∞ (fin (_ ∣ _)) ∞ = refl
normᵁ-addc ∞ ∞ _ = refl

normᵁ-fits : ∀ a b → (a ⊑ʰ b) ⇔ fitsᵁ (normᵁ a b)
normᵁ-fits (fin (x ∣ s)) (fin (y ∣ t)) = ⊑⇔Above x s y t
normᵁ-fits (fin _) ∞ = mk⇔ (λ _ → tt) (λ _ → tt)
normᵁ-fits ∞ ∞ = mk⇔ (λ _ → tt) (λ _ → tt)
normᵁ-fits ∞ (fin _) = mk⇔ (λ ()) (λ ())

------------------------------------------------------------------------
-- The lower gap

data Gᴸ : Set where
  gapᴸ : ℤ → Side → Side → Gᴸ
  sat  : Gᴸ

-- weights minus bounds, met when the bounds lie below the weights

mkᴸ : ℤ → Side → Side → Gᴸ
mkᴸ d s t with Above? d t s
... | yes _ = sat
... | no _  = gapᴸ d s t

normᴸ : Cut → Cut → Gᴸ
normᴸ (x ∣ s) (y ∣ t) = mkᴸ (x ⊖ y) s t

addpᴸ : Gᴸ → Cut → Gᴸ
addpᴸ (gapᴸ d s t) (w ∣ u) = mkᴸ (d ℤ.+ + w) (s ∨ˢ u) t
addpᴸ sat          _       = sat

addcᴸ : Gᴸ → Cut → Gᴸ
addcᴸ (gapᴸ d s t) (c ∣ u) = mkᴸ (d - + c) s (t ∨ˢ u)
addcᴸ sat          _       = sat

fitsᴸ : Gᴸ → Set
fitsᴸ (gapᴸ _ _ _) = ⊥
fitsᴸ sat          = ⊤

fitsᴸ? : ∀ g → Dec (fitsᴸ g)
fitsᴸ? (gapᴸ _ _ _) = no λ ()
fitsᴸ? sat          = yes tt

normᴸ-fits : ∀ a b → (b ⊑ a) ⇔ fitsᴸ (normᴸ a b)
normᴸ-fits (x ∣ s) (y ∣ t) with Above? (x ⊖ y) t s
... | yes p = mk⇔ (λ _ → tt) (λ _ → from (⊑⇔Above y t x s) p)
... | no ¬p = mk⇔ (λ h → ¬p (to (⊑⇔Above y t x s) h)) (λ ())

private
  mkᴸ-cong : ∀ {d d′} s t → d ≡ d′ → mkᴸ d s t ≡ mkᴸ d′ s t
  mkᴸ-cong s t refl = refl

  sat-fits : ∀ {g} → fitsᴸ g → g ≡ sat
  sat-fits {sat} _ = refl

normᴸ-addp : ∀ a b h → normᴸ (a +ˡ h) b ≡ addpᴸ (normᴸ a b) h
normᴸ-addp (x ∣ s) (y ∣ t) (w ∣ u) with Above? (x ⊖ y) t s in e
... | no _  = mkᴸ-cong (s ∨ˢ u) t (⊖-+ˡ x w y)
... | yes p = sat-fits (to (normᴸ-fits ((x ℕ.+ w) ∣ (s ∨ˢ u)) (y ∣ t))
                         (⊑-trans (from (⊑⇔Above y t x s) p) (+ˡ-inflate (x ∣ s) (w ∣ u))))

normᴸ-addc : ∀ a b h → ¬ (b ⊑ a) → normᴸ a (b +ˡ h) ≡ addcᴸ (normᴸ a b) h
normᴸ-addc (x ∣ s) (y ∣ t) (c ∣ u) ¬m with Above? (x ⊖ y) t s
... | yes p = ⊥-elim (¬m (from (⊑⇔Above y t x s) p))
... | no _  = mkᴸ-cong s (t ∨ˢ u) (trans (cong (x ⊖_) (refl {x = y ℕ.+ c})) (⊖-+ʳ x y c))
