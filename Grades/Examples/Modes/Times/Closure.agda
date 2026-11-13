------------------------------------------------------------------------
-- Closures of the mode times, through the coordinates of the boxes.  --
--                                                                    --
-- The intervals with "no trace" adjoined form a dioid with the       --
-- trivial action (`intervals`), whose star, the unit joined with the --
-- closure, is `[0 , 0]` or `[0 , ∞]` on an interval and so a Kleene  --
-- star (`interval-kleene`). A box has a coordinate at every mode,    --
-- its interval there, and one for the whole, its total, "no trace"   --
-- having "no trace" at each (`time-coordinates`): these preserve the --
-- operations and the star of the entries, are kept by exchanging two --
-- modes other than theirs, reflect the order together, and have the  --
-- box with the interval at the coordinate and `[0 , ∞]` elsewhere as --
-- right adjoint. So the star of the entries is a Kleene star, and    --
-- every mode-times grade has a closure (`Matrix.ModeCoordinates`,    --
-- used in `Modes.Times`).                                            --
------------------------------------------------------------------------

module Grades.Examples.Modes.Times.Closure where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)

open import Grades.Base using (Grade; Plus; plus; plus-self)
open import Grades.Indexed using (ℕ-names; ℕ-infinite; module Maps; Names)
open import Grades.Examples.Time.Interval
open import Grades.Examples.Modes.Times.Boxes
open import Grades.Matrix.Dioid using (Dioid)
open import Grades.Matrix.Modes ℕ-infinite using (Name; _≟ᴺ_; swap; swap-fix)
open import Grades.Matrix.Nominal ℕ-infinite using (trivial)
import Grades.Matrix.ModeGrade
import Grades.Matrix.ModeClosure
import Grades.Matrix.ModeCoordinates
import Grades.Matrix.Nominal

open import Util.Equality

open Maps ℕ-names using (Map; _∣_; _!_; others; named; everywhere; map₂; !-map₂; lookup;
                         lookup-∉; pointwise⁻; pointwise⁺; plus-map; module Pointwise)

private
  module I = Grade interval
  module 𝕊 = Dioid times

------------------------------------------------------------------------
-- The intervals with "no trace"

intervals : Dioid
intervals = B.adjoin-zero interval

private
  module 𝕋 = Dioid intervals

-- the closures: those of the intervals, and "no trace" its own

interval-plus : (x : 𝕋.Carrier) → Plus 𝕋._⊗_ 𝕋._≤_ x
interval-plus nothing  = plus-self tt tt
interval-plus (just i) =
  plus (just (Plus.c⁺ p)) (Plus.≾-c⁺ p) (Plus.c⁺-iter p)
       (λ {v} → least {v}) (λ {d} → indˡ {d}) (λ {d} → indʳ {d})
  where
    p = plusᵢ i
    least : ∀ {v} → just i 𝕋.≤ v → (v 𝕋.⊗ v) 𝕋.≤ v → just (Plus.c⁺ p) 𝕋.≤ v
    least {nothing} () _
    least {just v}  a b = Plus.c⁺-least p {v} a b
    indˡ : ∀ {d} → (just i 𝕋.⊗ d) 𝕋.≤ d → (just (Plus.c⁺ p) 𝕋.⊗ d) 𝕋.≤ d
    indˡ {nothing} _ = tt
    indˡ {just d}  q = Plus.⁺-indˡ p {d} q
    indʳ : ∀ {d} → (d 𝕋.⊗ just i) 𝕋.≤ d → (d 𝕋.⊗ just (Plus.c⁺ p)) 𝕋.≤ d
    indʳ {nothing} _ = tt
    indʳ {just d}  q = Plus.⁺-indʳ p {d} q

private
  module GT = Grades.Matrix.ModeGrade ℕ-infinite intervals (trivial intervals)
  module CT = Grades.Matrix.ModeClosure ℕ-infinite intervals (trivial intervals)

interval-stars : GT.Stars
interval-stars = GT.stars-from interval-plus

private
  starᵀ = GT.Stars.star interval-stars

  -- the values of the star: no time, or any time
  star-values : ∀ x → (starᵀ x 𝕋.≈ just 𝟏ᵢ) ⊎ (starᵀ x 𝕋.≈ just ⊤ᵢ)
  star-values nothing = inj₁ 𝕋.≈-refl
  star-values (just [ m , ↑ zero ]) = inj₁ ((ℕₚ.≤-refl , ℕₚ.≤-refl) , (ℕₚ.≤-refl , ℕₚ.≤-refl))
  star-values (just [ m , ↑ suc n ]) = inj₂ ((ℕₚ.≤-refl , tt) , (ℕₚ.≤-refl , tt))
  star-values (just [ m , ∞ ]) = inj₂ ((ℕₚ.≤-refl , tt) , (ℕₚ.≤-refl , tt))

  -- any time absorbs any time
  ⊤-absorbs : ∀ b → ((just ⊤ᵢ 𝕋.⊗ b) 𝕋.⊗ just ⊤ᵢ) 𝕋.≤ (just ⊤ᵢ 𝕋.⊗ b)
  ⊤-absorbs nothing  = tt
  ⊤-absorbs (just j) = ℕₚ.≤-reflexive (sym (ℕₚ.+-identityʳ (min j))) , tt

  tr : ∀ x y z → x 𝕋.≤ y → y 𝕋.≤ z → x 𝕋.≤ z
  tr x y z = 𝕋.≤-trans {x} {y} {z}

  mono : ∀ a a' b b' → a 𝕋.≤ a' → b 𝕋.≤ b' → (a 𝕋.⊗ b) 𝕋.≤ (a' 𝕋.⊗ b')
  mono a a' b b' = 𝕋.⊗-mono {a} {a'} {b} {b'}

  split : ∀ {s t} → (s 𝕋.≈ just 𝟏ᵢ) ⊎ (s 𝕋.≈ just ⊤ᵢ) → (t 𝕋.≈ just 𝟏ᵢ) ⊎ (t 𝕋.≈ just ⊤ᵢ)
        → ∀ b → ((s 𝕋.⊗ b) 𝕋.⊗ t) 𝕋.≤ ((s 𝕋.⊗ b) 𝕋.⊕ (b 𝕋.⊗ t))
  split {s} {t} _ (inj₁ t≈) b =
    tr L ((s 𝕋.⊗ b) 𝕋.⊗ just 𝟏ᵢ) R (mono (s 𝕋.⊗ b) (s 𝕋.⊗ b) t (just 𝟏ᵢ) (𝕋.≤-refl {s 𝕋.⊗ b}) (proj₁ t≈))
      (tr ((s 𝕋.⊗ b) 𝕋.⊗ just 𝟏ᵢ) (s 𝕋.⊗ b) R (proj₁ (𝕋.⊗-identityʳ (s 𝕋.⊗ b))) (𝕋.⊕-ubˡ (s 𝕋.⊗ b) (b 𝕋.⊗ t)))
    where L = (s 𝕋.⊗ b) 𝕋.⊗ t ; R = (s 𝕋.⊗ b) 𝕋.⊕ (b 𝕋.⊗ t)
  split {s} {t} (inj₁ s≈) (inj₂ _) b =
    tr L ((just 𝟏ᵢ 𝕋.⊗ b) 𝕋.⊗ t) R
      (mono (s 𝕋.⊗ b) (just 𝟏ᵢ 𝕋.⊗ b) t t (mono s (just 𝟏ᵢ) b b (proj₁ s≈) (𝕋.≤-refl {b})) (𝕋.≤-refl {t}))
      (tr ((just 𝟏ᵢ 𝕋.⊗ b) 𝕋.⊗ t) (b 𝕋.⊗ t) R
        (mono (just 𝟏ᵢ 𝕋.⊗ b) b t t (proj₁ (𝕋.⊗-identityˡ b)) (𝕋.≤-refl {t}))
        (𝕋.⊕-ubʳ (s 𝕋.⊗ b) (b 𝕋.⊗ t)))
    where L = (s 𝕋.⊗ b) 𝕋.⊗ t ; R = (s 𝕋.⊗ b) 𝕋.⊕ (b 𝕋.⊗ t)
  split {s} {t} (inj₂ s≈) (inj₂ t≈) b =
    tr L ((just ⊤ᵢ 𝕋.⊗ b) 𝕋.⊗ just ⊤ᵢ) R
      (mono (s 𝕋.⊗ b) (just ⊤ᵢ 𝕋.⊗ b) t (just ⊤ᵢ) (mono s (just ⊤ᵢ) b b (proj₁ s≈) (𝕋.≤-refl {b})) (proj₁ t≈))
      (tr ((just ⊤ᵢ 𝕋.⊗ b) 𝕋.⊗ just ⊤ᵢ) (just ⊤ᵢ 𝕋.⊗ b) R (⊤-absorbs b)
        (tr (just ⊤ᵢ 𝕋.⊗ b) (s 𝕋.⊗ b) R (mono (just ⊤ᵢ) s b b (proj₂ s≈) (𝕋.≤-refl {b}))
          (𝕋.⊕-ubˡ (s 𝕋.⊗ b) (b 𝕋.⊗ t))))
    where L = (s 𝕋.⊗ b) 𝕋.⊗ t ; R = (s 𝕋.⊗ b) 𝕋.⊕ (b 𝕋.⊗ t)

interval-kleene : CT.KleeneStars interval-stars
interval-kleene = record
  { star-ext   = CT.stars-from-ext interval-plus
  ; star-idem  = CT.stars-from-idem interval-plus
  ; star-split = λ a b c → split {starᵀ a} {starᵀ c} (star-values a) (star-values c) b
  }

------------------------------------------------------------------------
-- The coordinates of the entries: at a mode, and the total

private
  module MS = Maps ℕ-names
  module GS = Grades.Matrix.ModeGrade ℕ-infinite times equivariant-times
  module ES = Grades.Matrix.Nominal.Equivariant equivariant-times

  Coord : Set
  Coord = Maybe Name

  at : Coord → List Name
  at (just s) = s ∷ []
  at nothing  = []

  h : Coord → 𝕊.Carrier → 𝕋.Carrier
  h c        (nothing , _)          = nothing
  h (just s) (just (m , t) , _)     = just (m ! s)
  h nothing  (just (m , t) , _)     = just t

  -- the box with an interval at the coordinate and any time elsewhere
  single : Name → Interval∞ → Map Interval∞
  single s i = ⊤ᵢ ∣ ((s , i) ∷ [])

  single-at : ∀ s i → single s i ! s ≡ i
  single-at s i with s ≟ᴺ s
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  min∈ : ∀ i → min i ∈ᵢ i
  min∈ i = ℕₚ.≤-refl , min≤max i

  single-real : ∀ s i → Realisable (single s i) ⊤ᵢ
  single-real s i = witness ((s , min i) ∷ []) ((λ ()) , tt) , fits , (z≤n , tt)
    where
      fits : ∀ s' → time ((s , min i) ∷ []) s' ∈ᵢ single s i ! s'
      fits s' with s' ≟ᴺ s
      ... | yes _ = min∈ i
      ... | no _  = z≤n , tt

  total-real : ∀ i → Realisable (everywhere ⊤ᵢ) i
  total-real i =
    witness ((0 , min i) ∷ []) ((λ ()) , tt) , (λ s' → z≤n , tt) ,
    subst (_∈ᵢ i) (sym (ℕₚ.+-identityʳ (min i))) (min∈ i)

  g : Coord → 𝕋.Carrier → 𝕊.Carrier
  g c        nothing  = nothing , tt
  g (just s) (just i) = just (single s i , ⊤ᵢ) , single-real s i
  g nothing  (just i) = just (everywhere ⊤ᵢ , i) , total-real i

  h-mono : ∀ c {a b} → a 𝕊.≤ b → h c a 𝕋.≤ h c b
  h-mono c        {nothing , _}      _        = tt
  h-mono c        {just _ , _}  {nothing , _} ()
  h-mono (just s) {just (m , t) , _} {just (m' , t') , _} (p , q) = pointwise⁻ _≾ᵢ_ p s
  h-mono nothing  {just (m , t) , _} {just (m' , t') , _} (p , q) = q

  h-g : ∀ c {a t} → h c a 𝕋.≤ t → a 𝕊.≤ g c t
  h-g c        {nothing , _}      _ = tt
  h-g (just s) {just _ , _} {nothing} ()
  h-g nothing  {just _ , _} {nothing} ()
  h-g (just s) {just (m , t₀) , _} {just i} p =
    pointwise⁺ _≾ᵢ_ {m} {single s i} (I.≾-⊤ (others m)) at-s , I.≾-⊤ t₀
    where
      at-s : ∀ s' → (m ! s') ≾ᵢ (single s i ! s')
      at-s s' with s' ≟ᴺ s
      ... | yes refl = p
      ... | no _     = I.≾-⊤ (m ! s')
  h-g nothing  {just (m , t₀) , _} {just i} p =
    pointwise⁺ _≾ᵢ_ {m} {everywhere ⊤ᵢ} (I.≾-⊤ (others m)) (λ s' → I.≾-⊤ (m ! s')) , p

  g-h : ∀ c {a t} → a 𝕊.≤ g c t → h c a 𝕋.≤ t
  g-h c        {nothing , _}      _ = tt
  g-h c        {just _ , _} {nothing} ()
  g-h (just s) {just (m , t₀) , _} {just i} (p , _) =
    subst ((m ! s) ≾ᵢ_) (single-at s i) (pointwise⁻ _≾ᵢ_ p s)
  g-h nothing  {just (m , t₀) , _} {just i} (_ , q) = q

  ≡⇒≈ : ∀ {x y} → x ≡ y → x 𝕋.≈ y
  ≡⇒≈ {x} refl = 𝕋.≈-refl {x}

  refl≈ : ∀ x → x 𝕋.≈ x
  refl≈ x = 𝕋.≈-refl {x}

  h-⊗ : ∀ c a b → h c (a 𝕊.⊗ b) 𝕋.≈ (h c a 𝕋.⊗ h c b)
  h-⊗ c        (nothing , _)      b                  = refl≈ nothing
  h-⊗ (just s) (just _ , _)       (nothing , _)      = refl≈ nothing
  h-⊗ nothing  (just _ , _)       (nothing , _)      = refl≈ nothing
  h-⊗ (just s) (just (m , t) , _) (just (m' , t') , _) = ≡⇒≈ (cong just (!-map₂ _·ᵢ_ m m' s))
  h-⊗ nothing  (just (m , t) , _) (just (m' , t') , _) = refl≈ (just (t ·ᵢ t'))

  h-⊕ : ∀ c a b → h c (a 𝕊.⊕ b) 𝕋.≤ (h c a 𝕋.⊕ h c b)
  h-⊕ c        (nothing , _)      b                  = 𝕋.≤-refl {h c b}
  h-⊕ (just s) (just (m , t) , _) (nothing , _)      = I.≾-refl {m ! s}
  h-⊕ nothing  (just (m , t) , _) (nothing , _)      = I.≾-refl {t}
  h-⊕ (just s) (just (m , t) , _) (just (m' , t') , _) = proj₁ (≡⇒≈ (cong just (!-map₂ _⊔ᵢ_ m m' s)))
  h-⊕ nothing  (just (m , t) , _) (just (m' , t') , _) = I.≾-refl {t ⊔ᵢ t'}

  -- the closure of a map at a name is the closure there
  plus-map-! : ∀ d es s → Plus.c⁺ (plus-map interval plusᵢ (d ∣ es)) ! s ≡ Plus.c⁺ (plusᵢ (lookup d es s))
  plus-map-! d []             s = refl
  plus-map-! d ((s' , c) ∷ es) s with s ≟ᴺ s'
  ... | yes _ = refl
  ... | no _  = plus-map-! d es s

  h-star : ∀ c a → h c (GS.Stars.star (GS.stars-from times-plus) a) 𝕋.≈ starᵀ (h c a)
  h-star (just s) (nothing , _)      = refl≈ (just 𝟏ᵢ)
  h-star nothing  (nothing , _)      = refl≈ (just 𝟏ᵢ)
  h-star (just s) (just (m , t) , _) =
    ≡⇒≈ (cong just (trans (!-map₂ _⊔ᵢ_ (everywhere 𝟏ᵢ) (Plus.c⁺ (plus-map interval plusᵢ m)) s)
                     (cong (𝟏ᵢ ⊔ᵢ_) (plus-map-! (others m) (named m) s))))
  h-star nothing  (just (m , t) , _) = refl≈ (just (𝟏ᵢ ⊔ᵢ Plus.c⁺ (plusᵢ t)))

  h-act : ∀ c {a b} → a ∉ at c → b ∉ at c → ∀ x → h c (ES.act a b x) 𝕋.≈ h c x
  h-act c        a∉ b∉ (nothing , _)      = refl≈ nothing
  h-act (just s) {a} {b} a∉ b∉ (just (m , t) , _) =
    ≡⇒≈ (cong just (trans (rename-! a b m s)
                     (cong (m !_) (swap-fix (λ e → a∉ (here (sym e))) (λ e → b∉ (here (sym e)))))))
  h-act nothing  a∉ b∉ (just (m , t) , _) = refl≈ (just t)

  reflect : ∀ {a b} → (∀ c → h c a 𝕋.≤ h c b) → a 𝕊.≤ b
  reflect {nothing , _}      f = tt
  reflect {just _ , _} {nothing , _} f = ⊥-elim (f nothing)
  reflect {just (m , t) , _} {just (m' , t') , _} f =
    pointwise⁺ _≾ᵢ_ {m} {m'}
      (subst₂ _≾ᵢ_ (lookup-∉ (others m) (named m) s₀ (λ q → Names.fresh-∉ ℕ-infinite ks (∈-++⁺ˡ q)))
                   (lookup-∉ (others m') (named m') s₀ (λ q → Names.fresh-∉ ℕ-infinite ks (∈-++⁺ʳ (MS.keys m) q)))
                   (f (just s₀)))
      (λ s → f (just s))
    , f nothing
    where
      ks = MS.keys m ++ MS.keys m'
      s₀ = Names.fresh ℕ-infinite ks

time-coordinates : Grades.Matrix.ModeCoordinates.Coordinates ℕ-infinite times equivariant-times intervals
                     (GS.stars-from times-plus) interval-stars
time-coordinates = record
  { Coord    = Coord
  ; at       = at
  ; width    = 1
  ; at-width = λ { (just _) → s≤s z≤n ; nothing → z≤n }
  ; h        = h
  ; g        = g
  ; h-mono   = λ c {a} {b} → h-mono c {a} {b}
  ; h-g      = λ c {a} {t} → h-g c {a} {t}
  ; g-h      = λ c {a} {t} → g-h c {a} {t}
  ; h-⊗      = h-⊗
  ; h-⊕      = h-⊕
  ; h-𝟘      = λ _ → tt
  ; h-𝟙      = λ { (just _) → refl≈ (just 𝟏ᵢ) ; nothing → refl≈ (just 𝟏ᵢ) }
  ; h-star   = h-star
  ; h-act    = h-act
  ; reflect  = λ {a} {b} → reflect {a} {b}
  }
