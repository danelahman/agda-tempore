------------------------------------------------------------------------
-- Kleene's plus of a language.                                       --
--                                                                    --
-- For a language `L`, a predicate on words, `L ⁺ = L · L*` is the    --
-- least language above `L` closed under concatenation, and it        --
-- satisfies two induction laws: what `L` does not raise on one       --
-- side, `L ⁺` does not raise either. The proofs are                  --
-- about words, by induction on iteration; the grade of regular       --
-- languages (`Regular.Grade`) declares its plus from them.           --
------------------------------------------------------------------------

module Grades.Regular.Plus {A : Set} where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product.Base using (_×_; _,_; ∃₂)
open import Relation.Binary.PropositionalEquality

Word : Set
Word = List A

Lang : Set₁
Lang = Word → Set

infix  4 _⊆ˡ_
infixl 7 _·ˡ_
infix  8 _⁺

_⊆ˡ_ : Lang → Lang → Set
X ⊆ˡ Y = ∀ w → X w → Y w

_·ˡ_ : Lang → Lang → Lang
(X ·ˡ Y) w = ∃₂ λ x y → w ≡ x ++ y × X x × Y y

data Star (X : Lang) : Lang where
  none : ∀ {w} → w ≡ [] → Star X w
  more : ∀ {w} u v → w ≡ u ++ v → X u → Star X v → Star X w

_⁺ : Lang → Lang
X ⁺ = X ·ˡ Star X

------------------------------------------------------------------------
-- Iterated words

-- they concatenate

Star-++ : ∀ {X x y} → Star X x → Star X y → Star X (x ++ y)
Star-++ (none refl)            ys = ys
Star-++ {y = y} (more u v refl u∈ vs) ys =
  more u (v ++ y) (++-assoc u v y) u∈ (Star-++ vs ys)

-- a language absorbing `X` on the left absorbs its iteration

Star-absorbˡ : ∀ {X D : Lang} → (X ·ˡ D) ⊆ˡ D → ∀ {y} z → Star X y → D z → D (y ++ z)
Star-absorbˡ             f z (none refl)            z∈ = z∈
Star-absorbˡ {X} {D} f z (more u v refl u∈ vs)  z∈ =
  subst D (sym (++-assoc u v z)) (f (u ++ (v ++ z)) (u , v ++ z , refl , u∈ , Star-absorbˡ f z vs z∈))

-- ... and on the right

Star-absorbʳ : ∀ {X D : Lang} → (D ·ˡ X) ⊆ˡ D → ∀ {y} z → Star X y → D z → D (z ++ y)
Star-absorbʳ {X} {D} f z (none refl)           z∈ = subst D (sym (++-identityʳ z)) z∈
Star-absorbʳ {X} {D} f z (more u v refl u∈ vs) z∈ =
  subst D (++-assoc z u v) (Star-absorbʳ f (z ++ u) vs (f (z ++ u) (z , u , refl , z∈ , u∈)))

------------------------------------------------------------------------
-- The laws

module _ {X : Lang} where

  ⊆-⁺ : X ⊆ˡ X ⁺
  ⊆-⁺ w w∈ = w , [] , sym (++-identityʳ w) , w∈ , none refl

  ⁺-iter : (X ⁺ ·ˡ X ⁺) ⊆ˡ X ⁺
  ⁺-iter _ (_ , _ , refl , (x , y , refl , x∈ , y∈) , (z , t , refl , z∈ , t∈)) =
    x , y ++ (z ++ t) , ++-assoc x y (z ++ t) , x∈ , Star-++ y∈ (more z t refl z∈ t∈)

  ⁺-least : ∀ {V} → X ⊆ˡ V → (V ·ˡ V) ⊆ˡ V → X ⁺ ⊆ˡ V
  ⁺-least {V} xv vv _ (x , y , refl , x∈ , y∈) =
    Star-absorbʳ {X} {V} (λ { _ (z , u , refl , z∈ , u∈) → vv (z ++ u) (z , u , refl , z∈ , xv u u∈) })
      x y∈ (xv x x∈)

  ⁺-indˡ : ∀ {D} → (X ·ˡ D) ⊆ˡ D → (X ⁺ ·ˡ D) ⊆ˡ D
  ⁺-indˡ {D} xd _ (_ , z , refl , (x , y , refl , x∈ , y∈) , z∈) =
    subst D (sym (++-assoc x y z))
      (xd (x ++ (y ++ z)) (x , y ++ z , refl , x∈ , Star-absorbˡ {X} {D} xd z y∈ z∈))

  ⁺-indʳ : ∀ {D} → (D ·ˡ X) ⊆ˡ D → (D ·ˡ X ⁺) ⊆ˡ D
  ⁺-indʳ {D} dx _ (z , _ , refl , z∈ , (x , y , refl , x∈ , y∈)) =
    subst D (++-assoc z x y)
      (Star-absorbʳ {X} {D} dx (z ++ x) y∈ (dx (z ++ x) (z , x , refl , z∈ , x∈)))
