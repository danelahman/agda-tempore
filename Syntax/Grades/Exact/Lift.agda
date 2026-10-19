------------------------------------------------------------------------
-- Sets of exact words, ordered by the ∀∃ lift of the fit order.      --
--                                                                    --
-- A grade denotes a set of exact words, the runs it describes:       --
--                                                                    --
--   X ≾ Y   iff   every word of X fits some word of Y                --
--                                                                    --
-- The product sequences a word of one set with a word of the other,  --
-- the join is the union, the unit is the empty word, and every word  --
-- fits the unrestricted stretch of its own duration, so the set of   --
-- all words and the stretches of every length admitting every        --
-- operation are both greatest. The product is monotone, distributes  --
-- over the join, and has the zero-product property once the other   --
-- factor is inhabited.                                               --
--                                                                    --
-- Sets are predicates, and sequencing within them concatenates       --
-- words without merging: the order does not see how stretches are    --
-- merged (`Exact.Order`), so the normal form plays no part here.     --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Exact.Lift
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Subset using (_⊆_) renaming (⊤ to all; ⊥ to none)
open import Data.Fin.Subset.Properties using (⊆⊤; ∈⊤)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T

open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Order T Op n code code-injective

private
  ≮⇒≥ : ∀ {p d} → ¬ (p <ᴰ d) → d ≤ᴰ p
  ≮⇒≥ {p} {d} ¬p with d ≤ᴰ? p
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

  ∸-<-intro : ∀ {d p e} → d ≤ᴰ p → p <ᴰ d +ᴰ e → p ∸ᴰ d <ᴰ e
  ∸-<-intro {d} {p} r s t =
    s (≤ᴰ-trans (+ᴰ-monoʳ-≤ d t) (≤ᴰ-reflexive (+-∸ r)))

------------------------------------------------------------------------
-- Words with the same labels fit each other

≡ˡ⇒⊑ : ∀ {x y} → dur x ≡ dur y → (∀ p → p <ᴰ dur y → lab x p ≡ lab y p) → x ⊑ y
≡ˡ⇒⊑ e h = fits e (λ p r → ≤ˡ-reflexive (h p r))

-- the labels of a stretch

lab-stretch : ∀ S τ {p} → p <ᴰ τ → lab (stretch S τ) p ≡ bud S
lab-stretch S τ {p} r = case (0ᴰ <ᴰ? τ)
  where
    case : (c : Dec (0ᴰ <ᴰ τ)) → lab (stretch-of S τ c) p ≡ bud S
    case (yes q) = lab-here {st (pos⁺ τ q) S} {[]} r
    case (no ¬q) = ⊥-elim (¬q (≤-<-trans (0ᴰ-least p) r))

------------------------------------------------------------------------
-- Concatenation is monotone

⊑-++ : ∀ {x x′ y y′} → x ⊑ x′ → y ⊑ y′ → x ++ y ⊑ x′ ++ y′
⊑-++ {x} {x′} {y} {y′} (fits e h) (fits e′ h′) =
  fits (trans (dur-++ x y) (trans (cong₂ _+ᴰ_ e e′) (sym (dur-++ x′ y′)))) at
  where
    at : ∀ p → p <ᴰ dur (x′ ++ y′) → lab (x ++ y) p ≤ˡ lab (x′ ++ y′) p
    at p r = case (p <ᴰ? dur x′)
      where
        r′ : p <ᴰ dur x′ +ᴰ dur y′
        r′ = subst (p <ᴰ_) (dur-++ x′ y′) r
        case : Dec (p <ᴰ dur x′) → lab (x ++ y) p ≤ˡ lab (x′ ++ y′) p
        case (yes s) =
          subst₂ _≤ˡ_ (sym (lab-++ˡ x y (subst (p <ᴰ_) (sym e) s)))
                      (sym (lab-++ˡ x′ y′ s)) (h p s)
        case (no ¬s) =
          subst₂ _≤ˡ_ (sym (trans (lab-++ʳ x y (subst (λ z → ¬ (p <ᴰ z)) (sym e) ¬s))
                                  (cong (λ z → lab y (p ∸ᴰ z)) e)))
                      (sym (lab-++ʳ x′ y′ ¬s))
                      (h′ (p ∸ᴰ dur x′) (∸-<-intro (≮⇒≥ ¬s) r′))

-- a word fits the stretch of its duration admitting every operation

≤ˡ-all : ∀ ℓ → ℓ ≤ˡ bud all
≤ˡ-all (bud S)     = bud≤bud ⊆⊤
≤ˡ-all (opl o δ d) = opl≤bud ∈⊤

⊑-all : ∀ x → x ⊑ stretch all (dur x)
⊑-all x =
  fits (sym (dur-stretch all (dur x)))
       (λ p r → subst (lab x p ≤ˡ_)
                      (sym (lab-stretch all (dur x) (subst (p <ᴰ_) (dur-stretch all (dur x)) r)))
                      (≤ˡ-all (lab x p)))

------------------------------------------------------------------------
-- Sets of words

Lang : Set₁
Lang = Word → Set

infix  4 _≾_ _⊆ᴸ_ _≈_
infixl 7 _·ᴸ_
infixl 6 _∪ᴸ_

_≾_ : Lang → Lang → Set
X ≾ Y = ∀ x → X x → Σ[ y ∈ Word ] Y y × x ⊑ y

_≈_ : Lang → Lang → Set
X ≈ Y = X ≾ Y × Y ≾ X

_⊆ᴸ_ : Lang → Lang → Set
X ⊆ᴸ Y = ∀ x → X x → Y x

_·ᴸ_ : Lang → Lang → Lang
(X ·ᴸ Y) w = Σ[ x ∈ Word ] Σ[ y ∈ Word ] w ≡ x ++ y × X x × Y y

_∪ᴸ_ : Lang → Lang → Lang
(X ∪ᴸ Y) w = X w ⊎ Y w

uᴸ : Lang
uᴸ w = w ≡ []

⊤ᴸ : Lang
⊤ᴸ _ = ⊤

-- the stretches of every length admitting every operation

anyᴸ : Lang
anyᴸ w = Σ[ τ ∈ Carrier ] w ≡ stretch all τ

-- the strict wait of a duration

of-durᴸ : Carrier → Lang
of-durᴸ τ w = w ≡ ![ τ ]

------------------------------------------------------------------------
-- A preorder

⊆⇒≾ : ∀ {X Y} → X ⊆ᴸ Y → X ≾ Y
⊆⇒≾ s x x∈ = x , s x x∈ , ⊑-refl

≾-refl : ∀ {X} → X ≾ X
≾-refl = ⊆⇒≾ (λ _ x∈ → x∈)

≾-trans : ∀ {X Y Z} → X ≾ Y → Y ≾ Z → X ≾ Z
≾-trans f g x x∈ with f x x∈
... | y , y∈ , xy with g y y∈
...   | z , z∈ , yz = z , z∈ , ⊑-trans xy yz

-- greatest elements

≾-⊤ : ∀ X → X ≾ ⊤ᴸ
≾-⊤ X x _ = x , tt , ⊑-refl

≾-any : ∀ X → X ≾ anyᴸ
≾-any X x _ = stretch all (dur x) , (dur x , refl) , ⊑-all x

-- joins

∪-ubˡ : ∀ X Y → X ≾ X ∪ᴸ Y
∪-ubˡ X Y = ⊆⇒≾ (λ _ → inj₁)

∪-ubʳ : ∀ X Y → Y ≾ X ∪ᴸ Y
∪-ubʳ X Y = ⊆⇒≾ (λ _ → inj₂)

∪-lub : ∀ {X Y Z} → X ≾ Z → Y ≾ Z → X ∪ᴸ Y ≾ Z
∪-lub f g x (inj₁ x∈) = f x x∈
∪-lub f g x (inj₂ x∈) = g x x∈

-- the product is monotone

·-mono : ∀ {X X′ Y Y′} → X ≾ X′ → Y ≾ Y′ → X ·ᴸ Y ≾ X′ ·ᴸ Y′
·-mono f g w (x , y , refl , x∈ , y∈) with f x x∈ | g y y∈
... | x′ , x′∈ , xx′ | y′ , y′∈ , yy′ =
  x′ ++ y′ , (x′ , y′ , refl , x′∈ , y′∈) , ⊑-++ xx′ yy′

-- and distributes over joins

·-distribˡ : ∀ X Y Z → X ·ᴸ (Y ∪ᴸ Z) ≾ (X ·ᴸ Y) ∪ᴸ (X ·ᴸ Z)
·-distribˡ X Y Z = ⊆⇒≾ λ
  { w (x , y , e , x∈ , inj₁ y∈) → inj₁ (x , y , e , x∈ , y∈)
  ; w (x , y , e , x∈ , inj₂ y∈) → inj₂ (x , y , e , x∈ , y∈) }

·-distribʳ : ∀ X Y Z → (Y ∪ᴸ Z) ·ᴸ X ≾ (Y ·ᴸ X) ∪ᴸ (Z ·ᴸ X)
·-distribʳ X Y Z = ⊆⇒≾ λ
  { w (y , x , e , inj₁ y∈ , x∈) → inj₁ (y , x , e , y∈ , x∈)
  ; w (y , x , e , inj₂ y∈ , x∈) → inj₂ (y , x , e , y∈ , x∈) }

-- the monoid laws, up to equivalence

·-identityˡ : ∀ X → uᴸ ·ᴸ X ≈ X
·-identityˡ X =
  ⊆⇒≾ (λ { w (x , y , refl , refl , y∈) → y∈ }) ,
  ⊆⇒≾ (λ w w∈ → [] , w , refl , refl , w∈)

·-identityʳ : ∀ X → X ·ᴸ uᴸ ≈ X
·-identityʳ X =
  ⊆⇒≾ (λ { w (x , y , refl , x∈ , refl) → subst X (sym (++-identityʳ x)) x∈ }) ,
  ⊆⇒≾ (λ w w∈ → w , [] , sym (++-identityʳ w) , w∈ , refl)

·-assoc : ∀ X Y Z → (X ·ᴸ Y) ·ᴸ Z ≈ X ·ᴸ (Y ·ᴸ Z)
·-assoc X Y Z =
  ⊆⇒≾ (λ { w (_ , z , refl , (x , y , refl , x∈ , y∈) , z∈) →
             x , y ++ z , ++-assoc x y z , x∈ , (y , z , refl , y∈ , z∈) }) ,
  ⊆⇒≾ (λ { w (x , _ , refl , x∈ , (y , z , refl , y∈ , z∈)) →
             x ++ y , z , sym (++-assoc x y z) , (x , y , refl , x∈ , y∈) , z∈ })

-- the zero-product property, against an inhabited factor

++-conicalˡ : ∀ (x : Word) {y} → x ++ y ≡ [] → x ≡ []
++-conicalˡ []      _  = refl
++-conicalˡ (_ ∷ _) ()

++-conicalʳ : ∀ (x : Word) {y} → x ++ y ≡ [] → y ≡ []
++-conicalʳ []      e  = e
++-conicalʳ (_ ∷ _) ()

zero-productˡ : ∀ {X Y} → (∃ Y) → X ·ᴸ Y ≾ uᴸ → X ≾ uᴸ
zero-productˡ {X} {Y} (y , y∈) f x x∈ with f (x ++ y) (x , y , refl , x∈ , y∈)
... | _ , refl , r = [] , refl , subst (_⊑ []) (sym (++-conicalˡ x (⊑-ε r))) ⊑-refl

zero-productʳ : ∀ {X Y} → (∃ X) → X ·ᴸ Y ≾ uᴸ → Y ≾ uᴸ
zero-productʳ {X} {Y} (x , x∈) f y y∈ with f (x ++ y) (x , y , refl , x∈ , y∈)
... | _ , refl , r = [] , refl , subst (_⊑ []) (sym (++-conicalʳ x (⊑-ε r))) ⊑-refl

-- strict waits are a monoid morphism

of-dur-zero : of-durᴸ 0ᴰ ≈ uᴸ
of-dur-zero =
  ⊆⇒≾ (λ w e → trans e ![]-zero) , ⊆⇒≾ (λ w e → trans e (sym ![]-zero))

of-dur-plus : ∀ m n → of-durᴸ (m +ᴰ n) ≈ of-durᴸ m ·ᴸ of-durᴸ n
of-dur-plus m n =
  (λ w e → ![ m ] ++ ![ n ] , (![ m ] , ![ n ] , refl , refl , refl) ,
           subst (_⊑ ![ m ] ++ ![ n ]) (sym e) (sum⊑ m n)) ,
  (λ { w (x , y , refl , refl , refl) →
         ![ m +ᴰ n ] , refl , sum⊒ m n })
  where
    -- the merged wait and the concatenated waits have the same labels
    lab-waits : ∀ m n p → p <ᴰ m +ᴰ n → lab ![ m +ᴰ n ] p ≡ lab (![ m ] ++ ![ n ]) p
    lab-waits m n p r = trans (lab-stretch none (m +ᴰ n) r) (sym (case (p <ᴰ? dur ![ m ])))
      where
        case : Dec (p <ᴰ dur ![ m ]) → lab (![ m ] ++ ![ n ]) p ≡ bud none
        case (yes s) =
          trans (lab-++ˡ ![ m ] ![ n ] s)
                (lab-stretch none m (subst (p <ᴰ_) (dur-stretch none m) s))
        case (no ¬s) =
          trans (lab-++ʳ ![ m ] ![ n ] ¬s)
                (lab-stretch none n
                  (∸-<-intro (≮⇒≥ ¬s)
                    (subst (p <ᴰ_) (cong (_+ᴰ n) (sym (dur-stretch none m))) r)))
    dur-waits : ∀ m n → dur ![ m +ᴰ n ] ≡ dur (![ m ] ++ ![ n ])
    dur-waits m n = trans (dur-stretch none (m +ᴰ n))
                     (sym (trans (dur-++ ![ m ] ![ n ])
                                 (cong₂ _+ᴰ_ (dur-stretch none m) (dur-stretch none n))))
    sum⊑ : ∀ m n → ![ m +ᴰ n ] ⊑ ![ m ] ++ ![ n ]
    sum⊑ m n = ≡ˡ⇒⊑ (dur-waits m n)
                 (λ p r → lab-waits m n p
                   (subst (p <ᴰ_) (trans (sym (dur-waits m n)) (dur-stretch none (m +ᴰ n))) r))
    sum⊒ : ∀ m n → ![ m ] ++ ![ n ] ⊑ ![ m +ᴰ n ]
    sum⊒ m n = ≡ˡ⇒⊑ (sym (dur-waits m n))
                 (λ p r → sym (lab-waits m n p (subst (p <ᴰ_) (dur-stretch none (m +ᴰ n)) r)))
