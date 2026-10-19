------------------------------------------------------------------------
-- The arithmetic of a time domain.                                    --
--                                                                    --
-- Everything here is derived from the fields of `TimeDomain`: the     --
-- strict order, decidable equality, truncated subtraction `_∸ᴰ_`, the --
-- maximum and minimum, and the laws relating them to addition. The    --
-- subtraction is characterised by two facts -- below the minuend it   --
-- is the difference, otherwise it is zero -- and every other law is   --
-- proved from those two and cancellation, never by unfolding it.      --
------------------------------------------------------------------------

open import Syntax.Durations

module Syntax.Durations.Monus {D : Duration} (T : TimeDomain D) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

open Duration D public
open TimeDomain T public

private
  variable
    τ τ' τ'' κ m n o : Carrier

------------------------------------------------------------------------
-- The order and addition

0ᴰ-least : (τ : Carrier) → 0ᴰ ≤ᴰ τ
0ᴰ-least τ = subst (0ᴰ ≤ᴰ_) (+ᴰ-identityˡ τ) (≤ᴰ-+ 0ᴰ τ)

≤ᴰ-+ˡ : (τ τ' : Carrier) → τ ≤ᴰ τ' +ᴰ τ
≤ᴰ-+ˡ τ τ' = subst (τ ≤ᴰ_) (+ᴰ-comm τ τ') (≤ᴰ-+ τ τ')

≤ᴰ-reflexive : τ ≡ τ' → τ ≤ᴰ τ'
≤ᴰ-reflexive refl = ≤ᴰ-refl

-- a sum `τ + κ` that is `τ'` puts `τ` below `τ'`

≤ᴰ-intro : τ +ᴰ κ ≡ τ' → τ ≤ᴰ τ'
≤ᴰ-intro {τ} {κ} refl = ≤ᴰ-+ τ κ

+ᴰ-cancelʳ : (τ : Carrier) → τ' +ᴰ τ ≡ τ'' +ᴰ τ → τ' ≡ τ''
+ᴰ-cancelʳ {τ'} {τ''} τ e =
  +ᴰ-cancelˡ τ (trans (+ᴰ-comm τ τ') (trans e (+ᴰ-comm τ'' τ)))

+ᴰ-monoʳ-≤ : (τ : Carrier) → τ' ≤ᴰ τ'' → τ +ᴰ τ' ≤ᴰ τ +ᴰ τ''
+ᴰ-monoʳ-≤ {τ'} τ p with diff p
... | κ , e = ≤ᴰ-intro (trans (+ᴰ-assoc τ τ' κ) (cong (τ +ᴰ_) e))

+ᴰ-monoˡ-≤ : (τ : Carrier) → τ' ≤ᴰ τ'' → τ' +ᴰ τ ≤ᴰ τ'' +ᴰ τ
+ᴰ-monoˡ-≤ {τ'} {τ''} τ p =
  subst₂ _≤ᴰ_ (+ᴰ-comm τ τ') (+ᴰ-comm τ τ'') (+ᴰ-monoʳ-≤ τ p)

+ᴰ-mono-≤ : m ≤ᴰ n → τ ≤ᴰ τ' → m +ᴰ τ ≤ᴰ n +ᴰ τ'
+ᴰ-mono-≤ {n = n} {τ = τ} p q = ≤ᴰ-trans (+ᴰ-monoˡ-≤ τ p) (+ᴰ-monoʳ-≤ n q)

-- the order reflects addition

+ᴰ-cancelˡ-≤ : (τ : Carrier) → τ +ᴰ τ' ≤ᴰ τ +ᴰ τ'' → τ' ≤ᴰ τ''
+ᴰ-cancelˡ-≤ {τ'} τ p with diff p
... | κ , e = ≤ᴰ-intro (+ᴰ-cancelˡ τ (trans (sym (+ᴰ-assoc τ τ' κ)) e))

+ᴰ-cancelʳ-≤ : (τ : Carrier) → τ' +ᴰ τ ≤ᴰ τ'' +ᴰ τ → τ' ≤ᴰ τ''
+ᴰ-cancelʳ-≤ {τ'} {τ''} τ p =
  +ᴰ-cancelˡ-≤ τ (subst₂ _≤ᴰ_ (+ᴰ-comm τ' τ) (+ᴰ-comm τ'' τ) p)

-- below zero is zero

≤0⇒≡0 : τ ≤ᴰ 0ᴰ → τ ≡ 0ᴰ
≤0⇒≡0 {τ} p = ≤ᴰ-antisym p (0ᴰ-least τ)

-- no time is a sum only of no time (conicality)

zero-sumˡ : τ +ᴰ τ' ≡ 0ᴰ → τ ≡ 0ᴰ
zero-sumˡ {τ} {τ'} e = ≤0⇒≡0 (subst (τ ≤ᴰ_) e (≤ᴰ-+ τ τ'))

zero-sumʳ : τ +ᴰ τ' ≡ 0ᴰ → τ' ≡ 0ᴰ
zero-sumʳ {τ} {τ'} e = zero-sumˡ (trans (+ᴰ-comm τ' τ) e)

-- a summand that does not move the sum is zero

+ᴰ-absorbˡ : τ +ᴰ τ' ≡ τ' → τ ≡ 0ᴰ
+ᴰ-absorbˡ {τ} {τ'} e =
  +ᴰ-cancelʳ τ' (trans e (sym (+ᴰ-identityˡ τ')))

+ᴰ-absorbʳ : τ +ᴰ τ' ≡ τ → τ' ≡ 0ᴰ
+ᴰ-absorbʳ {τ} {τ'} e = +ᴰ-cancelˡ τ (trans e (sym (+ᴰ-identityʳ τ)))

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟ᴰ_

_≟ᴰ_ : DecidableEquality Carrier
τ ≟ᴰ τ' with τ ≤ᴰ? τ' | τ' ≤ᴰ? τ
... | yes p | yes q = yes (≤ᴰ-antisym p q)
... | no ¬p | _     = no λ { refl → ¬p ≤ᴰ-refl }
... | _     | no ¬q = no λ { refl → ¬q ≤ᴰ-refl }

------------------------------------------------------------------------
-- The strict order

infix 4 _<ᴰ_ _<ᴰ?_

_<ᴰ_ : Carrier → Carrier → Set₀
τ <ᴰ τ' = ¬ (τ' ≤ᴰ τ)

_<ᴰ?_ : Decidable _<ᴰ_
τ <ᴰ? τ' with τ' ≤ᴰ? τ
... | yes p = no λ q → q p
... | no ¬p = yes ¬p

<⇒≤ : τ <ᴰ τ' → τ ≤ᴰ τ'
<⇒≤ {τ} {τ'} p with ≤ᴰ-total τ τ'
... | inj₁ q = q
... | inj₂ q = ⊥-elim (p q)

<⇒≢ : τ <ᴰ τ' → τ ≢ τ'
<⇒≢ p refl = p ≤ᴰ-refl

≤∧≢⇒< : τ ≤ᴰ τ' → τ ≢ τ' → τ <ᴰ τ'
≤∧≢⇒< p ne q = ne (≤ᴰ-antisym p q)

<-irrefl : ¬ (τ <ᴰ τ)
<-irrefl p = p ≤ᴰ-refl

<-≤-trans : τ <ᴰ τ' → τ' ≤ᴰ τ'' → τ <ᴰ τ''
<-≤-trans p q r = p (≤ᴰ-trans q r)

≤-<-trans : τ ≤ᴰ τ' → τ' <ᴰ τ'' → τ <ᴰ τ''
≤-<-trans p q r = q (≤ᴰ-trans r p)

<-trans : τ <ᴰ τ' → τ' <ᴰ τ'' → τ <ᴰ τ''
<-trans p q = <-≤-trans p (<⇒≤ q)

-- a positive duration strictly increases what it is added to

<-+ : 0ᴰ <ᴰ κ → τ <ᴰ τ +ᴰ κ
<-+ {κ} {τ} p q =
  p (+ᴰ-cancelˡ-≤ τ (≤ᴰ-trans q (≤ᴰ-reflexive (sym (+ᴰ-identityʳ τ)))))

<-+ˡ : 0ᴰ <ᴰ κ → τ <ᴰ κ +ᴰ τ
<-+ˡ {κ} {τ} p = subst (τ <ᴰ_) (+ᴰ-comm τ κ) (<-+ p)

+ᴰ-monoʳ-< : (τ : Carrier) → τ' <ᴰ τ'' → τ +ᴰ τ' <ᴰ τ +ᴰ τ''
+ᴰ-monoʳ-< τ p q = p (+ᴰ-cancelˡ-≤ τ q)

+ᴰ-monoˡ-< : (τ : Carrier) → τ' <ᴰ τ'' → τ' +ᴰ τ <ᴰ τ'' +ᴰ τ
+ᴰ-monoˡ-< τ p q = p (+ᴰ-cancelʳ-≤ τ q)

-- trichotomy

data Tri (τ τ' : Carrier) : Set₀ where
  tri< : τ <ᴰ τ' → Tri τ τ'
  tri≈ : τ ≡ τ'  → Tri τ τ'
  tri> : τ' <ᴰ τ → Tri τ τ'

compare : (τ τ' : Carrier) → Tri τ τ'
compare τ τ' with τ ≤ᴰ? τ' | τ' ≤ᴰ? τ
... | yes p | yes q = tri≈ (≤ᴰ-antisym p q)
... | yes p | no ¬q = tri< ¬q
... | no ¬p | _     = tri> ¬p

------------------------------------------------------------------------
-- Truncated subtraction

infixl 6 _∸ᴰ_

_∸ᴰ_ : Carrier → Carrier → Carrier
m ∸ᴰ n with n ≤ᴰ? m
... | yes p = proj₁ (diff p)
... | no _  = 0ᴰ

-- the two facts characterising it

+-∸ : n ≤ᴰ m → n +ᴰ (m ∸ᴰ n) ≡ m
+-∸ {n} {m} p with n ≤ᴰ? m
... | yes q = proj₂ (diff q)
... | no ¬q = ⊥-elim (¬q p)

∸-≰ : ¬ (n ≤ᴰ m) → m ∸ᴰ n ≡ 0ᴰ
∸-≰ {n} {m} ¬p with n ≤ᴰ? m
... | yes q = ⊥-elim (¬p q)
... | no _  = refl

-- the difference is unique

∸-unique : n +ᴰ κ ≡ m → m ∸ᴰ n ≡ κ
∸-unique {n} {κ} {m} e = +ᴰ-cancelˡ n (trans (+-∸ (≤ᴰ-intro e)) (sym e))

∸-+ : n ≤ᴰ m → (m ∸ᴰ n) +ᴰ n ≡ m
∸-+ {n} {m} p = trans (+ᴰ-comm (m ∸ᴰ n) n) (+-∸ p)

-- below the subtrahend it is zero

∸-≤ : m ≤ᴰ n → m ∸ᴰ n ≡ 0ᴰ
∸-≤ {m} {n} p = case (n ≤ᴰ? m)
  where
    case : Dec (n ≤ᴰ m) → m ∸ᴰ n ≡ 0ᴰ
    case (yes q) = ∸-unique {n} {0ᴰ} {m} (trans (+ᴰ-identityʳ n) (≤ᴰ-antisym q p))
    case (no ¬q) = ∸-≰ ¬q

∸-self : (τ : Carrier) → τ ∸ᴰ τ ≡ 0ᴰ
∸-self τ = ∸-≤ (≤ᴰ-refl {τ})

∸-0 : (τ : Carrier) → τ ∸ᴰ 0ᴰ ≡ τ
∸-0 τ = ∸-unique (+ᴰ-identityˡ τ)

0-∸ : (τ : Carrier) → 0ᴰ ∸ᴰ τ ≡ 0ᴰ
0-∸ τ = ∸-≤ (0ᴰ-least τ)

-- cancelling a summand

m+n∸n : (m n : Carrier) → (m +ᴰ n) ∸ᴰ n ≡ m
m+n∸n m n = ∸-unique (+ᴰ-comm n m)

m+n∸m : (m n : Carrier) → (m +ᴰ n) ∸ᴰ m ≡ n
m+n∸m m n = ∸-unique refl

-- the difference is below the minuend

∸-≤-self : (m n : Carrier) → m ∸ᴰ n ≤ᴰ m
∸-≤-self m n = case (n ≤ᴰ? m)
  where
    case : Dec (n ≤ᴰ m) → m ∸ᴰ n ≤ᴰ m
    case (yes p) = ≤ᴰ-intro (trans (+ᴰ-comm (m ∸ᴰ n) n) (+-∸ p))
    case (no ¬p) = subst (_≤ᴰ m) (sym (∸-≰ ¬p)) (0ᴰ-least m)

-- associativity laws with addition

+-∸-assoc : (m : Carrier) → o ≤ᴰ n → (m +ᴰ n) ∸ᴰ o ≡ m +ᴰ (n ∸ᴰ o)
+-∸-assoc {o} {n} m p =
  ∸-unique (trans (sym (+ᴰ-assoc o m (n ∸ᴰ o)))
           (trans (cong (_+ᴰ (n ∸ᴰ o)) (+ᴰ-comm o m))
           (trans (+ᴰ-assoc m o (n ∸ᴰ o)) (cong (m +ᴰ_) (+-∸ p)))))

+-∸-comm : (n : Carrier) → o ≤ᴰ m → (m +ᴰ n) ∸ᴰ o ≡ (m ∸ᴰ o) +ᴰ n
+-∸-comm {o} {m} n p =
  trans (cong (_∸ᴰ o) (+ᴰ-comm m n))
        (trans (+-∸-assoc n p) (+ᴰ-comm n (m ∸ᴰ o)))

∸-+-assoc : (m n o : Carrier) → (m ∸ᴰ n) ∸ᴰ o ≡ m ∸ᴰ (n +ᴰ o)
∸-+-assoc m n o = case (n ≤ᴰ? m)
  where
    case : Dec (n ≤ᴰ m) → (m ∸ᴰ n) ∸ᴰ o ≡ m ∸ᴰ (n +ᴰ o)
    case (no ¬p) =
      trans (cong (_∸ᴰ o) (∸-≰ ¬p))
            (trans (0-∸ o) (sym (∸-≤ (≤ᴰ-trans (<⇒≤ ¬p) (≤ᴰ-+ n o)))))
    case (yes p) = case' (o ≤ᴰ? (m ∸ᴰ n))
      where
        case' : Dec (o ≤ᴰ m ∸ᴰ n) → (m ∸ᴰ n) ∸ᴰ o ≡ m ∸ᴰ (n +ᴰ o)
        case' (yes q) =
          sym (∸-unique (trans (+ᴰ-assoc n o ((m ∸ᴰ n) ∸ᴰ o))
                               (trans (cong (n +ᴰ_) (+-∸ q)) (+-∸ p))))
        case' (no ¬q) =
          trans (∸-≰ ¬q)
                (sym (∸-≤ (≤ᴰ-trans (≤ᴰ-reflexive (sym (+-∸ p)))
                                    (+ᴰ-monoʳ-≤ n (<⇒≤ ¬q)))))

-- what was subtracted, followed by the difference, is at least the
-- minuend

≤-+-∸ : (m n : Carrier) → m ≤ᴰ n +ᴰ (m ∸ᴰ n)
≤-+-∸ m n = case (n ≤ᴰ? m)
  where
    case : Dec (n ≤ᴰ m) → m ≤ᴰ n +ᴰ (m ∸ᴰ n)
    case (yes q) = ≤ᴰ-reflexive (sym (+-∸ q))
    case (no ¬q) =
      subst (m ≤ᴰ_) (cong (n +ᴰ_) (sym (∸-≰ ¬q)))
            (subst (m ≤ᴰ_) (sym (+ᴰ-identityʳ n)) (<⇒≤ ¬q))

-- moving a summand across

∸-≤-+ : m ≤ᴰ n +ᴰ o → m ∸ᴰ n ≤ᴰ o
∸-≤-+ {m} {n} {o} p = case (n ≤ᴰ? m)
  where
    case : Dec (n ≤ᴰ m) → m ∸ᴰ n ≤ᴰ o
    case (yes q) = +ᴰ-cancelˡ-≤ n (≤ᴰ-trans (≤ᴰ-reflexive (+-∸ q)) p)
    case (no ¬q) = subst (_≤ᴰ o) (sym (∸-≰ ¬q)) (0ᴰ-least o)

+-≤-∸ : n ≤ᴰ m → n +ᴰ o ≤ᴰ m → o ≤ᴰ m ∸ᴰ n
+-≤-∸ {n} {m} {o} p q = +ᴰ-cancelˡ-≤ n (≤ᴰ-trans q (≤ᴰ-reflexive (sym (+-∸ p))))

-- monotone in the minuend, antitone in the subtrahend

∸-monoˡ-≤ : (o : Carrier) → m ≤ᴰ n → m ∸ᴰ o ≤ᴰ n ∸ᴰ o
∸-monoˡ-≤ {m} {n} o p = case (o ≤ᴰ? m)
  where
    case : Dec (o ≤ᴰ m) → m ∸ᴰ o ≤ᴰ n ∸ᴰ o
    case (no ¬q) = subst (_≤ᴰ n ∸ᴰ o) (sym (∸-≰ ¬q)) (0ᴰ-least (n ∸ᴰ o))
    case (yes q) = +-≤-∸ (≤ᴰ-trans q p) (≤ᴰ-trans (≤ᴰ-reflexive (+-∸ q)) p)

∸-monoʳ-≤ : (m : Carrier) → n ≤ᴰ o → m ∸ᴰ o ≤ᴰ m ∸ᴰ n
∸-monoʳ-≤ {n} {o} m p =
  ∸-≤-+ (≤ᴰ-trans (≤-+-∸ m n) (+ᴰ-monoˡ-≤ (m ∸ᴰ n) p))

------------------------------------------------------------------------
-- Maximum and minimum

infixl 7 _⊔ᴰ_ _⊓ᴰ_

_⊔ᴰ_ : Carrier → Carrier → Carrier
τ ⊔ᴰ τ' with τ ≤ᴰ? τ'
... | yes _ = τ'
... | no _  = τ

_⊓ᴰ_ : Carrier → Carrier → Carrier
τ ⊓ᴰ τ' with τ ≤ᴰ? τ'
... | yes _ = τ
... | no _  = τ'

⊔-ubˡ : (τ τ' : Carrier) → τ ≤ᴰ τ ⊔ᴰ τ'
⊔-ubˡ τ τ' with τ ≤ᴰ? τ'
... | yes p = p
... | no _  = ≤ᴰ-refl

⊔-ubʳ : (τ τ' : Carrier) → τ' ≤ᴰ τ ⊔ᴰ τ'
⊔-ubʳ τ τ' with τ ≤ᴰ? τ'
... | yes _ = ≤ᴰ-refl
... | no ¬p = <⇒≤ ¬p

⊔-lub : τ ≤ᴰ τ'' → τ' ≤ᴰ τ'' → τ ⊔ᴰ τ' ≤ᴰ τ''
⊔-lub {τ} {τ''} {τ'} p q with τ ≤ᴰ? τ'
... | yes _ = q
... | no _  = p

⊓-lbˡ : (τ τ' : Carrier) → τ ⊓ᴰ τ' ≤ᴰ τ
⊓-lbˡ τ τ' with τ ≤ᴰ? τ'
... | yes _ = ≤ᴰ-refl
... | no ¬p = <⇒≤ ¬p

⊓-lbʳ : (τ τ' : Carrier) → τ ⊓ᴰ τ' ≤ᴰ τ'
⊓-lbʳ τ τ' with τ ≤ᴰ? τ'
... | yes p = p
... | no _  = ≤ᴰ-refl

⊓-glb : τ'' ≤ᴰ τ → τ'' ≤ᴰ τ' → τ'' ≤ᴰ τ ⊓ᴰ τ'
⊓-glb {τ''} {τ} {τ'} p q with τ ≤ᴰ? τ'
... | yes _ = p
... | no _  = q
