------------------------------------------------------------------------
-- The non-negative rationals ℚ≥0.                                    --
--                                                                    --
-- The endpoints of the dense-time grades. A value is a normalised    --
-- rational of the standard library together with the verdict of      --
-- `0ℚ ≤? q` as an implicit side condition; two values are equal      --
-- exactly when their rationals are, and a literal is written `n / d` --
-- (or `# n` for a whole number), the side condition being discharged --
-- by computation.                                                    --
--                                                                    --
-- `#_` embeds ℕ as a monotone monoid morphism that preserves both    --
-- lattice operations, reading whole numbers of time steps in dense   --
-- time.                                                              --
------------------------------------------------------------------------

module Syntax.Grades.Example.Time.Dense.NonNegativeRational where

open import Data.Bool.Properties using (T-irrelevant)
open import Data.Integer.Base using () renaming (+_ to +ℤ_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ
open import Data.Sum using (inj₁; inj₂)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Util.Equality

------------------------------------------------------------------------
-- The carrier

record ℚ≥0 : Set₀ where
  constructor ⟨_⟩
  field
    val       : ℚ
    {nonneg?} : True (0ℚ ℚ.≤? val)

open ℚ≥0 public

-- the side condition, as a proof

nonneg : (p : ℚ≥0) → 0ℚ ℚ.≤ val p
nonneg p = toWitness {a? = 0ℚ ℚ.≤? val p} (nonneg? p)

-- two values are equal when their rationals are

≡-val : ∀ {p q} → val p ≡ val q → p ≡ q
≡-val {_} {q} refl = cong (λ x → ⟨ val q ⟩ {x}) (T-irrelevant _ _)

------------------------------------------------------------------------
-- Literals

infix 9 _/_ #_

-- the fraction `n / d`, normalised; the instance discharging the
-- denominator's side condition is exported with it

open import Data.Nat.Base public using (nonZero)

_/_ : ℕ → (d : ℕ) → .{{ℕ.NonZero d}} → ℚ≥0
n / d = ⟨ +ℤ n ℚ./ d ⟩
          {fromWitness (ℚ.nonNegative⁻¹ _ {{ℚ.normalize-nonNeg n d}})}

------------------------------------------------------------------------
-- Zero, addition, and the embedding of ℕ

0ᵈ : ℚ≥0
0ᵈ = ⟨ 0ℚ ⟩

1ᵈ : ℚ≥0
1ᵈ = ⟨ 1ℚ ⟩

infixl 6 _+_

_+_ : ℚ≥0 → ℚ≥0 → ℚ≥0
p + q = ⟨ val p ℚ.+ val q ⟩ {fromWitness (ℚ.+-mono-≤ (nonneg p) (nonneg q))}

-- `n` time steps

#_ : ℕ → ℚ≥0
# zero    = 0ᵈ
# (suc n) = 1ᵈ + # n

-- a commutative monoid

+-identityˡ : ∀ p → 0ᵈ + p ≡ p
+-identityˡ p = ≡-val (ℚ.+-identityˡ (val p))

+-identityʳ : ∀ p → p + 0ᵈ ≡ p
+-identityʳ p = ≡-val (ℚ.+-identityʳ (val p))

+-assoc : ∀ p q r → (p + q) + r ≡ p + (q + r)
+-assoc p q r = ≡-val (ℚ.+-assoc (val p) (val q) (val r))

+-comm : ∀ p q → p + q ≡ q + p
+-comm p q = ≡-val (ℚ.+-comm (val p) (val q))

------------------------------------------------------------------------
-- The order

infix 4 _≤_ _≤?_

-- `_≤_` on the rationals, wrapped with inferable arguments

record _≤_ (p q : ℚ≥0) : Set₀ where
  constructor *≤ᵈ*
  field
    ≤-val : val p ℚ.≤ val q

open _≤_ public

≤-refl : Reflexive _≤_
≤-refl = *≤ᵈ* ℚ.≤-refl

≤-reflexive : ∀ {p q} → p ≡ q → p ≤ q
≤-reflexive refl = ≤-refl

≤-trans : Transitive _≤_
≤-trans (*≤ᵈ* p≤q) (*≤ᵈ* q≤r) = *≤ᵈ* (ℚ.≤-trans p≤q q≤r)

≤-antisym : ∀ {p q} → p ≤ q → q ≤ p → p ≡ q
≤-antisym (*≤ᵈ* p≤q) (*≤ᵈ* q≤p) = ≡-val (ℚ.≤-antisym p≤q q≤p)

≤-irrelevant : Irrelevant _≤_
≤-irrelevant (*≤ᵈ* p) (*≤ᵈ* q) = cong *≤ᵈ* (ℚ.≤-irrelevant p q)

_≤?_ : Decidable _≤_
p ≤? q = map′ *≤ᵈ* ≤-val (val p ℚ.≤? val q)

-- zero is least

0≤ : ∀ p → 0ᵈ ≤ p
0≤ p = *≤ᵈ* (nonneg p)

-- anything below zero is zero

≤0⇒≡0 : ∀ {p} → p ≤ 0ᵈ → p ≡ 0ᵈ
≤0⇒≡0 {p} p≤0 = ≤-antisym p≤0 (0≤ p)

-- addition is monotone

+-mono-≤ : ∀ {p q r s} → p ≤ q → r ≤ s → p + r ≤ q + s
+-mono-≤ (*≤ᵈ* p≤q) (*≤ᵈ* r≤s) = *≤ᵈ* (ℚ.+-mono-≤ p≤q r≤s)

+-monoˡ-≤ : ∀ r {p q} → p ≤ q → p + r ≤ q + r
+-monoˡ-≤ r p≤q = +-mono-≤ p≤q (≤-refl {r})

+-monoʳ-≤ : ∀ r {p q} → p ≤ q → r + p ≤ r + q
+-monoʳ-≤ r p≤q = +-mono-≤ (≤-refl {r}) p≤q

-- a summand is below the sum, the other being non-negative

p≤p+q : ∀ p q → p ≤ p + q
p≤p+q p q =
  ≤-trans (≤-reflexive (sym (+-identityʳ p))) (+-monoʳ-≤ p (0≤ q))

q≤p+q : ∀ p q → q ≤ p + q
q≤p+q p q = ≤-trans (p≤p+q q p) (≤-reflexive (+-comm q p))

-- a sum below zero has both summands below zero

+-≤0ˡ : ∀ {p q} → p + q ≤ 0ᵈ → p ≤ 0ᵈ
+-≤0ˡ {p} {q} r = ≤-trans (p≤p+q p q) r

+-≤0ʳ : ∀ {p q} → p + q ≤ 0ᵈ → q ≤ 0ᵈ
+-≤0ʳ {p} {q} r = ≤-trans (q≤p+q p q) r

------------------------------------------------------------------------
-- Maximum and minimum

infixl 7 _⊔_ _⊓_

_⊔_ : ℚ≥0 → ℚ≥0 → ℚ≥0
p ⊔ q = ⟨ val p ℚ.⊔ val q ⟩
          {fromWitness (ℚ.≤-trans (nonneg p) (ℚ.p≤p⊔q (val p) (val q)))}

_⊓_ : ℚ≥0 → ℚ≥0 → ℚ≥0
p ⊓ q = ⟨ val p ℚ.⊓ val q ⟩ {fromWitness (ℚ.⊓-glb (nonneg p) (nonneg q))}

-- the maximum is the least upper bound

⊔-ubˡ : ∀ p q → p ≤ p ⊔ q
⊔-ubˡ p q = *≤ᵈ* (ℚ.p≤p⊔q (val p) (val q))

⊔-ubʳ : ∀ p q → q ≤ p ⊔ q
⊔-ubʳ p q = *≤ᵈ* (ℚ.p≤q⊔p (val p) (val q))

⊔-lub : ∀ {p q r} → p ≤ r → q ≤ r → p ⊔ q ≤ r
⊔-lub (*≤ᵈ* p≤r) (*≤ᵈ* q≤r) = *≤ᵈ* (ℚ.⊔-lub p≤r q≤r)

-- the minimum is the greatest lower bound

⊓-lbˡ : ∀ p q → p ⊓ q ≤ p
⊓-lbˡ p q = *≤ᵈ* (ℚ.p⊓q≤p (val p) (val q))

⊓-lbʳ : ∀ p q → p ⊓ q ≤ q
⊓-lbʳ p q = *≤ᵈ* (ℚ.p⊓q≤q (val p) (val q))

⊓-glb : ∀ {p q r} → r ≤ p → r ≤ q → r ≤ p ⊓ q
⊓-glb (*≤ᵈ* r≤p) (*≤ᵈ* r≤q) = *≤ᵈ* (ℚ.⊓-glb r≤p r≤q)

-- addition distributes over both, being monotone

+-distribˡ-⊔ : ∀ p q r → p + (q ⊔ r) ≡ (p + q) ⊔ (p + r)
+-distribˡ-⊔ p q r =
  ≡-val (ℚ.mono-≤-distrib-⊔ (ℚ.+-monoʳ-≤ (val p)) (val q) (val r))

+-distribʳ-⊔ : ∀ p q r → (q ⊔ r) + p ≡ (q + p) ⊔ (r + p)
+-distribʳ-⊔ p q r =
  ≡-val (ℚ.mono-≤-distrib-⊔ (ℚ.+-monoˡ-≤ (val p)) (val q) (val r))

+-distribˡ-⊓ : ∀ p q r → p + (q ⊓ r) ≡ (p + q) ⊓ (p + r)
+-distribˡ-⊓ p q r =
  ≡-val (ℚ.mono-≤-distrib-⊓ (ℚ.+-monoʳ-≤ (val p)) (val q) (val r))

+-distribʳ-⊓ : ∀ p q r → (q ⊓ r) + p ≡ (q + p) ⊓ (r + p)
+-distribʳ-⊓ p q r =
  ≡-val (ℚ.mono-≤-distrib-⊓ (ℚ.+-monoˡ-≤ (val p)) (val q) (val r))

-- comparable values: the maximum is the larger, the minimum the smaller

p≤q⇒p⊔q≡q : ∀ {p q} → p ≤ q → p ⊔ q ≡ q
p≤q⇒p⊔q≡q (*≤ᵈ* p≤q) = ≡-val (ℚ.p≤q⇒p⊔q≡q p≤q)

p≥q⇒p⊔q≡p : ∀ {p q} → q ≤ p → p ⊔ q ≡ p
p≥q⇒p⊔q≡p (*≤ᵈ* q≤p) = ≡-val (ℚ.p≥q⇒p⊔q≡p q≤p)

p≤q⇒p⊓q≡p : ∀ {p q} → p ≤ q → p ⊓ q ≡ p
p≤q⇒p⊓q≡p (*≤ᵈ* p≤q) = ≡-val (ℚ.p≤q⇒p⊓q≡p p≤q)

p≥q⇒p⊓q≡q : ∀ {p q} → q ≤ p → p ⊓ q ≡ q
p≥q⇒p⊓q≡q (*≤ᵈ* q≤p) = ≡-val (ℚ.p≥q⇒p⊓q≡q q≤p)

------------------------------------------------------------------------
-- The embedding of ℕ

-- a monoid morphism

#-zero : # 0 ≡ 0ᵈ
#-zero = refl

#-+ : ∀ m n → # (m ℕ.+ n) ≡ # m + # n
#-+ zero    n = sym (+-identityˡ (# n))
#-+ (suc m) n = trans (cong (1ᵈ +_) (#-+ m n)) (sym (+-assoc 1ᵈ (# m) (# n)))

-- monotone

#-mono-≤ : ∀ {m n} → m ℕ.≤ n → # m ≤ # n
#-mono-≤ {n = n} z≤n       = 0≤ (# n)
#-mono-≤         (s≤s m≤n) = +-monoʳ-≤ 1ᵈ (#-mono-≤ m≤n)

-- preserving maximum and minimum

#-⊔ : ∀ m n → # (m ℕ.⊔ n) ≡ # m ⊔ # n
#-⊔ m n with ℕ.≤-total m n
... | inj₁ m≤n = trans (cong #_ (ℕ.m≤n⇒m⊔n≡n m≤n))
                       (sym (p≤q⇒p⊔q≡q (#-mono-≤ m≤n)))
... | inj₂ n≤m = trans (cong #_ (ℕ.m≥n⇒m⊔n≡m n≤m))
                       (sym (p≥q⇒p⊔q≡p (#-mono-≤ n≤m)))

#-⊓ : ∀ m n → # (m ℕ.⊓ n) ≡ # m ⊓ # n
#-⊓ m n with ℕ.≤-total m n
... | inj₁ m≤n = trans (cong #_ (ℕ.m≤n⇒m⊓n≡m m≤n))
                       (sym (p≤q⇒p⊓q≡p (#-mono-≤ m≤n)))
... | inj₂ n≤m = trans (cong #_ (ℕ.m≥n⇒m⊓n≡n n≤m))
                       (sym (p≥q⇒p⊓q≡q (#-mono-≤ n≤m)))
