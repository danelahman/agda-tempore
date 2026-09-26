------------------------------------------------------------------------
-- The power of a grade: `n` counters, each graded by `G`.             --
--                                                                     --
-- A grade of `power n` is a vector of `n` grades of `G`, one per      --
-- counter, and everything is pointwise: the product, the order, the   --
-- greatest grade and the joins. Laws hold coordinatewise, so every    --
-- law of `G` carries over, zero-product included.                     --
--                                                                     --
-- The inclusion of ℕ is the unit. Time steps are not drawn from any   --
-- counter, so `n` steps leave every counter untouched; time is paired --
-- with the counters by a product of grades, not stored among them.    --
------------------------------------------------------------------------

open import Syntax.Grades

module Syntax.Grades.Example.Counts.Power (G : Grade) where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Maybe.Base using (just; nothing; maybe′)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Data.Vec.Base using (Vec; []; _∷_; zipWith; replicate; lookup; tabulate)
open import Data.Vec.Properties
  using (lookup-zipWith; lookup-replicate; tabulate∘lookup; tabulate-cong)

open import Algebra.Definitions using (Commutative)

open import Relation.Binary.Definitions using (Minimum)
open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

open Grade G
  renaming (Carrier to C; _≾_ to _≾ᴳ_; u to uᴳ; ⊤ to ⊤ᴳ; _·_ to _·ᴳ_;
            _⊔_ to _⊔ᴳ_; _≾?_ to _≾ᴳ?_; ≾-refl to ≾ᴳ-refl;
            ≾-trans to ≾ᴳ-trans; ≾-antisym to ≾ᴳ-antisym;
            ≾-irrelevant to ≾ᴳ-irrelevant)

------------------------------------------------------------------------
-- The operations, pointwise

infixl 7 _·ᵛ_
infixl 6 _⊔ᵛ_
infix  5 _≾ᵛ_

_·ᵛ_ : ∀ {n} → Vec C n → Vec C n → Vec C n
_·ᵛ_ = zipWith _·ᴳ_

uᵛ : ∀ {n} → Vec C n
uᵛ {n} = replicate n uᴳ

⊤ᵛ : ∀ {n} → Vec C n
⊤ᵛ {n} = replicate n ⊤ᴳ

_⊔ᵛ_ : ∀ {n} → Vec C n → Vec C n → Vec C n
_⊔ᵛ_ = zipWith _⊔ᴳ_

_≾ᵛ_ : ∀ {n} → Vec C n → Vec C n → Set
[]       ≾ᵛ []       = 𝟙
(a ∷ as) ≾ᵛ (b ∷ bs) = a ≾ᴳ b × as ≾ᵛ bs

------------------------------------------------------------------------
-- Coordinates

lookup-ext : ∀ {n} {c d : Vec C n}
           → (∀ i → lookup c i ≡ lookup d i) → c ≡ d
lookup-ext {c = c} {d} p =
  trans (sym (tabulate∘lookup c)) (trans (tabulate-cong p) (tabulate∘lookup d))

≾ᵛ-lookup : ∀ {n} {c d : Vec C n} → c ≾ᵛ d → (i : Fin n) → lookup c i ≾ᴳ lookup d i
≾ᵛ-lookup {c = _ ∷ _} {_ ∷ _} (p , _) zero    = p
≾ᵛ-lookup {c = _ ∷ _} {_ ∷ _} (_ , q) (suc i) = ≾ᵛ-lookup q i

lookup-≾ᵛ : ∀ {n} {c d : Vec C n} → ((i : Fin n) → lookup c i ≾ᴳ lookup d i) → c ≾ᵛ d
lookup-≾ᵛ {c = []}    {[]}    p = tt
lookup-≾ᵛ {c = _ ∷ _} {_ ∷ _} p = p zero , lookup-≾ᵛ (λ i → p (suc i))

lookup-·ᵛ : ∀ {n} (c d : Vec C n) (i : Fin n)
          → lookup (c ·ᵛ d) i ≡ lookup c i ·ᴳ lookup d i
lookup-·ᵛ c d i = lookup-zipWith _·ᴳ_ i c d

lookup-⊔ᵛ : ∀ {n} (c d : Vec C n) (i : Fin n)
          → lookup (c ⊔ᵛ d) i ≡ lookup c i ⊔ᴳ lookup d i
lookup-⊔ᵛ c d i = lookup-zipWith _⊔ᴳ_ i c d

lookup-uᵛ : ∀ {n} (i : Fin n) → lookup (uᵛ {n}) i ≡ uᴳ
lookup-uᵛ i = lookup-replicate i uᴳ

lookup-⊤ᵛ : ∀ {n} (i : Fin n) → lookup (⊤ᵛ {n}) i ≡ ⊤ᴳ
lookup-⊤ᵛ i = lookup-replicate i ⊤ᴳ

------------------------------------------------------------------------
-- The monoid

·ᵛ-identityˡ : ∀ {n} (c : Vec C n) → uᵛ ·ᵛ c ≡ c
·ᵛ-identityˡ []       = refl
·ᵛ-identityˡ (a ∷ as) = cong₂ _∷_ (·-identityˡ a) (·ᵛ-identityˡ as)

·ᵛ-identityʳ : ∀ {n} (c : Vec C n) → c ·ᵛ uᵛ ≡ c
·ᵛ-identityʳ []       = refl
·ᵛ-identityʳ (a ∷ as) = cong₂ _∷_ (·-identityʳ a) (·ᵛ-identityʳ as)

·ᵛ-assoc : ∀ {n} (c d e : Vec C n) → (c ·ᵛ d) ·ᵛ e ≡ c ·ᵛ (d ·ᵛ e)
·ᵛ-assoc []       []       []       = refl
·ᵛ-assoc (a ∷ as) (b ∷ bs) (c ∷ cs) =
  cong₂ _∷_ (·-assoc a b c) (·ᵛ-assoc as bs cs)

·ᵛ-comm : Commutative _≡_ _·ᴳ_ → ∀ {n} (c d : Vec C n) → c ·ᵛ d ≡ d ·ᵛ c
·ᵛ-comm comm []       []       = refl
·ᵛ-comm comm (a ∷ as) (b ∷ bs) = cong₂ _∷_ (comm a b) (·ᵛ-comm comm as bs)

------------------------------------------------------------------------
-- The order

≾ᵛ-refl : ∀ {n} {c : Vec C n} → c ≾ᵛ c
≾ᵛ-refl {c = []}    = tt
≾ᵛ-refl {c = _ ∷ _} = ≾ᴳ-refl , ≾ᵛ-refl

≾ᵛ-reflexive : ∀ {n} {c d : Vec C n} → c ≡ d → c ≾ᵛ d
≾ᵛ-reflexive refl = ≾ᵛ-refl

≾ᵛ-trans : ∀ {n} {c d e : Vec C n} → c ≾ᵛ d → d ≾ᵛ e → c ≾ᵛ e
≾ᵛ-trans {c = []}    {[]}    {[]}    _       _       = tt
≾ᵛ-trans {c = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) (q , qs) =
  ≾ᴳ-trans p q , ≾ᵛ-trans ps qs

≾ᵛ-antisym : ∀ {n} {c d : Vec C n} → c ≾ᵛ d → d ≾ᵛ c → c ≡ d
≾ᵛ-antisym {c = []}    {[]}    _       _       = refl
≾ᵛ-antisym {c = _ ∷ _} {_ ∷ _} (p , ps) (q , qs) =
  cong₂ _∷_ (≾ᴳ-antisym p q) (≾ᵛ-antisym ps qs)

≾ᵛ-irrelevant : ∀ {n} {c d : Vec C n} → (p q : c ≾ᵛ d) → p ≡ q
≾ᵛ-irrelevant {c = []}    {[]}    tt       tt       = refl
≾ᵛ-irrelevant {c = _ ∷ _} {_ ∷ _} (p , ps) (q , qs) =
  cong₂ _,_ (≾ᴳ-irrelevant p q) (≾ᵛ-irrelevant ps qs)

infix 5 _≾ᵛ?_

_≾ᵛ?_ : ∀ {n} (c d : Vec C n) → Dec (c ≾ᵛ d)
[]       ≾ᵛ? []       = yes tt
(a ∷ as) ≾ᵛ? (b ∷ bs) with a ≾ᴳ? b | as ≾ᵛ? bs
... | yes p | yes ps = yes (p , ps)
... | no ¬p | _      = no λ r → ¬p (proj₁ r)
... | yes _ | no ¬ps = no λ r → ¬ps (proj₂ r)

≾ᵛ-⊤ : ∀ {n} (c : Vec C n) → c ≾ᵛ ⊤ᵛ
≾ᵛ-⊤ []       = tt
≾ᵛ-⊤ (a ∷ as) = ≾-⊤ a , ≾ᵛ-⊤ as

------------------------------------------------------------------------
-- Joins

⊔ᵛ-ubˡ : ∀ {n} (c d : Vec C n) → c ≾ᵛ c ⊔ᵛ d
⊔ᵛ-ubˡ []       []       = tt
⊔ᵛ-ubˡ (a ∷ as) (b ∷ bs) = ⊔-ubˡ a b , ⊔ᵛ-ubˡ as bs

⊔ᵛ-ubʳ : ∀ {n} (c d : Vec C n) → d ≾ᵛ c ⊔ᵛ d
⊔ᵛ-ubʳ []       []       = tt
⊔ᵛ-ubʳ (a ∷ as) (b ∷ bs) = ⊔-ubʳ a b , ⊔ᵛ-ubʳ as bs

⊔ᵛ-lub : ∀ {n} {c d e : Vec C n} → c ≾ᵛ e → d ≾ᵛ e → c ⊔ᵛ d ≾ᵛ e
⊔ᵛ-lub {c = []}    {[]}    {[]}    _        _        = tt
⊔ᵛ-lub {c = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) (q , qs) =
  ⊔-lub p q , ⊔ᵛ-lub ps qs

------------------------------------------------------------------------
-- Monotonicity and distributivity

·ᵛ-monoˡ : ∀ {n} {e c d : Vec C n} → c ≾ᵛ d → c ·ᵛ e ≾ᵛ d ·ᵛ e
·ᵛ-monoˡ {e = []}    {[]}    {[]}    _        = tt
·ᵛ-monoˡ {e = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) = ·-monoˡ-≾ p , ·ᵛ-monoˡ ps

·ᵛ-monoʳ : ∀ {n} {e c d : Vec C n} → c ≾ᵛ d → e ·ᵛ c ≾ᵛ e ·ᵛ d
·ᵛ-monoʳ {e = []}    {[]}    {[]}    _        = tt
·ᵛ-monoʳ {e = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) = ·-monoʳ-≾ p , ·ᵛ-monoʳ ps

·ᵛ-distribˡ-⊔ᵛ : ∀ {n} (c d e : Vec C n) → c ·ᵛ (d ⊔ᵛ e) ≾ᵛ (c ·ᵛ d) ⊔ᵛ (c ·ᵛ e)
·ᵛ-distribˡ-⊔ᵛ []       []       []       = tt
·ᵛ-distribˡ-⊔ᵛ (a ∷ as) (b ∷ bs) (c ∷ cs) =
  ·-distribˡ-⊔-≾ a b c , ·ᵛ-distribˡ-⊔ᵛ as bs cs

·ᵛ-distribʳ-⊔ᵛ : ∀ {n} (c d e : Vec C n) → (d ⊔ᵛ e) ·ᵛ c ≾ᵛ (d ·ᵛ c) ⊔ᵛ (e ·ᵛ c)
·ᵛ-distribʳ-⊔ᵛ []       []       []       = tt
·ᵛ-distribʳ-⊔ᵛ (a ∷ as) (b ∷ bs) (c ∷ cs) =
  ·-distribʳ-⊔-≾ a b c , ·ᵛ-distribʳ-⊔ᵛ as bs cs

------------------------------------------------------------------------
-- Zero-product property, coordinatewise

≾ᵛ-zero-productˡ : ∀ {n} {c d : Vec C n} → c ·ᵛ d ≾ᵛ uᵛ → c ≾ᵛ uᵛ
≾ᵛ-zero-productˡ {c = []}    {[]}    _        = tt
≾ᵛ-zero-productˡ {c = _ ∷ _} {_ ∷ _} (p , ps) =
  ≾-zero-productˡ p , ≾ᵛ-zero-productˡ ps

≾ᵛ-zero-productʳ : ∀ {n} {c d : Vec C n} → c ·ᵛ d ≾ᵛ uᵛ → d ≾ᵛ uᵛ
≾ᵛ-zero-productʳ {c = []}    {[]}    _        = tt
≾ᵛ-zero-productʳ {c = _ ∷ _} {_ ∷ _} (p , ps) =
  ≾-zero-productʳ p , ≾ᵛ-zero-productʳ ps

------------------------------------------------------------------------
-- The greatest grade absorbs joins, and products where `G`'s does

⊤ᵛ-⊔ᵛ : ∀ {n} (c : Vec C n) → ⊤ᵛ ⊔ᵛ c ≡ ⊤ᵛ
⊤ᵛ-⊔ᵛ []       = refl
⊤ᵛ-⊔ᵛ (a ∷ as) = cong₂ _∷_ (trans (⊔-comm ⊤ᴳ a) (⊔-⊤ a)) (⊤ᵛ-⊔ᵛ as)

⊔ᵛ-⊤ᵛ : ∀ {n} (c : Vec C n) → c ⊔ᵛ ⊤ᵛ ≡ ⊤ᵛ
⊔ᵛ-⊤ᵛ []       = refl
⊔ᵛ-⊤ᵛ (a ∷ as) = cong₂ _∷_ (⊔-⊤ a) (⊔ᵛ-⊤ᵛ as)

⊤ᵛ-·ᵛ : (∀ a → ⊤ᴳ ·ᴳ a ≡ ⊤ᴳ) → ∀ {n} (c : Vec C n) → ⊤ᵛ ·ᵛ c ≡ ⊤ᵛ
⊤ᵛ-·ᵛ absorb []       = refl
⊤ᵛ-·ᵛ absorb (a ∷ as) = cong₂ _∷_ (absorb a) (⊤ᵛ-·ᵛ absorb as)

·ᵛ-⊤ᵛ : (∀ a → a ·ᴳ ⊤ᴳ ≡ ⊤ᴳ) → ∀ {n} (c : Vec C n) → c ·ᵛ ⊤ᵛ ≡ ⊤ᵛ
·ᵛ-⊤ᵛ absorb []       = refl
·ᵛ-⊤ᵛ absorb (a ∷ as) = cong₂ _∷_ (absorb a) (·ᵛ-⊤ᵛ absorb as)

------------------------------------------------------------------------
-- Grades given coordinate by coordinate

tabulate-·ᵛ : ∀ {n} (f g : Fin n → C)
            → tabulate (λ i → f i ·ᴳ g i) ≡ tabulate f ·ᵛ tabulate g
tabulate-·ᵛ {zero}  f g = refl
tabulate-·ᵛ {suc n} f g = cong (f zero ·ᴳ g zero ∷_) (tabulate-·ᵛ (λ i → f (suc i)) (λ i → g (suc i)))

tabulate-⊔ᵛ : ∀ {n} (f g : Fin n → C)
            → tabulate (λ i → f i ⊔ᴳ g i) ≡ tabulate f ⊔ᵛ tabulate g
tabulate-⊔ᵛ {zero}  f g = refl
tabulate-⊔ᵛ {suc n} f g = cong (f zero ⊔ᴳ g zero ∷_) (tabulate-⊔ᵛ (λ i → f (suc i)) (λ i → g (suc i)))

tabulate-uᵛ : ∀ {n} (f : Fin n → C) → (∀ i → f i ≡ uᴳ) → tabulate f ≡ uᵛ
tabulate-uᵛ {zero}  f p = refl
tabulate-uᵛ {suc n} f p = cong₂ _∷_ (p zero) (tabulate-uᵛ (λ i → f (suc i)) (λ i → p (suc i)))

tabulate-≾ᵛ : ∀ {n} {f g : Fin n → C} → (∀ i → f i ≾ᴳ g i) → tabulate f ≾ᵛ tabulate g
tabulate-≾ᵛ {zero}  p = tt
tabulate-≾ᵛ {suc n} p = p zero , tabulate-≾ᵛ (λ i → p (suc i))

------------------------------------------------------------------------
-- The declared properties carry over

uᵛ-least : Minimum _≾ᴳ_ uᴳ → ∀ {n} → Minimum (_≾ᵛ_ {n}) uᵛ
uᵛ-least least []       = tt
uᵛ-least least (a ∷ as) = least a , uᵛ-least least as

------------------------------------------------------------------------
-- The grade

power : ℕ → Grade
power n = record
  { Carrier         = Vec C n
  ; _·_             = _·ᵛ_
  ; u               = uᵛ
  ; ·-identityˡ     = ·ᵛ-identityˡ
  ; ·-identityʳ     = ·ᵛ-identityʳ
  ; ·-assoc         = ·ᵛ-assoc
  ; _≾_             = _≾ᵛ_
  ; ⊤               = ⊤ᵛ
  ; ≾-⊤             = ≾ᵛ-⊤
  ; u-least?        = maybe′ (λ least → just (uᵛ-least least)) nothing u-least?
  ; ·-comm?         = maybe′ (λ comm → just (·ᵛ-comm comm)) nothing ·-comm?
  ; _⊔_             = _⊔ᵛ_
  ; ⊔-ubˡ           = ⊔ᵛ-ubˡ
  ; ⊔-ubʳ           = ⊔ᵛ-ubʳ
  ; ⊔-lub           = λ {c} {d} {e} → ⊔ᵛ-lub {c = c} {d} {e}
  ; ·-distribˡ-⊔-≾  = ·ᵛ-distribˡ-⊔ᵛ
  ; ·-distribʳ-⊔-≾  = ·ᵛ-distribʳ-⊔ᵛ
  ; ·-monoˡ-≾       = λ {e} {c} {d} → ·ᵛ-monoˡ {e = e} {c} {d}
  ; ·-monoʳ-≾       = λ {e} {c} {d} → ·ᵛ-monoʳ {e = e} {c} {d}
  ; ≾-refl          = λ {c} → ≾ᵛ-refl {c = c}
  ; ≾-trans         = λ {c} {d} {e} → ≾ᵛ-trans {c = c} {d} {e}
  ; ≾-antisym       = λ {c} {d} → ≾ᵛ-antisym {c = c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵛ-irrelevant {c = c} {d}
  ; _≾?_            = _≾ᵛ?_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵛ-zero-productˡ {c = c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵛ-zero-productʳ {c = c} {d}
  ; of-nat          = λ _ → uᵛ
  ; of-nat-zero     = refl
  ; of-nat-plus     = sym (·ᵛ-identityˡ uᵛ)
  }
