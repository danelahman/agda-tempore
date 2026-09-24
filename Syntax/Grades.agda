--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Syntax.Grades where

open import Algebra.Definitions using (Commutative)
open import Data.Empty
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)

open import Level hiding (_⊔_) renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

-- Partially ordered effect and resource monoids

record Grade : Set₁ where
  infixl 7 _·_
  infixl 6 _⊔_
  infixl 5 _≾_

  field

    -- carrier and operations
    Carrier : Set₀
    _·_     : Carrier → Carrier → Carrier
    u       : Carrier
    _≾_     : Rel Carrier lzero
    ⊤       : Carrier
    _⊔_     : Carrier → Carrier → Carrier
    of-nat  : ℕ → Carrier

    -- a monoid
    ·-identityˡ : (c : Carrier) → (u · c) ≡ c
    ·-identityʳ : (c : Carrier) → (c · u) ≡ c
    ·-assoc     : (c d e : Carrier) → (c · d) · e ≡ c · (d · e)

    -- a partial order, decidable and proof-irrelevant
    ≾-refl       : Reflexive _≾_
    ≾-trans      : Transitive _≾_
    ≾-antisym    : {c d : Carrier} → c ≾ d → d ≾ c → c ≡ d
    ≾-irrelevant : ∀ {c d} → (p q : c ≾ d) → p ≡ q
    _≾?_         : Decidable _≾_

    -- ⊤ is the greatest grade
    ≾-⊤ : (c : Carrier) → c ≾ ⊤

    -- ⊔ is a binary join
    ⊔-ubˡ : (c d : Carrier) → c ≾ c ⊔ d
    ⊔-ubʳ : (c d : Carrier) → d ≾ c ⊔ d
    ⊔-lub : {c d e : Carrier} → c ≾ e → d ≾ e → c ⊔ d ≾ e

    -- an ordered monoid; · distributes over ⊔ (the converse
    -- inequalities follow from monotonicity)
    ·-monoˡ-≾      : ∀ {c} → _Preserves_⟶_ (_· c) _≾_ _≾_
    ·-monoʳ-≾      : ∀ {c} → _Preserves_⟶_ (c ·_) _≾_ _≾_
    ·-distribˡ-⊔-≾ : (c d e : Carrier) → c · (d ⊔ e) ≾ (c · d) ⊔ (c · e)
    ·-distribʳ-⊔-≾ : (c d e : Carrier) → (d ⊔ e) · c ≾ (d · c) ⊔ (e · c)

    -- the unit's zero-product property
    ≾-zero-productˡ : ∀ {c d} → c · d ≾ u → c ≾ u
    ≾-zero-productʳ : ∀ {c d} → c · d ≾ u → d ≾ u

    -- ℕ included as a monoid morphism, `n` the grade of `n` time steps
    of-nat-zero : of-nat 0 ≡ u
    of-nat-plus : ∀ {m n} → of-nat (m + n) ≡ of-nat m · of-nat n

    -- optional declared properties

    -- whether the unit is least, where the grade declares it
    u-least? : Maybe (Minimum _≾_ u)

    -- commutativity of `_·_`, where the grade declares it; the trace
    -- grades leave it out, as there it depends on whether `Op` is empty
    ·-comm? : Maybe (Commutative _≡_ _·_)

  -- _≡_ is included in _≾_
  ≾-reflexive  : _≡_ ⇒ _≾_
  ≾-reflexive refl = ≾-refl

  -- _≡_ (on Carrier) is decidable: by antisymmetry, two grades are
  -- equal exactly when each is below the other
  _≡?_ : Decidable (_≡_ {A = Carrier})
  c ≡? d with c ≾? d | d ≾? c
  ... | yes p | yes q = yes (≾-antisym p q)
  ... | yes _ | no ¬q = no λ eq → ¬q (≾-reflexive (sym eq))
  ... | no ¬p | _     = no λ eq → ¬p (≾-reflexive eq)

  -- _⊔_ is monotone with respect to _≾_
  ⊔-mono : ∀ {c c' d d'} → c ≾ c' → d ≾ d' → c ⊔ d ≾ c' ⊔ d'
  ⊔-mono {c' = c'} {d' = d'} p q =
    ⊔-lub (≾-trans p (⊔-ubˡ c' d')) (≾-trans q (⊔-ubʳ c' d'))

  -- _⊔_ is idempotent, commutative and associative: each direction is
  -- a least upper bound, and antisymmetry turns the pair into an
  -- equation
  ⊔-idem : (c : Carrier) → c ⊔ c ≡ c
  ⊔-idem c = ≾-antisym (⊔-lub ≾-refl ≾-refl) (⊔-ubˡ c c)

  ⊔-comm : (c d : Carrier) → c ⊔ d ≡ d ⊔ c
  ⊔-comm c d = ≾-antisym (⊔-lub (⊔-ubʳ d c) (⊔-ubˡ d c))
                         (⊔-lub (⊔-ubʳ c d) (⊔-ubˡ c d))

  ⊔-assoc : (c d e : Carrier) → (c ⊔ d) ⊔ e ≡ c ⊔ (d ⊔ e)
  ⊔-assoc c d e =
    ≾-antisym
      (⊔-lub (⊔-lub (⊔-ubˡ c (d ⊔ e))
                    (≾-trans (⊔-ubˡ d e) (⊔-ubʳ c (d ⊔ e))))
             (≾-trans (⊔-ubʳ d e) (⊔-ubʳ c (d ⊔ e))))
      (⊔-lub (≾-trans (⊔-ubˡ c d) (⊔-ubˡ (c ⊔ d) e))
             (⊔-lub (≾-trans (⊔-ubʳ c d) (⊔-ubˡ (c ⊔ d) e))
                    (⊔-ubʳ (c ⊔ d) e)))

  -- a grade below another is absorbed by it in a join
  ⊔-absorb : ∀ {c d} → c ≾ d → c ⊔ d ≡ d
  ⊔-absorb {c} {d} p = ≾-antisym (⊔-lub p ≾-refl) (⊔-ubʳ c d)

  -- ⊤ absorbs joins
  ⊔-⊤ : (c : Carrier) → c ⊔ ⊤ ≡ ⊤
  ⊔-⊤ c = ⊔-absorb (≾-⊤ c)

  -- `_·_` distributes over `_⊔_`: the converse of each field follows
  -- from `_·_` being monotone in each argument separately, so the two
  -- sides are equal
  ·-distribˡ-⊔ : (c d e : Carrier) → c · (d ⊔ e) ≡ (c · d) ⊔ (c · e)
  ·-distribˡ-⊔ c d e =
    ≾-antisym (·-distribˡ-⊔-≾ c d e)
              (⊔-lub (·-monoʳ-≾ (⊔-ubˡ d e)) (·-monoʳ-≾ (⊔-ubʳ d e)))

  ·-distribʳ-⊔ : (c d e : Carrier) → (d ⊔ e) · c ≡ (d · c) ⊔ (e · c)
  ·-distribʳ-⊔ c d e =
    ≾-antisym (·-distribʳ-⊔-≾ c d e)
              (⊔-lub (·-monoˡ-≾ (⊔-ubˡ d e)) (·-monoˡ-≾ (⊔-ubʳ d e)))

open Grade


-- Morphisms of effect and resource monoids

record _→ᵍ_ (G₁ G₂ : Grade) : Set₁ where
  open Grade G₁ renaming (Carrier to C₁; _≾_ to _≾₁_; u to u₁; _·_ to _·₁_;
                          ⊤ to ⊤₁; _⊔_ to _⊔₁_; of-nat to of-nat₁)
  open Grade G₂ renaming (Carrier to C₂; _≾_ to _≾₂_; u to u₂; _·_ to _·₂_;
                          ⊤ to ⊤₂; _⊔_ to _⊔₂_; of-nat to of-nat₂)
  
  field

    -- map between carriers of grades
    map    : C₁ → C₂

    -- map is monotone
    map-monotone : {c₁ c₁' : C₁} → (c₁ ≾₁ c₁') → (map c₁ ≾₂ map c₁')

    -- map preserves the monoid structure
    map-u        : map u₁ ≡ u₂
    map-·        : {c₁ c₁' : C₁} → map (c₁ ·₁ c₁') ≡ map c₁ ·₂ map c₁'

    -- map preserves the greatest grade
    map-⊤        : map ⊤₁ ≡ ⊤₂

    -- map preserves binary joins
    map-⊔        : {c₁ c₁' : C₁} → map (c₁ ⊔₁ c₁') ≡ map c₁ ⊔₂ map c₁'

    -- map preserves inclusion of ℕ
    map-of-nat   : ∀ {n} → map (of-nat₁ n) ≡ of-nat₂ n


-- Grade systems

record GradeSystem : Set₂ where

  field

    RGrade : Grade
    EGrade : Grade
    ∣_∣ᵉ : EGrade →ᵍ RGrade


-- Helpful module exporting effect and resource grade fields with different names

module GradeSystemInterface (GS : GradeSystem) where

  open GradeSystem GS public

  open Grade RGrade renaming
    (Carrier to R;
     _·_ to _·ᵣ_;
     u to uᵣ;
     _≾_ to _≾ᵣ_;
     ⊤ to ⊤ᵣ;
     _⊔_ to _⊔ᵣ_;
     of-nat to of-natʳ;
     ·-identityˡ to ·ᵣ-identityˡ;
     ·-identityʳ to ·ᵣ-identityʳ;
     ·-assoc to ·ᵣ-assoc;
     ≾-refl to ≾ᵣ-refl;
     ≾-trans to ≾ᵣ-trans;
     ≾-antisym to ≾ᵣ-antisym;
     ≾-irrelevant to ≾ᵣ-irrelevant;
     _≾?_ to _≾ᵣ?_;
     ≾-⊤ to ≾-⊤ᵣ;
     ⊔-ubˡ to ⊔ᵣ-ubˡ;
     ⊔-ubʳ to ⊔ᵣ-ubʳ;
     ⊔-lub to ⊔ᵣ-lub;
     ·-monoˡ-≾ to ·ᵣ-monoˡ-≾ᵣ;
     ·-monoʳ-≾ to ·ᵣ-monoʳ-≾ᵣ;
     ·-distribˡ-⊔-≾ to ·ᵣ-distribˡ-⊔ᵣ-≾ᵣ;
     ·-distribʳ-⊔-≾ to ·ᵣ-distribʳ-⊔ᵣ-≾ᵣ;
     ≾-zero-productˡ to ≾ᵣ-zero-productˡ;
     ≾-zero-productʳ to ≾ᵣ-zero-productʳ;
     of-nat-zero to of-natʳ-zero;
     of-nat-plus to of-natʳ-plus;
     u-least? to uᵣ-least?;
     ·-comm? to ·ᵣ-comm?;
     ≾-reflexive to ≾ᵣ-reflexive;
     _≡?_ to _≡ᵣ?_;
     ⊔-mono to ⊔ᵣ-mono;
     ⊔-idem to ⊔ᵣ-idem;
     ⊔-comm to ⊔ᵣ-comm;
     ⊔-assoc to ⊔ᵣ-assoc;
     ⊔-absorb to ⊔ᵣ-absorb;
     ⊔-⊤ to ⊔ᵣ-⊤ᵣ;
     ·-distribˡ-⊔ to ·ᵣ-distribˡ-⊔ᵣ;
     ·-distribʳ-⊔ to ·ᵣ-distribʳ-⊔ᵣ
    ) public

  open Grade EGrade renaming
    (Carrier to E;
     _·_ to _·ₑ_;
     u to uₑ;
     _≾_ to _≾ₑ_;
     ⊤ to ⊤ₑ;
     _⊔_ to _⊔ₑ_;
     of-nat to of-natᵉ;
     ·-identityˡ to ·ₑ-identityˡ;
     ·-identityʳ to ·ₑ-identityʳ;
     ·-assoc to ·ₑ-assoc;
     ≾-refl to ≾ₑ-refl;
     ≾-trans to ≾ₑ-trans;
     ≾-antisym to ≾ₑ-antisym;
     ≾-irrelevant to ≾ₑ-irrelevant;
     _≾?_ to _≾ₑ?_;
     ≾-⊤ to ≾-⊤ₑ;
     ⊔-ubˡ to ⊔ₑ-ubˡ;
     ⊔-ubʳ to ⊔ₑ-ubʳ;
     ⊔-lub to ⊔ₑ-lub;
     ·-monoˡ-≾ to ·ₑ-monoˡ-≾ₑ;
     ·-monoʳ-≾ to ·ₑ-monoʳ-≾ₑ;
     ·-distribˡ-⊔-≾ to ·ₑ-distribˡ-⊔ₑ-≾ₑ;
     ·-distribʳ-⊔-≾ to ·ₑ-distribʳ-⊔ₑ-≾ₑ;
     of-nat-zero to of-natᵉ-zero;
     of-nat-plus to of-natᵉ-plus;
     u-least? to uₑ-least?;
     ·-comm? to ·ₑ-comm?;
     ≾-reflexive to ≾ₑ-reflexive;
     _≡?_ to _≡ₑ?_;
     ⊔-mono to ⊔ₑ-mono;
     ⊔-idem to ⊔ₑ-idem;
     ⊔-comm to ⊔ₑ-comm;
     ⊔-assoc to ⊔ₑ-assoc;
     ⊔-absorb to ⊔ₑ-absorb;
     ⊔-⊤ to ⊔ₑ-⊤ₑ;
     ·-distribˡ-⊔ to ·ₑ-distribˡ-⊔ₑ;
     ·-distribʳ-⊔ to ·ₑ-distribʳ-⊔ₑ
   ) public

  open _→ᵍ_ ∣_∣ᵉ renaming
    (map to mapᵉ;
     map-monotone to map-monotoneᵉ;
     map-u to map-uᵉ;
     map-· to map-·ᵉ;
     map-⊤ to map-⊤ᵉ;
     map-⊔ to map-⊔ᵉ;
     map-of-nat to map-of-natᵉ
    ) public
