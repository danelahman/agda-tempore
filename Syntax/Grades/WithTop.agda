------------------------------------------------------------------------
-- Adjoining a greatest grade.                                         --
--                                                                     --
-- Not every ordered monoid of grades has a `≾`-greatest element: the   --
-- subset grades' floor would need the empty set of demands, which is   --
-- excluded, and the allowance grades' cap would need the set of all    --
-- runs, which is not finite. This module adds one point above          --
-- everything, absorbing in the product. It asks nothing of the monoid  --
-- it extends, so it applies wherever a top is missing.                 --
--                                                                     --
-- Adjoining is not the only way to get a top: where the unit is        --
-- already greatest (`Time.LeftSided`, the coverage floor) the grade is --
-- left alone. The two differ in one respect that matters downstream --  --
-- an adjoined top is absorbing, a unit top is not -- and `map-·` alone --
-- forces a morphism out of an absorbing top to land on one too, so a   --
-- morphism out of an extended grade needs an extended one to land in.  --
--                                                                     --
-- The input is a `Grade` minus its `⊤` and `≾-⊤`, which is what a      --
-- grade without a top has to offer; `forgetTop` supplies it from a     --
-- grade that already has one.                                          --
------------------------------------------------------------------------

module Syntax.Grades.WithTop where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades

open import Util.Equality

------------------------------------------------------------------------
-- Grades without a designated top

record OrderedMonoid : Set₁ where
  infixl 7 _·_
  infixl 5 _≾_

  field

    Carrier : Set₀

    _·_ : Carrier → Carrier → Carrier
    u   : Carrier

    ·-identityʳ : (c : Carrier) → (c · u) ≡ c
    ·-identityˡ : (c : Carrier) → (u · c) ≡ c
    ·-assoc     : (c d e : Carrier) → (c · d) · e ≡ c · (d · e)

    _≾_ : Rel Carrier lzero

    ·-monoˡ-≾ : ∀ {c} → _Preserves_⟶_ (_· c) _≾_ _≾_
    ·-monoʳ-≾ : ∀ {c} → _Preserves_⟶_ (c ·_) _≾_ _≾_

    ≾-refl  : Reflexive _≾_
    ≾-trans : Transitive _≾_

    ≾-irrelevant : ∀ {c d} → (p q : c ≾ d) → p ≡ q

    _≡?_ : Decidable (_≡_ {A = Carrier})

    ≾-zero-productˡ : ∀ {c d} → c · d ≾ u → c ≾ u
    ≾-zero-productʳ : ∀ {c d} → c · d ≾ u → d ≾ u

    of-nat      : ℕ → Carrier
    of-nat-zero : of-nat 0 ≡ u
    of-nat-plus : ∀ {m n} → of-nat (m + n) ≡ of-nat m · of-nat n

-- a grade that already has a top can be extended again

forgetTop : Grade → OrderedMonoid
forgetTop G = record
  { Carrier         = Carrier
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ·-monoˡ-≾       = λ {c} {d} {e} → ·-monoˡ-≾ {c} {d} {e}
  ; ·-monoʳ-≾       = λ {c} {d} {e} → ·-monoʳ-≾ {c} {d} {e}
  ; ≾-refl          = λ {c} → ≾-refl {c}
  ; ≾-trans         = λ {c} {d} {e} → ≾-trans {c} {d} {e}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; _≡?_            = _≡?_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
  where open Grade G

------------------------------------------------------------------------
-- The extension

module Adjoin (M : OrderedMonoid) where

  open OrderedMonoid M

  -- `only c` is a grade of the monoid extended; `⊤ᵍ` is the new point,
  -- above all of them

  infix 8 only_

  data Ext : Set₀ where
    only_ : Carrier → Ext
    ⊤ᵍ    : Ext

  only-inj : {c d : Carrier} → only c ≡ only d → c ≡ d
  only-inj refl = refl

  ----------------------------------------------------------------------
  -- The monoid, with the new point absorbing

  infixl 7 _·ᵉ_

  _·ᵉ_ : Ext → Ext → Ext
  (only c) ·ᵉ (only d) = only (c · d)
  (only _) ·ᵉ ⊤ᵍ       = ⊤ᵍ
  ⊤ᵍ       ·ᵉ _        = ⊤ᵍ

  uᵉ : Ext
  uᵉ = only u

  ·ᵉ-identityʳ : (c : Ext) → c ·ᵉ uᵉ ≡ c
  ·ᵉ-identityʳ (only c) = cong only_ (·-identityʳ c)
  ·ᵉ-identityʳ ⊤ᵍ       = refl

  ·ᵉ-identityˡ : (c : Ext) → uᵉ ·ᵉ c ≡ c
  ·ᵉ-identityˡ (only c) = cong only_ (·-identityˡ c)
  ·ᵉ-identityˡ ⊤ᵍ       = refl

  ·ᵉ-assoc : (c d e : Ext) → (c ·ᵉ d) ·ᵉ e ≡ c ·ᵉ (d ·ᵉ e)
  ·ᵉ-assoc (only c) (only d) (only e) = cong only_ (·-assoc c d e)
  ·ᵉ-assoc (only _) (only _) ⊤ᵍ       = refl
  ·ᵉ-assoc (only _) ⊤ᵍ       (only _) = refl
  ·ᵉ-assoc (only _) ⊤ᵍ       ⊤ᵍ       = refl
  ·ᵉ-assoc ⊤ᵍ       _        _        = refl

  ----------------------------------------------------------------------
  -- The order, with the new point on top

  infix 5 _≾ᵉ_

  _≾ᵉ_ : Rel Ext lzero
  (only c) ≾ᵉ (only d) = c ≾ d
  (only _) ≾ᵉ ⊤ᵍ       = ⊤
  ⊤ᵍ       ≾ᵉ (only _) = ⊥
  ⊤ᵍ       ≾ᵉ ⊤ᵍ       = ⊤

  ≾ᵉ-⊤ : (c : Ext) → c ≾ᵉ ⊤ᵍ
  ≾ᵉ-⊤ (only _) = tt
  ≾ᵉ-⊤ ⊤ᵍ       = tt

  ≾ᵉ-refl : Reflexive _≾ᵉ_
  ≾ᵉ-refl {only _} = ≾-refl
  ≾ᵉ-refl {⊤ᵍ}     = tt

  ≾ᵉ-trans : Transitive _≾ᵉ_
  ≾ᵉ-trans {only _} {only _} {only _} p q = ≾-trans p q
  ≾ᵉ-trans {only _} {only _} {⊤ᵍ}     p q = tt
  ≾ᵉ-trans {only _} {⊤ᵍ}     {only _} p ()
  ≾ᵉ-trans {only _} {⊤ᵍ}     {⊤ᵍ}     p q = tt
  ≾ᵉ-trans {⊤ᵍ}     {only _} {_}      () q
  ≾ᵉ-trans {⊤ᵍ}     {⊤ᵍ}     {only _} p ()
  ≾ᵉ-trans {⊤ᵍ}     {⊤ᵍ}     {⊤ᵍ}     p q = tt

  ≾ᵉ-irrelevant : ∀ {c d} → (p q : c ≾ᵉ d) → p ≡ q
  ≾ᵉ-irrelevant {only _} {only _} p  q  = ≾-irrelevant p q
  ≾ᵉ-irrelevant {only _} {⊤ᵍ}     tt tt = refl
  ≾ᵉ-irrelevant {⊤ᵍ}     {only _} () q
  ≾ᵉ-irrelevant {⊤ᵍ}     {⊤ᵍ}     tt tt = refl

  ·ᵉ-monoˡ-≾ᵉ : ∀ {e} → _Preserves_⟶_ (_·ᵉ e) _≾ᵉ_ _≾ᵉ_
  ·ᵉ-monoˡ-≾ᵉ {only _} {only _} {only _} p = ·-monoˡ-≾ p
  ·ᵉ-monoˡ-≾ᵉ {⊤ᵍ}     {only _} {only _} p = tt
  ·ᵉ-monoˡ-≾ᵉ {only _} {only _} {⊤ᵍ}     p = tt
  ·ᵉ-monoˡ-≾ᵉ {⊤ᵍ}     {only _} {⊤ᵍ}     p = tt
  ·ᵉ-monoˡ-≾ᵉ {_}      {⊤ᵍ}     {only _} ()
  ·ᵉ-monoˡ-≾ᵉ {only _} {⊤ᵍ}     {⊤ᵍ}     p = tt
  ·ᵉ-monoˡ-≾ᵉ {⊤ᵍ}     {⊤ᵍ}     {⊤ᵍ}     p = tt

  ·ᵉ-monoʳ-≾ᵉ : ∀ {e} → _Preserves_⟶_ (e ·ᵉ_) _≾ᵉ_ _≾ᵉ_
  ·ᵉ-monoʳ-≾ᵉ {only _} {only _} {only _} p = ·-monoʳ-≾ p
  ·ᵉ-monoʳ-≾ᵉ {⊤ᵍ}     {only _} {only _} p = tt
  ·ᵉ-monoʳ-≾ᵉ {only _} {only _} {⊤ᵍ}     p = tt
  ·ᵉ-monoʳ-≾ᵉ {⊤ᵍ}     {only _} {⊤ᵍ}     p = tt
  ·ᵉ-monoʳ-≾ᵉ {_}      {⊤ᵍ}     {only _} ()
  ·ᵉ-monoʳ-≾ᵉ {only _} {⊤ᵍ}     {⊤ᵍ}     p = tt
  ·ᵉ-monoʳ-≾ᵉ {⊤ᵍ}     {⊤ᵍ}     {⊤ᵍ}     p = tt

  ----------------------------------------------------------------------
  -- Zero-product, decidable equality, and the inclusion of ℕ
  --
  -- The new point sits above the unit and not below it, so every clause
  -- mentioning it is vacuous and the property is inherited.

  ≾ᵉ-zero-productˡ : ∀ {c d} → c ·ᵉ d ≾ᵉ uᵉ → c ≾ᵉ uᵉ
  ≾ᵉ-zero-productˡ {only _} {only _} p = ≾-zero-productˡ p
  ≾ᵉ-zero-productˡ {only _} {⊤ᵍ}     ()
  ≾ᵉ-zero-productˡ {⊤ᵍ}     {_}      ()

  ≾ᵉ-zero-productʳ : ∀ {c d} → c ·ᵉ d ≾ᵉ uᵉ → d ≾ᵉ uᵉ
  ≾ᵉ-zero-productʳ {only _} {only _} p = ≾-zero-productʳ p
  ≾ᵉ-zero-productʳ {only _} {⊤ᵍ}     ()
  ≾ᵉ-zero-productʳ {⊤ᵍ}     {_}      ()

  _≡ᵉ?_ : Decidable (_≡_ {A = Ext})
  (only c) ≡ᵉ? (only d) with c ≡? d
  ... | yes p = yes (cong only_ p)
  ... | no ¬p = no λ eq → ¬p (only-inj eq)
  (only _) ≡ᵉ? ⊤ᵍ       = no λ ()
  ⊤ᵍ       ≡ᵉ? (only _) = no λ ()
  ⊤ᵍ       ≡ᵉ? ⊤ᵍ       = yes refl

  of-natᵉ : ℕ → Ext
  of-natᵉ n = only (of-nat n)

  of-natᵉ-zero : of-natᵉ 0 ≡ uᵉ
  of-natᵉ-zero = cong only_ of-nat-zero

  of-natᵉ-plus : ∀ {m n} → of-natᵉ (m + n) ≡ of-natᵉ m ·ᵉ of-natᵉ n
  of-natᵉ-plus {m} {n} = cong only_ (of-nat-plus {m} {n})

  ----------------------------------------------------------------------
  -- The extended grade

  withTop : Grade
  withTop = record
    { Carrier         = Ext
    ; _·_             = _·ᵉ_
    ; u               = uᵉ
    ; ·-identityʳ     = ·ᵉ-identityʳ
    ; ·-identityˡ     = ·ᵉ-identityˡ
    ; ·-assoc         = ·ᵉ-assoc
    ; _≾_             = _≾ᵉ_
    ; ⊤               = ⊤ᵍ
    ; ≾-⊤             = ≾ᵉ-⊤
    ; ·-monoˡ-≾       = λ {e} {c} {d} → ·ᵉ-monoˡ-≾ᵉ {e} {c} {d}
    ; ·-monoʳ-≾       = λ {e} {c} {d} → ·ᵉ-monoʳ-≾ᵉ {e} {c} {d}
    ; ≾-refl          = λ {c} → ≾ᵉ-refl {c}
    ; ≾-trans         = λ {c} {d} {e} → ≾ᵉ-trans {c} {d} {e}
    ; ≾-irrelevant    = λ {c} {d} → ≾ᵉ-irrelevant {c} {d}
    ; _≡?_            = _≡ᵉ?_
    ; ≾-zero-productˡ = λ {c} {d} → ≾ᵉ-zero-productˡ {c} {d}
    ; ≾-zero-productʳ = λ {c} {d} → ≾ᵉ-zero-productʳ {c} {d}
    ; of-nat          = of-natᵉ
    ; of-nat-zero     = of-natᵉ-zero
    ; of-nat-plus     = λ {m} {n} → of-natᵉ-plus {m} {n}
    }

------------------------------------------------------------------------
-- Extending a morphism
--
-- Both adjoined points are absorbing, so `map-·` at the new point is
-- immediate and the extension is a morphism whenever the original is.

module AdjoinMap {M₁ M₂ : OrderedMonoid}
  (map₀ : OrderedMonoid.Carrier M₁ → OrderedMonoid.Carrier M₂)
  (map₀-monotone : {c d : OrderedMonoid.Carrier M₁}
                 → OrderedMonoid._≾_ M₁ c d
                 → OrderedMonoid._≾_ M₂ (map₀ c) (map₀ d))
  (map₀-u : map₀ (OrderedMonoid.u M₁) ≡ OrderedMonoid.u M₂)
  (map₀-· : {c d : OrderedMonoid.Carrier M₁}
          → map₀ (OrderedMonoid._·_ M₁ c d)
          ≡ OrderedMonoid._·_ M₂ (map₀ c) (map₀ d))
  (map₀-of-nat : {n : ℕ}
               → map₀ (OrderedMonoid.of-nat M₁ n) ≡ OrderedMonoid.of-nat M₂ n)
  where

  open Adjoin M₁ using () renaming (Ext to Ext₁; only_ to only₁_; ⊤ᵍ to ⊤ᵍ₁;
                                    withTop to withTop₁)
  open Adjoin M₂ using () renaming (Ext to Ext₂; only_ to only₂_; ⊤ᵍ to ⊤ᵍ₂;
                                    withTop to withTop₂)

  mapᵉ : Ext₁ → Ext₂
  mapᵉ (only₁ c) = only₂ (map₀ c)
  mapᵉ ⊤ᵍ₁       = ⊤ᵍ₂

  mapᵉ-monotone : {c d : Ext₁}
                → Grade._≾_ withTop₁ c d → Grade._≾_ withTop₂ (mapᵉ c) (mapᵉ d)
  mapᵉ-monotone {only₁ _} {only₁ _} p = map₀-monotone p
  mapᵉ-monotone {only₁ _} {⊤ᵍ₁}     p = tt
  mapᵉ-monotone {⊤ᵍ₁}     {only₁ _} ()
  mapᵉ-monotone {⊤ᵍ₁}     {⊤ᵍ₁}     p = tt

  mapᵉ-· : {c d : Ext₁}
         → mapᵉ (Grade._·_ withTop₁ c d)
         ≡ Grade._·_ withTop₂ (mapᵉ c) (mapᵉ d)
  mapᵉ-· {only₁ _} {only₁ _} = cong only₂_ map₀-·
  mapᵉ-· {only₁ _} {⊤ᵍ₁}     = refl
  mapᵉ-· {⊤ᵍ₁}     {only₁ _} = refl
  mapᵉ-· {⊤ᵍ₁}     {⊤ᵍ₁}     = refl

  withTopᵐ : withTop₁ →ᵍ withTop₂
  withTopᵐ = record
    { map          = mapᵉ
    ; map-monotone = λ {c} {d} → mapᵉ-monotone {c} {d}
    ; map-u        = cong only₂_ map₀-u
    ; map-·        = λ {c} {d} → mapᵉ-· {c} {d}
    ; map-of-nat   = λ {n} → cong only₂_ (map₀-of-nat {n})
    }
