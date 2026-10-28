---------------------------------------------------------------
-- Signature of base types over which the language is built  --
---------------------------------------------------------------

module Language.BaseTypes where

open import Relation.Binary.Definitions using (Decidable; Tri; tri<; tri≈; tri>)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary

open import Language.Comparisons using (Order; less; equal; greater)

open import Util.Equality

-- The outcome a trichotomy names

order-of : ∀ {X Y Z : Set} → Tri X Y Z → Order
order-of (tri< _ _ _) = less
order-of (tri≈ _ _ _) = equal
order-of (tri> _ _ _) = greater

-- Bundle of the data describing the base types: the set of
-- base types itself, decidable equality on base types, the
-- decidable predicate singling out the eternal base types,
-- the set of constants for each base type, and an order on them,
-- strict and total at the eternal base types. The predicate's
-- witnesses are used irrelevantly.

record BaseTypes : Set₁ where
  field
    BaseType         : Set
    _≡ᵇ?_            : Decidable (_≡_ {A = BaseType})

    EternalBaseType  : BaseType → Set
    eternalBaseType? : (b : BaseType) → Dec (EternalBaseType b)

    BaseConstants    : BaseType → Set

    -- the order on constants, a strict total order at eternal base types
    _≺ᵇ_                  : ∀ {b} → BaseConstants b → BaseConstants b → Set
    ≺ᵇ-isStrictTotalOrder : ∀ {b} → .(EternalBaseType b)
                          → IsStrictTotalOrder _≡_ (_≺ᵇ_ {b})

  -- the three-way comparison of two constants of an eternal base type

  compareᵇ : ∀ {b} → .(EternalBaseType b) → BaseConstants b → BaseConstants b → Order
  compareᵇ eb c c' = order-of (IsStrictTotalOrder.compare (≺ᵇ-isStrictTotalOrder eb) c c')
