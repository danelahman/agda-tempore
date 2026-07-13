---------------------------------------------------------------
-- Signature of base types over which the language is built  --
---------------------------------------------------------------

module Syntax.BaseTypes where

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary

open import Util.Equality

-- Bundle of the data describing the base types: the set of
-- base types itself, decidable equality on base types, the
-- predicate distinguishing eternal base types together with
-- its decision procedure, and the set of constants for each
-- base type.

record BaseTypes : Set₁ where
  field
    BaseType         : Set
    _≡ᵇ?_            : Decidable (_≡_ {A = BaseType})
    
    EternalBaseType  : BaseType → Set
    eternalBaseType? : (b : BaseType) → Dec (EternalBaseType b)

    -- Being an eternal base type is a *property*, not structure: it is
    -- evidence that a base type is eternal, and any two such witnesses
    -- coincide. This is what makes the interpretation of a variable of
    -- eternal type independent of how its eternality was established.
    eternalBaseType-irrelevant : ∀ {b} → (p q : EternalBaseType b) → p ≡ q

    BaseConstants    : BaseType → Set
