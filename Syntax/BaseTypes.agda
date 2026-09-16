---------------------------------------------------------------
-- Signature of base types over which the language is built  --
---------------------------------------------------------------

module Syntax.BaseTypes where

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary

open import Util.Equality

-- Bundle of the data describing the base types: the set of
-- base types itself, decidable equality on base types, the
-- decidable predicate singling out the eternal base types,
-- and the set of constants for each base type. The predicate's
-- witnesses are used irrelevantly.

record BaseTypes : Set₁ where
  field
    BaseType         : Set
    _≡ᵇ?_            : Decidable (_≡_ {A = BaseType})

    EternalBaseType  : BaseType → Set
    eternalBaseType? : (b : BaseType) → Dec (EternalBaseType b)

    BaseConstants    : BaseType → Set
