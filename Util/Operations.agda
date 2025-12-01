------------------------------------------------------
-- Signature of operation symbols over ground types --
------------------------------------------------------

open import Util.Time

module Util.Operations where

-- Base types

postulate
  BaseType : Set

-- Set of (constant) elements for each base type

postulate
  BaseSet  : BaseType → Set

-- Ground types (for operation signatures)

data GType : Set where
  Base   : BaseType → GType                -- base types
  Unit   : GType                           -- unit type
  Empty  : GType                           -- empty type
  _|×|ᵍ_ : GType → GType → GType           -- product type
  [_]ᵍ_  : Time → GType → GType            -- temporal modality: values of type `[ t ] A`
                                           -- become available in at most `t` time steps
infix 38 _|×|ᵍ_
infix 37 [_]ᵍ_

-- Signature of (ground-typed) operation symbols

postulate
  Op       : Set                          -- set of operation symbols
  param    : Op → GType                   -- parameter type of each operation
  arity    : Op → GType                   -- arity type of each operation
  op-time  : Op → Time                    -- each operation's (maximal) time duration
