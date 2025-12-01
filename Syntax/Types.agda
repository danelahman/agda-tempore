---------------------------
-- Types of the language --
---------------------------

module Syntax.Types where

open import Util.Equality
open import Util.Operations
open import Util.Time

-- Value and computation types

mutual

  data VType : Set where
    Base  : BaseType → VType                 -- base types
    Unit  : VType                            -- unit type
    _|×|_ : VType → VType → VType            -- product type
    Empty : VType                            -- empty type
    _⇒_   : VType → CType → VType            -- function type
    [_]_  : Time → VType → VType             -- temporal modality: values of type `[ t ] A`
                                             -- become available in at most `t` time steps
  data CType : Set where
    _‼_ : VType → Time → CType

  infix  37 [_]_
  infix  32 _|×|_
  infixr 30 _⇒_
  infix  31 _‼_

-- Embedding ground types into types

type-of-gtype : GType → VType
type-of-gtype (Base B)   = Base B
type-of-gtype Unit       = Unit
type-of-gtype Empty      = Empty
type-of-gtype (A |×|ᵍ B) = type-of-gtype A |×| type-of-gtype B
type-of-gtype ([ τ ]ᵍ A) = [ τ ] (type-of-gtype A)

-- Type formation rules is injective

⇒-injective-dom : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B
⇒-injective-dom refl = refl

⇒-injective-cod : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → C ≡ D
⇒-injective-cod refl = refl

‼-injective-ty : ∀ {A B τ τ'} → (A ‼ τ) ≡ (B ‼ τ') → A ≡ B
‼-injective-ty refl = refl

‼-injective-time : ∀ {A B τ τ'} → (A ‼ τ) ≡ (B ‼ τ') → τ ≡ τ'
‼-injective-time refl = refl
