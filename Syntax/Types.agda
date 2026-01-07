---------------------------
-- Types of the language --
---------------------------

open import Syntax.Grades

module Syntax.Types (Grades : GradeSystem) where

open GradeSystem Grades
open Grade EGrade renaming (Carrier to E)
open Grade RGrade renaming (Carrier to R)

open import Util.Equality
open import Util.Operations (Grades)

-- Value and computation types

mutual

  data VType : Set  where
    Base  : BaseType → VType                 -- base types
    Unit  : VType                            -- unit type
    _|×|_ : VType → VType → VType            -- product type
    Empty : VType                            -- empty type
    _⇒_   : VType → CType → VType            -- function type
    [_]_  : R → VType → VType                -- grade modality: values of type `[ ρ ] A`
                                             -- become available in at most `ρ` steps
  data CType : Set where
    _‼_ : VType → E → CType

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
type-of-gtype ([ ρ ]ᵍ A) = [ ρ ] (type-of-gtype A)

-- Type formation rules is injective

⇒-injective-dom : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B
⇒-injective-dom refl = refl

⇒-injective-cod : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → C ≡ D
⇒-injective-cod refl = refl

‼-injective-ty : ∀ {A B ε ε'} → (A ‼ ε) ≡ (B ‼ ε') → A ≡ B
‼-injective-ty refl = refl

‼-injective-egrade : ∀ {A B ε ε'} → (A ‼ ε) ≡ (B ‼ ε') → ε ≡ ε'
‼-injective-egrade refl = refl
