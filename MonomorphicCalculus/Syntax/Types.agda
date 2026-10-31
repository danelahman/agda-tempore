------------------------------------------------
-- Types of the monomorphic calculus          --
------------------------------------------------

open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Relation.Nullary

open import Language.BaseTypes
open import Grades.Base
open import Language.Spec

open import Util.Equality

module MonomorphicCalculus.Syntax.Types (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- Re-exported, so that `BaseType`, `_≡ᵇ?_`, `EternalBaseType`,
-- `eternalBaseType?` and `BaseConstants` come with the types.

open BaseTypes BTs public

-- Re-exported, so that `GType` and its constructors come with the types.

open import Language.GroundTypes Grades BTs public

-- Value and computation types

mutual

  data VType : Set  where
    Base  : BaseType → VType                 -- base types
    Unit  : VType                            -- unit type
    Bool  : VType                            -- boolean type
    Nat   : VType                            -- natural-number type
    _|×|_ : VType → VType → VType            -- product type
    _|+|_ : VType → VType → VType            -- sum type
    |List| : VType → VType                   -- list type
    Empty : VType                            -- empty type
    _⇒_   : VType → CType → VType            -- function type
    _⇛_   : CType → CType → VType            -- handler type
    [_]_  : R → VType → VType                -- box modality: values of type `[ ρ ] A`
                                             -- become available in at most `ρ` steps
  data CType : Set where
    _‼_ : VType → E → CType

  infix  37 [_]_
  infix  32 _|×|_ _|+|_
  infixr 30 _⇒_ _⇛_
  infix  31 _‼_

data Eternal : VType → Set where
  Baseₑ  : ∀ {b} → .(EternalBaseType b) → Eternal (Base b)
  Unitₑ  : Eternal Unit
  Boolₑ  : Eternal Bool
  Natₑ   : Eternal Nat
  _|×|ₑ_ : ∀ {A₁ A₂} → Eternal A₁ → Eternal A₂ → Eternal (A₁ |×| A₂)
  _|+|ₑ_ : ∀ {A₁ A₂} → Eternal A₁ → Eternal A₂ → Eternal (A₁ |+| A₂)
  |List|ₑ : ∀ {A} → Eternal A → Eternal (|List| A)
  Emptyₑ : Eternal Empty

-- Eternality is a property of a type: any two witnesses coincide
-- (the base-type witness is irrelevant).

eternal-irrelevant : ∀ {A} → (et et' : Eternal A) → et ≡ et'
eternal-irrelevant (Baseₑ p) (Baseₑ q) =
  refl
eternal-irrelevant Unitₑ Unitₑ =
  refl
eternal-irrelevant Boolₑ Boolₑ =
  refl
eternal-irrelevant Natₑ Natₑ =
  refl
eternal-irrelevant (et₁ |×|ₑ et₂) (et₁' |×|ₑ et₂') =
  cong₂ _|×|ₑ_ (eternal-irrelevant et₁ et₁') (eternal-irrelevant et₂ et₂')
eternal-irrelevant (et₁ |+|ₑ et₂) (et₁' |+|ₑ et₂') =
  cong₂ _|+|ₑ_ (eternal-irrelevant et₁ et₁') (eternal-irrelevant et₂ et₂')
eternal-irrelevant (|List|ₑ et) (|List|ₑ et') =
  cong |List|ₑ (eternal-irrelevant et et')
eternal-irrelevant Emptyₑ Emptyₑ =
  refl

-- Embedding ground types into types

type-of-gtype : GType → VType
type-of-gtype (Base B)   = Base B
type-of-gtype Unit       = Unit
type-of-gtype Bool       = Bool
type-of-gtype Nat        = Nat
type-of-gtype Empty      = Empty
type-of-gtype (A |×|ᵍ B) = type-of-gtype A |×| type-of-gtype B
type-of-gtype (A |+|ᵍ B) = type-of-gtype A |+| type-of-gtype B
type-of-gtype (|List|ᵍ A) = |List| (type-of-gtype A)
type-of-gtype ([ ρ ]ᵍ A) = [ ρ ] (type-of-gtype A)

-- Checking if a type is eternal is decidable

eternal? : (A : VType) → Dec (Eternal A)
eternal? (Base b) with eternalBaseType? b
... | yes p = yes (Baseₑ p)
... | no ¬p = no λ { (Baseₑ p') → ⊥-elim-irr (¬p p') }
eternal? Unit        = yes Unitₑ
eternal? Bool        = yes Boolₑ
eternal? Nat         = yes Natₑ
eternal? (A₁ |×| A₂) with eternal? A₁ | eternal? A₂
... | yes p | yes q = yes (p |×|ₑ q)
... | yes _ | no ¬q = no λ { (_ |×|ₑ x₂) → ¬q x₂}
... | no ¬p | _     = no λ { (x₁ |×|ₑ _) → ¬p x₁}
eternal? (A₁ |+| A₂) with eternal? A₁ | eternal? A₂
... | yes p | yes q = yes (p |+|ₑ q)
... | yes _ | no ¬q = no λ { (_ |+|ₑ x₂) → ¬q x₂}
... | no ¬p | _     = no λ { (x₁ |+|ₑ _) → ¬p x₁}
eternal? (|List| A)  with eternal? A
... | yes p = yes (|List|ₑ p)
... | no ¬p = no λ { (|List|ₑ x) → ¬p x }
eternal? Empty       = yes Emptyₑ
eternal? (_ ⇒ _)     = no λ ()
eternal? (_ ⇛ _)     = no λ ()
eternal? ([ _ ] _)   = no λ ()
