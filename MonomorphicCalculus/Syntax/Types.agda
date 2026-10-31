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
    unit  : VType                            -- unit type
    bool  : VType                            -- boolean type
    nat   : VType                            -- natural-number type
    _|×|_ : VType → VType → VType            -- product type
    _|+|_ : VType → VType → VType            -- sum type
    list  : VType → VType                    -- list type
    empty : VType                            -- empty type
    _⇒_   : VType → CType → VType            -- function type
    _⇛_   : CType → CType → VType            -- handler type
    [_]_  : R → VType → VType                -- box modality: values of type `[ ρ ] A`
                                             -- become available in at most `ρ` steps
  data CType : Set where
    _!_ : VType → E → CType

  infix  37 [_]_
  infix  32 _|×|_ _|+|_
  infixr 30 _⇒_ _⇛_
  infix  31 _!_

data Et : VType → Set where
  Baseₑ  : ∀ {b} → .(EternalBaseType b) → Et (Base b)
  unitₑ  : Et unit
  boolₑ  : Et bool
  natₑ   : Et nat
  _|×|ₑ_ : ∀ {A₁ A₂} → Et A₁ → Et A₂ → Et (A₁ |×| A₂)
  _|+|ₑ_ : ∀ {A₁ A₂} → Et A₁ → Et A₂ → Et (A₁ |+| A₂)
  listₑ  : ∀ {A} → Et A → Et (list A)
  emptyₑ : Et empty

-- Eternality is a property of a type: any two witnesses coincide
-- (the base-type witness is irrelevant).

eternal-irrelevant : ∀ {A} → (et et' : Et A) → et ≡ et'
eternal-irrelevant (Baseₑ p) (Baseₑ q) =
  refl
eternal-irrelevant unitₑ unitₑ =
  refl
eternal-irrelevant boolₑ boolₑ =
  refl
eternal-irrelevant natₑ natₑ =
  refl
eternal-irrelevant (et₁ |×|ₑ et₂) (et₁' |×|ₑ et₂') =
  cong₂ _|×|ₑ_ (eternal-irrelevant et₁ et₁') (eternal-irrelevant et₂ et₂')
eternal-irrelevant (et₁ |+|ₑ et₂) (et₁' |+|ₑ et₂') =
  cong₂ _|+|ₑ_ (eternal-irrelevant et₁ et₁') (eternal-irrelevant et₂ et₂')
eternal-irrelevant (listₑ et) (listₑ et') =
  cong listₑ (eternal-irrelevant et et')
eternal-irrelevant emptyₑ emptyₑ =
  refl

-- Embedding ground types into types

⌜_⌝ᵍ : GType → VType
⌜ Base B ⌝ᵍ    = Base B
⌜ unit ⌝ᵍ      = unit
⌜ bool ⌝ᵍ      = bool
⌜ nat ⌝ᵍ       = nat
⌜ empty ⌝ᵍ     = empty
⌜ A |×|ᵍ B ⌝ᵍ  = ⌜ A ⌝ᵍ |×| ⌜ B ⌝ᵍ
⌜ A |+|ᵍ B ⌝ᵍ  = ⌜ A ⌝ᵍ |+| ⌜ B ⌝ᵍ
⌜ listᵍ A ⌝ᵍ   = list ⌜ A ⌝ᵍ
⌜ [ ρ ]ᵍ A ⌝ᵍ  = [ ρ ] ⌜ A ⌝ᵍ

-- Checking if a type is eternal is decidable

eternal? : (A : VType) → Dec (Et A)
eternal? (Base b) with eternalBaseType? b
... | yes p = yes (Baseₑ p)
... | no ¬p = no λ { (Baseₑ p') → ⊥-elim-irr (¬p p') }
eternal? unit        = yes unitₑ
eternal? bool        = yes boolₑ
eternal? nat         = yes natₑ
eternal? (A₁ |×| A₂) with eternal? A₁ | eternal? A₂
... | yes p | yes q = yes (p |×|ₑ q)
... | yes _ | no ¬q = no λ { (_ |×|ₑ x₂) → ¬q x₂}
... | no ¬p | _     = no λ { (x₁ |×|ₑ _) → ¬p x₁}
eternal? (A₁ |+| A₂) with eternal? A₁ | eternal? A₂
... | yes p | yes q = yes (p |+|ₑ q)
... | yes _ | no ¬q = no λ { (_ |+|ₑ x₂) → ¬q x₂}
... | no ¬p | _     = no λ { (x₁ |+|ₑ _) → ¬p x₁}
eternal? (list A)    with eternal? A
... | yes p = yes (listₑ p)
... | no ¬p = no λ { (listₑ x) → ¬p x }
eternal? empty       = yes emptyₑ
eternal? (_ ⇒ _)     = no λ ()
eternal? (_ ⇛ _)     = no λ ()
eternal? ([ _ ] _)   = no λ ()
