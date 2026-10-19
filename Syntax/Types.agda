---------------------------
-- Types of the language --
---------------------------

open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Relation.Binary.Definitions hiding (Empty)
open import Relation.Nullary

open import Syntax.BaseTypes
open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Types (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- Re-export the base types data so that downstream syntax and
-- semantics modules see `BaseType`, `_≡ᵇ?_`, `EternalBaseType`,
-- `eternalBaseType?`, and `BaseConstants` directly via `Syntax.Types`.

open BaseTypes BTs public

-- Re-export the ground types so that downstream syntax and
-- semantics modules see `GType` and its constructors directly
-- via `Syntax.Types`.

open import Syntax.GroundTypes Grades BTs public

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
    [_]_  : R → VType → VType                -- box modality: values of type `[ ρ ] A`
                                             -- become available in at most `ρ` steps
  data CType : Set where
    _‼_ : VType → E → CType

  infix  37 [_]_
  infix  32 _|×|_ _|+|_
  infixr 30 _⇒_
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

-- Eternality is a *property* of a type: any two witnesses coincide
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
type-of-gtype Empty      = Empty
type-of-gtype (A |×|ᵍ B) = type-of-gtype A |×| type-of-gtype B
type-of-gtype ([ ρ ]ᵍ A) = [ ρ ] (type-of-gtype A)

-- (Value) types are decidable, given decidable equality of the grades

module DecidableTypes (_≡ᵣ?_ : Decidable (_≡_ {A = R}))
                      (_≡ₑ?_ : Decidable (_≡_ {A = E})) where


  _≡ᵥ?_ : Decidable (_≡_ {A = VType})
  Base b ≡ᵥ? Base b' with b ≡ᵇ? b'
  ... | yes refl = yes refl
  ... | no ¬p = no (λ { refl → ¬p refl })
  Base b ≡ᵥ? Unit = no (λ { () })
  Base b ≡ᵥ? Bool = no (λ { () })
  Base b ≡ᵥ? Nat = no (λ { () })
  Base b ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  Base b ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  Base b ≡ᵥ? (|List| B₁) = no (λ { () })
  Base b ≡ᵥ? Empty = no (λ { () })
  Base b ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  Base b ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  Unit ≡ᵥ? Base b' = no (λ { () })
  Unit ≡ᵥ? Unit = yes refl
  Unit ≡ᵥ? Bool = no (λ { () })
  Unit ≡ᵥ? Nat = no (λ { () })
  Unit ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  Unit ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  Unit ≡ᵥ? (|List| B₁) = no (λ { () })
  Unit ≡ᵥ? Empty = no (λ { () })
  Unit ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  Unit ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  Bool ≡ᵥ? Base b' = no (λ { () })
  Bool ≡ᵥ? Unit = no (λ { () })
  Bool ≡ᵥ? Bool = yes refl
  Bool ≡ᵥ? Nat = no (λ { () })
  Bool ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  Bool ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  Bool ≡ᵥ? (|List| B₁) = no (λ { () })
  Bool ≡ᵥ? Empty = no (λ { () })
  Bool ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  Bool ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  Nat ≡ᵥ? Base b' = no (λ { () })
  Nat ≡ᵥ? Unit = no (λ { () })
  Nat ≡ᵥ? Bool = no (λ { () })
  Nat ≡ᵥ? Nat = yes refl
  Nat ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  Nat ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  Nat ≡ᵥ? (|List| B₁) = no (λ { () })
  Nat ≡ᵥ? Empty = no (λ { () })
  Nat ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  Nat ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? Base b' = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? Unit = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? Bool = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? Nat = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? (B₁ |×| B₂) with A₁ ≡ᵥ? B₁ | A₂ ≡ᵥ? B₂
  ... | yes p | yes q = yes (cong₂ _|×|_ p q)
  ... | yes p | no ¬q = no (λ { refl → ¬q refl })
  ... | no ¬p | yes q = no (λ { refl → ¬p refl })
  ... | no ¬p | no ¬q = no λ { refl → ¬p refl }
  (A₁ |×| A₂) ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? (|List| B₁) = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? Empty = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  (A₁ |×| A₂) ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? Base b' = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? Unit = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? Bool = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? Nat = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? (B₁ |+| B₂) with A₁ ≡ᵥ? B₁ | A₂ ≡ᵥ? B₂
  ... | yes p | yes q = yes (cong₂ _|+|_ p q)
  ... | yes p | no ¬q = no (λ { refl → ¬q refl })
  ... | no ¬p | yes q = no (λ { refl → ¬p refl })
  ... | no ¬p | no ¬q = no λ { refl → ¬p refl }
  (A₁ |+| A₂) ≡ᵥ? (|List| B₁) = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? Empty = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  (A₁ |+| A₂) ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  (|List| A₁) ≡ᵥ? Base b' = no (λ { () })
  (|List| A₁) ≡ᵥ? Unit = no (λ { () })
  (|List| A₁) ≡ᵥ? Bool = no (λ { () })
  (|List| A₁) ≡ᵥ? Nat = no (λ { () })
  (|List| A₁) ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  (|List| A₁) ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  (|List| A₁) ≡ᵥ? (|List| B₁) with A₁ ≡ᵥ? B₁
  ... | yes p = yes (cong |List| p)
  ... | no ¬p = no (λ { refl → ¬p refl })
  (|List| A₁) ≡ᵥ? Empty = no (λ { () })
  (|List| A₁) ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  (|List| A₁) ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  Empty ≡ᵥ? Base b' = no (λ { () })
  Empty ≡ᵥ? Unit = no (λ { () })
  Empty ≡ᵥ? Bool = no (λ { () })
  Empty ≡ᵥ? Nat = no (λ { () })
  Empty ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  Empty ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  Empty ≡ᵥ? (|List| B₁) = no (λ { () })
  Empty ≡ᵥ? Empty = yes refl
  Empty ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  Empty ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? Base b' = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? Unit = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? Bool = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? Nat = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? (|List| B₁) = no (λ { () })
  (A₁ ⇒ A₂) ≡ᵥ? Empty = no (λ { () })
  (A₁ ⇒ A₂ ‼ ε) ≡ᵥ? (B₁ ⇒ B₂ ‼ ε') with A₁ ≡ᵥ? B₁ | A₂ ≡ᵥ? B₂ | ε ≡ₑ? ε'
  ... | yes p | yes q | yes r = yes (cong₂ _⇒_ p (cong₂ _‼_ q r))
  ... | yes p | yes q | no ¬r = no (λ { refl → ¬r refl })
  ... | yes p | no ¬q | yes r = no (λ { refl → ¬q refl })
  ... | yes p | no ¬q | no ¬r = no (λ { refl → ¬q refl })
  ... | no ¬p | yes q | yes r = no (λ { refl → ¬p refl })
  ... | no ¬p | yes q | no ¬r = no (λ { refl → ¬p refl })
  ... | no ¬p | no ¬q | yes r = no (λ { refl → ¬p refl })
  ... | no ¬p | no ¬q | no ¬r = no (λ { refl → ¬p refl })
  (A₁ ⇒ A₂) ≡ᵥ? ([ ρ' ] B) = no (λ { () })
  ([ ρ ] A) ≡ᵥ? Base b' = no (λ { () })
  ([ ρ ] A) ≡ᵥ? Unit = no (λ { () })
  ([ ρ ] A) ≡ᵥ? Bool = no (λ { () })
  ([ ρ ] A) ≡ᵥ? Nat = no (λ { () })
  ([ ρ ] A) ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
  ([ ρ ] A) ≡ᵥ? (B₁ |+| B₂) = no (λ { () })
  ([ ρ ] A) ≡ᵥ? (|List| B₁) = no (λ { () })
  ([ ρ ] A) ≡ᵥ? Empty = no (λ { () })
  ([ ρ ] A) ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
  ([ ρ ] A) ≡ᵥ? ([ ρ' ] B) with A ≡ᵥ? B | ρ ≡ᵣ? ρ'
  ... | yes p | yes q = yes (cong₂ [_]_ q p)
  ... | yes p | no ¬q = no (λ { refl → ¬q refl })
  ... | no ¬p | yes q = no (λ { refl → ¬p refl })
  ... | no ¬p | no ¬q = no (λ { refl → ¬p refl })

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
eternal? ([ _ ] _)   = no λ ()
