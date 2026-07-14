---------------------------
-- Types of the language --
---------------------------

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
    _|×|_ : VType → VType → VType            -- product type
    Empty : VType                            -- empty type
    _⇒_   : VType → CType → VType            -- function type
    [_]_  : R → VType → VType                -- box modality: values of type `[ ρ ] A`
                                             -- become available in at most `ρ` steps
  data CType : Set where
    _‼_ : VType → E → CType

  infix  37 [_]_
  infix  32 _|×|_
  infixr 30 _⇒_
  infix  31 _‼_

data Eternal : VType → Set where
  Baseₑ  : (b : BaseType) → EternalBaseType b → Eternal (Base b)
  Unitₑ  : Eternal Unit
  _|×|ₑ_ : ∀ {A₁ A₂} → Eternal A₁ → Eternal A₂ → Eternal (A₁ |×| A₂)
  Emptyₑ : Eternal Empty

-- Eternality is a *property* of a type: any two witnesses coincide
-- (inherited from `eternalBaseType-irrelevant` at the base types).

eternal-irrelevant : ∀ {A} → (et et' : Eternal A) → et ≡ et'
eternal-irrelevant (Baseₑ b p) (Baseₑ .b q) =
  cong (Baseₑ b) (eternalBaseType-irrelevant p q)
eternal-irrelevant Unitₑ Unitₑ =
  refl
eternal-irrelevant (et₁ |×|ₑ et₂) (et₁' |×|ₑ et₂') =
  cong₂ _|×|ₑ_ (eternal-irrelevant et₁ et₁') (eternal-irrelevant et₂ et₂')
eternal-irrelevant Emptyₑ Emptyₑ =
  refl

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

-- (Value) types are decidable

_≡ᵥ?_ : Decidable (_≡_ {A = VType})
Base b ≡ᵥ? Base b' with b ≡ᵇ? b'
... | yes refl = yes refl
... | no ¬p = no (λ { refl → ¬p refl })
Base b ≡ᵥ? Unit = no (λ { () })
Base b ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
Base b ≡ᵥ? Empty = no (λ { () })
Base b ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
Base b ≡ᵥ? ([ ρ' ] B) = no (λ { () })
Unit ≡ᵥ? Base b' = no (λ { () })
Unit ≡ᵥ? Unit = yes refl
Unit ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
Unit ≡ᵥ? Empty = no (λ { () })
Unit ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
Unit ≡ᵥ? ([ ρ' ] B) = no (λ { () })
(A₁ |×| A₂) ≡ᵥ? Base b' = no (λ { () })
(A₁ |×| A₂) ≡ᵥ? Unit = no (λ { () })
(A₁ |×| A₂) ≡ᵥ? (B₁ |×| B₂) with A₁ ≡ᵥ? B₁ | A₂ ≡ᵥ? B₂
... | yes p | yes q = yes (cong₂ _|×|_ p q)
... | yes p | no ¬q = no (λ { refl → ¬q refl })
... | no ¬p | yes q = no (λ { refl → ¬p refl })
... | no ¬p | no ¬q = no λ { refl → ¬p refl }
(A₁ |×| A₂) ≡ᵥ? Empty = no (λ { () })
(A₁ |×| A₂) ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
(A₁ |×| A₂) ≡ᵥ? ([ ρ' ] B) = no (λ { () })
Empty ≡ᵥ? Base b' = no (λ { () })
Empty ≡ᵥ? Unit = no (λ { () })
Empty ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
Empty ≡ᵥ? Empty = yes refl
Empty ≡ᵥ? (B₁ ⇒ B₂) = no (λ { () })
Empty ≡ᵥ? ([ ρ' ] B) = no (λ { () })
(A₁ ⇒ A₂) ≡ᵥ? Base b' = no (λ { () })
(A₁ ⇒ A₂) ≡ᵥ? Unit = no (λ { () })
(A₁ ⇒ A₂) ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
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
([ ρ ] A) ≡ᵥ? (B₁ |×| B₂) = no (λ { () })
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
... | yes p = yes (Baseₑ b p)
... | no ¬p = no λ { (Baseₑ _ p') → ¬p p' }
eternal? Unit        = yes Unitₑ
eternal? (A₁ |×| A₂) with eternal? A₁ | eternal? A₂
... | yes p | yes q = yes (p |×|ₑ q)
... | yes _ | no ¬q = no λ { (_ |×|ₑ x₂) → ¬q x₂}
... | no ¬p | _     = no λ { (x₁ |×|ₑ _) → ¬p x₁}
eternal? Empty       = yes Emptyₑ
eternal? (_ ⇒ _)     = no λ ()
eternal? ([ _ ] _)   = no λ ()
