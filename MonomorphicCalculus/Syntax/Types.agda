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

-- The side condition of the variable rule, `Et(A) ∨ ρ ≾ 𝟏`: a variable bound
-- `ρ` ago is usable if its type is eternal or `ρ` is within the unit.

infix 4 _Et∨≾ᵘ_

data _Et∨≾ᵘ_ (A : VType) (ρ : R) : Set where
  et-ok : Et A → A Et∨≾ᵘ ρ
  ≾ᵘ-ok : ρ ≾ᵣ 𝟏ᵣ → A Et∨≾ᵘ ρ

-- The condition as a bound required of non-eternal types only, and back
-- through the decision on `Et`. The term formers keep the condition
-- irrelevant, so the bound is recovered through the decision on `_≾ᵣ_`.

Et∨≾ᵘ→¬Et⇒≾ : ∀ {A ρ} → .(A Et∨≾ᵘ ρ) → ¬ Et A → ρ ≾ᵣ 𝟏ᵣ
Et∨≾ᵘ→¬Et⇒≾ {ρ = ρ} ok ¬et = recompute (ρ ≾ᵣ? 𝟏ᵣ) (bound ok ¬et)
  where
  bound : ∀ {A ρ} → A Et∨≾ᵘ ρ → ¬ Et A → ρ ≾ᵣ 𝟏ᵣ
  bound (et-ok et) ¬et = ⊥-elim-irr (¬et et)
  bound (≾ᵘ-ok p)  ¬et = p

¬Et⇒≾→Et∨≾ᵘ : ∀ {A ρ} → (¬ Et A → ρ ≾ᵣ 𝟏ᵣ) → A Et∨≾ᵘ ρ
¬Et⇒≾→Et∨≾ᵘ {A} f with eternal? A
... | yes et = et-ok et
... | no ¬et = ≾ᵘ-ok (f ¬et)

-- Lowering the grade, where the lower grade is bounded unless the type is
-- eternal.

Et∨≾ᵘ-≾ : ∀ {A ρ ρ'} → (¬ Et A → ρ' ≾ᵣ ρ) → A Et∨≾ᵘ ρ → A Et∨≾ᵘ ρ'
Et∨≾ᵘ-≾ q (et-ok et) = et-ok et
Et∨≾ᵘ-≾ {A} q (≾ᵘ-ok p) with eternal? A
... | yes et = et-ok et
... | no ¬et = ≾ᵘ-ok (≾ᵣ-trans (q ¬et) p)

-- Leaving a lock: the grade before it is the left factor.

Et∨≾ᵘ-zero-productˡ : ∀ {A ρ ρ'} → A Et∨≾ᵘ (ρ ·ᵣ ρ') → A Et∨≾ᵘ ρ
Et∨≾ᵘ-zero-productˡ (et-ok et) = et-ok et
Et∨≾ᵘ-zero-productˡ (≾ᵘ-ok p)  = ≾ᵘ-ok (≾ᵣ-zero-productˡ p)
