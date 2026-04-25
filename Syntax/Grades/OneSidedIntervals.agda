--------------------------------------------
-- One-sided (closed) intervals as grades --
--------------------------------------------

open import Syntax.Grades

module Syntax.Grades.OneSidedIntervals (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core

-- interval addition

_·ₒ_ : ℕ → ℕ → ℕ
_·ₒ_ = _+_

infixl 7 _·ₒ_

-- interval order

_≾ₒ_ : Rel ℕ lzero
_≾ₒ_ = _≤_

-- cancellativity

·ₒ-≡-cancellative-aux : ∀ {m₁ m₂ m₃ m₄ m₅}
                       → m₁ + m₃ + m₂ ≡ m₄ + m₃ + m₅
                       → m₁ + m₂ ≡ m₄ + m₅
·ₒ-≡-cancellative-aux {m₁} {m₂} {m₃} {m₄} {m₅} eq =
  +-cancelˡ-≡ m₃ (m₁ + m₂) (m₄ + m₅)
    (begin
      m₃ + (m₁ + m₂)
    ≡⟨ sym (+-assoc m₃ m₁ m₂) ⟩
      (m₃ + m₁) + m₂
    ≡⟨ cong (_+ m₂) (+-comm m₃ m₁) ⟩
      (m₁ + m₃) + m₂
    ≡⟨ eq ⟩
      (m₄ + m₃) + m₅
    ≡⟨ cong (_+ m₅) (+-comm m₄ m₃) ⟩
      (m₃ + m₄) + m₅
    ≡⟨ +-assoc m₃ m₄ m₅ ⟩
      m₃ + (m₄ + m₅)
    ∎)

·ₒ-≾ₒ-cancellative-aux : ∀ {m₁ m₂ m₃ m₄ m₅}
                        → m₁ + m₃ + m₂ ≤ m₄ + m₃ + m₅
                        → m₁ + m₂ ≤ m₄ + m₅
·ₒ-≾ₒ-cancellative-aux {m₁} {m₂} {m₃} {m₄} {m₅} rel =
  +-cancelˡ-≤ m₃ (m₁ + m₂) (m₄ + m₅)
    (≤-trans
      (≤-reflexive (trans (sym (+-assoc m₃ m₁ m₂)) (cong (_+ m₂) (+-comm m₃ m₁))))
    (≤-trans
      rel
      (≤-reflexive (trans (cong (_+ m₅) (+-comm m₄ m₃)) (+-assoc m₃ m₄ m₅)))))

-- the grade of one-sided intervals

one-sided-intervals : Grade
one-sided-intervals = record
  { Carrier          = ℕ
  ; _·_              = _·ₒ_
  ; u                = 0
  ; ·-identityʳ      = +-identityʳ
  ; ·-identityˡ      = +-identityˡ
  ; ·-assoc          = +-assoc
  ; _≾_              = _≾ₒ_
  ; ·-monoʳ-≾        = λ {n} → +-monoʳ-≤ n
  ; ·-monoˡ-≾        = λ {n} → +-monoˡ-≤ n
  ; ≾-refl           = ≤-refl
  ; ≾-trans          = ≤-trans
  ; ≾-irrelevant     = ≤-irrelevant
  ; _≾?_             = _≤?_
  ; _≡?_             = _≟_
  ; ·-≡-cancellative = λ {c} {d} {e} {f} {g} eq
                         → ·ₒ-≡-cancellative-aux {c} {d} {e} {f} {g} eq
  ; ·-≾-cancellative = λ {c} {d} {e} {f} {g} rel
                         → ·ₒ-≾ₒ-cancellative-aux {c} {d} {e} {f} {g} rel
  ; ≡-zero-productˡ  = λ {c} eq  → m+n≡0⇒m≡0 c eq
  ; ≡-zero-productʳ  = λ {c} eq  → m+n≡0⇒n≡0 c eq
  ; ≾-zero-productˡ  = λ {c} rel → m+n≤o⇒m≤o c rel
  ; ≾-zero-productʳ  = λ {c} rel → m+n≤o⇒n≤o c rel
  ; of-nat           = λ n → n
  ; of-nat-zero      = refl
  ; of-nat-plus      = λ {m} {n} → refl
  }
