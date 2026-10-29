------------------------------------------------------------------------
-- The durations of a time domain as a commutative monoid, and the    --
-- standard library's solver for equations between sums of them.      --
------------------------------------------------------------------------

open import Grades.Durations

module Grades.Durations.Solver {D : Duration} (T : TimeDomain D) where

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂; isEquivalence)

open Duration D
open TimeDomain T

+ᴰ-commutativeMonoid : CommutativeMonoid _ _
+ᴰ-commutativeMonoid = record
  { Carrier = Carrier ; _≈_ = _≡_ ; _∙_ = _+ᴰ_ ; ε = 0ᴰ
  ; isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _+ᴰ_ }
        ; assoc = +ᴰ-assoc }
      ; identity = +ᴰ-identityˡ , +ᴰ-identityʳ }
    ; comm = +ᴰ-comm } }

-- `solve n (λ x y … → lhs ⊜ rhs) refl`, sums written with `_⊕_`

open import Algebra.Solver.CommutativeMonoid +ᴰ-commutativeMonoid public
  using (solve; _⊜_; _⊕_)
