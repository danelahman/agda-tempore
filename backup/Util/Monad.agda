module Util.Monad where

open import Function.Base using (const; _∘_)

open import Syntax.Durations using (Duration)
open import Syntax.Grades

open import Util.Equality

-- A GRADED MONAD on `Set`, over a given grade monoid.
--
-- The monadic top-level operational semantics runs the external
-- implementations of the algebraic operations in such a monad. Its grade is
-- the time the implementation takes, so an operation's declared duration
-- `op-grade op` is not merely asserted by the reduction rule — it is the grade
-- of the runtime computation itself, and the two cannot disagree.
--
-- The grades form a preorder, so the monad carries a sub-effecting coercion,
-- functorial in the order, and the laws are stated up to it: the two sides of
-- each sit at equivalent grades.

record GradedMonad {D : Duration} (G : Grade D) : Set₁ where

  open Grade G

  infixl 20 _>>=_

  field
    T       : Carrier → Set → Set
    returnM : ∀ {A} → A → T u A
    _>>=_   : ∀ {ε ε' A B} → T ε A → (A → T ε' B) → T (ε · ε') B

    -- sub-effecting, functorial in the order
    subᵐ    : ∀ {ε ε' A} → ε ≾ ε' → T ε A → T ε' A
    subᵐ-refl  : ∀ {ε A} → (p : ε ≾ ε) → (t : T ε A) → subᵐ p t ≡ t
    subᵐ-trans : ∀ {ε ε' ε'' A} → (p : ε ≾ ε') → (q : ε' ≾ ε'') → (r : ε ≾ ε'')
               → (t : T ε A) → subᵐ q (subᵐ p t) ≡ subᵐ r t

    >>=-apply : ∀ {ε A B} → (a : A) → (F : A → T ε B)
              → (returnM a >>= F) ≡ subᵐ (≃⇒≿ (·-identityˡ ε)) (F a)

    >>=-id    : ∀ {ε A} → (ta : T ε A)
              → (ta >>= returnM) ≡ subᵐ (≃⇒≿ (·-identityʳ ε)) ta

    >>=-assoc : ∀ {ε ε' ε'' A B C}
              → (ta : T ε A)
              → (F : A → T ε' B)
              → (G : B → T ε'' C)
              → ((ta >>= F) >>= G)
              ≡ subᵐ (≃⇒≿ (·-assoc ε ε' ε'')) (ta >>= λ a → F a >>= G)
