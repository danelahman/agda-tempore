module Util.Monad where

open import Function.Base using (const; _∘_)

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
-- The laws are stated up to a transport along the grade monoid's laws, since
-- the two sides sit at grades that are equal but not definitionally so.

record GradedMonad (G : Grade) : Set₁ where

  open Grade G

  infixl 20 _>>=_

  field
    T       : Carrier → Set → Set
    returnM : ∀ {A} → A → T u A
    _>>=_   : ∀ {ε ε' A B} → T ε A → (A → T ε' B) → T (ε · ε') B

  -- transport along an equality of grades

  ε-substᵐ : ∀ {A} {ε ε' : Carrier} → ε ≡ ε' → T ε A → T ε' A
  ε-substᵐ e t = subst (λ ε → T ε _) e t

  field
    >>=-apply : ∀ {ε A B} → (a : A) → (F : A → T ε B)
              → (returnM a >>= F) ≡ ε-substᵐ (sym (·-identityˡ ε)) (F a)

    >>=-id    : ∀ {ε A} → (ta : T ε A)
              → (ta >>= returnM) ≡ ε-substᵐ (sym (·-identityʳ ε)) ta

    >>=-assoc : ∀ {ε ε' ε'' A B C}
              → (ta : T ε A)
              → (F : A → T ε' B)
              → (G : B → T ε'' C)
              → ((ta >>= F) >>= G)
              ≡ ε-substᵐ (sym (·-assoc ε ε' ε'')) (ta >>= λ a → F a >>= G)
