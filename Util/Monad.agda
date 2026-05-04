module Util.Monad where

open import Function.Base using (const; _∘_)

open import Util.Equality

private
  variable
    A B C : Set

record Monad : Set₁ where
  field
    T       : Set → Set
    _>>=_   : ∀ {A B} → T A → (A → T B) → T B
    returnM : ∀ {A} → A → T A

  kleisliExt : ∀ {A B} → (A → T B) → T A → T B
  kleisliExt F = λ ta → ta >>= F

  field
    >>=-id    : ∀ {A} → (ta : T A) → (kleisliExt returnM) ta ≡ ta
    
    >>=-apply : ∀ {A B} → (a : A) → (F : A → T B) → (returnM a >>= F) ≡ F a

    >>=-assoc : ∀ {A B C}
              → (ta : T A)
              → (F : A → T B)
              → (G : B → T C)
              → ((ta >>= F) >>= G) ≡ (ta >>= λ a → F a >>= G)
