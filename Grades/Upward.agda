------------------------------------------------------------------------
-- The sub-grade of an upward-closed submonoid holding the durations. --
--                                                                    --
-- Let `P` be a property of the grades of `G` that is closed upward   --
-- (`c ≾ d` and `P c` give `P d`), holds of `u` and of every          --
-- `of-dur τ`, and is closed under `_·_`. Then the grades with a      --
-- witness of `P` form a grade `G ∣ P`:                               --
--                                                                    --
--   * `⊤` and `c ⊔ d` have `P`, being above a grade that has it;     --
--   * the order, and with it `≃`, is that of `G`, the witness being  --
--     data the order ignores;                                        --
--   * every law is inherited, and so is Kleene's plus, the closure   --
--     lying above the grade it closes.                               --
--                                                                    --
-- The inclusion `G ∣ P → G` is a grade morphism, preserving the      --
-- structure on the nose.                                             --
------------------------------------------------------------------------

module Grades.Upward where

open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Grades.Durations
open import Grades.Base

open import Util.Equality

------------------------------------------------------------------------
-- The conditions on the property

record Upward {D : Duration} (G : Grade D) (P : Grade.Carrier G → Set) : Set where
  open Grade G
  field
    up      : ∀ {c d} → c ≾ d → P c → P d
    P-u     : P u
    P-·     : ∀ {c d} → P c → P d → P (c · d)
    P-of-dur : ∀ τ → P (of-dur τ)

  P-⊤ : P ⊤
  P-⊤ = up (≾-⊤ u) P-u

  P-⊔ : ∀ {c d} → P c → P d → P (c ⊔ d)
  P-⊔ {c} {d} p _ = up (⊔-ubˡ c d) p

------------------------------------------------------------------------
-- The sub-grade

module _ {D : Duration} (G : Grade D) {P : Grade.Carrier G → Set} (U : Upward G P) where

  private
    module G = Grade G
    open Upward U

    C : Set
    C = Σ G.Carrier P

    _·ᴾ_ _⊔ᴾ_ : C → C → C
    (c , p) ·ᴾ (d , q) = c G.· d , P-· p q
    (c , p) ⊔ᴾ (d , q) = c G.⊔ d , P-⊔ p q

    _≾ᴾ_ : C → C → Set
    a ≾ᴾ b = proj₁ a G.≾ proj₁ b

    -- the closure of a grade with `P`
    plusᴾ : ∀ {c} (p : P c) → Plus G._·_ G._≾_ c → Plus _·ᴾ_ _≾ᴾ_ (c , p)
    plusᴾ p q =
      plus (Plus.c⁺ q , up (Plus.≾-c⁺ q) p) (Plus.≾-c⁺ q) (Plus.c⁺-iter q)
           (λ a b → Plus.c⁺-least q a b) (λ a → Plus.⁺-indˡ q a) (λ a → Plus.⁺-indʳ q a)

  infix 5 _∣ᵍ_

  _∣ᵍ_ : Grade D
  _∣ᵍ_ = record
    { Carrier         = C
    ; _·_             = _·ᴾ_
    ; u               = G.u , P-u
    ; _≾_             = _≾ᴾ_
    ; ⊤               = G.⊤ , P-⊤
    ; _⊔_             = _⊔ᴾ_
    ; of-dur          = λ τ → G.of-dur τ , P-of-dur τ
    ; ·-identityˡ     = λ a → G.·-identityˡ (proj₁ a)
    ; ·-identityʳ     = λ a → G.·-identityʳ (proj₁ a)
    ; ·-assoc         = λ a b c → G.·-assoc (proj₁ a) (proj₁ b) (proj₁ c)
    ; ≾-refl          = G.≾-refl
    ; ≾-trans         = G.≾-trans
    ; ≾-irrelevant    = G.≾-irrelevant
    ; _≾?_            = λ a b → proj₁ a G.≾? proj₁ b
    ; ≾-⊤             = λ a → G.≾-⊤ (proj₁ a)
    ; ⊔-ubˡ           = λ a b → G.⊔-ubˡ (proj₁ a) (proj₁ b)
    ; ⊔-ubʳ           = λ a b → G.⊔-ubʳ (proj₁ a) (proj₁ b)
    ; ⊔-lub           = G.⊔-lub
    ; ·-monoˡ-≾       = G.·-monoˡ-≾
    ; ·-monoʳ-≾       = G.·-monoʳ-≾
    ; ·-distribˡ-⊔-≾  = λ a b c → G.·-distribˡ-⊔-≾ (proj₁ a) (proj₁ b) (proj₁ c)
    ; ·-distribʳ-⊔-≾  = λ a b c → G.·-distribʳ-⊔-≾ (proj₁ a) (proj₁ b) (proj₁ c)
    ; ≾-zero-productˡ = G.≾-zero-productˡ
    ; ≾-zero-productʳ = G.≾-zero-productʳ
    ; of-dur-zero     = G.of-dur-zero
    ; of-dur-plus     = G.of-dur-plus
    ; ≃⇒≡?            = nothing
    ; u-least?        = Maybe.map (λ l a → l (proj₁ a)) G.u-least?
    ; ·-comm?         = Maybe.map (λ m a b → m (proj₁ a) (proj₁ b)) G.·-comm?
    ; plus?           = λ a → Maybe.map (plusᴾ (proj₂ a)) (G.plus? (proj₁ a))
    }

  -- the inclusion

  inclusionᵍ : _∣ᵍ_ →ᵍ G
  inclusionᵍ = record
    { map          = proj₁
    ; map-monotone = λ p → p
    ; map-u        = G.≃-refl
    ; map-·        = G.≃-refl
    ; map-⊤        = G.≃-refl
    ; map-⊔        = G.≃-refl
    ; map-of-dur   = G.≃-refl
    }
