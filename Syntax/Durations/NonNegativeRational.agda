----------------------------------------------------
-- The non-negative rationals as durations        --
----------------------------------------------------

module Syntax.Durations.NonNegativeRational where

open import Syntax.Durations
open import Syntax.Durations.Nat using (ℕᴰ)

open import Syntax.Grades.Example.Time.Dense.NonNegativeRational
  using (ℚ≥0; ⟨_⟩; val; nonneg; ≡-val; 0ᵈ; _+_; #_; #-+; +-identityˡ;
         +-identityʳ; +-assoc; +-comm; _≤_; *≤ᵈ*; _≤?_; ≤-refl; ≤-trans;
         ≤-antisym; ≤-irrelevant; p≤p+q)

open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Rational.Base as ℚ
import Data.Rational.Properties as ℚ
open import Relation.Nullary.Decidable.Core using (fromWitness)

open import Util.Equality

-- Dense time: a duration is a non-negative rational number of time units

ℚ≥0ᴰ : Duration
ℚ≥0ᴰ = record
  { Carrier      = ℚ≥0
  ; _+ᴰ_         = _+_
  ; 0ᴰ           = 0ᵈ
  ; +ᴰ-identityˡ = +-identityˡ
  ; +ᴰ-identityʳ = +-identityʳ
  ; +ᴰ-assoc     = +-assoc
  }

-- the inclusion of discrete time, `n` steps being `n` units

ℕ→ℚ≥0ᴰ : ℕᴰ →ᴰ ℚ≥0ᴰ
ℕ→ℚ≥0ᴰ = record
  { map   = #_
  ; map-0 = refl
  ; map-+ = λ {m} {n} → #-+ m n
  }


------------------------------------------------------------------------
-- The time domain

-- cancelling a summand of a rational sum

private
  -‿cancel : ∀ a b → (ℚ.- a) ℚ.+ (a ℚ.+ b) ≡ b
  -‿cancel a b =
    trans (sym (ℚ.+-assoc (ℚ.- a) a b))
          (trans (cong (ℚ._+ b) (ℚ.+-inverseˡ a)) (ℚ.+-identityˡ b))

  +-cancelˡ : ∀ p {q r} → p + q ≡ p + r → q ≡ r
  +-cancelˡ p {q} {r} e =
    ≡-val (trans (sym (-‿cancel (val p) (val q)))
                 (trans (cong (λ x → (ℚ.- val p) ℚ.+ val x) e)
                        (-‿cancel (val p) (val r))))

  -- the difference `q - p` above `p`

  diff : ∀ {p q} → p ≤ q → Σ ℚ≥0 (λ κ → p + κ ≡ q)
  diff {p} {q} (*≤ᵈ* p≤q) =
    ⟨ val q ℚ.- val p ⟩
      {fromWitness (subst (ℚ._≤ val q ℚ.- val p) (ℚ.+-inverseʳ (val p))
                          (ℚ.+-monoˡ-≤ (ℚ.- val p) p≤q))}
    , ≡-val (trans (cong (val p ℚ.+_) (ℚ.+-comm (val q) (ℚ.- val p)))
                   (trans (sym (ℚ.+-assoc (val p) (ℚ.- val p) (val q)))
                          (trans (cong (ℚ._+ val q) (ℚ.+-inverseʳ (val p)))
                                 (ℚ.+-identityˡ (val q)))))

  total : ∀ p q → p ≤ q ⊎ q ≤ p
  total p q with ℚ.≤-total (val p) (val q)
  ... | inj₁ r = inj₁ (*≤ᵈ* r)
  ... | inj₂ r = inj₂ (*≤ᵈ* r)

ℚ≥0ᵀ : TimeDomain ℚ≥0ᴰ
ℚ≥0ᵀ = record
  { +ᴰ-comm    = +-comm
  ; +ᴰ-cancelˡ = +-cancelˡ
  ; _≤ᴰ_       = _≤_
  ; _≤ᴰ?_      = _≤?_
  ; ≤ᴰ-refl    = ≤-refl
  ; ≤ᴰ-trans   = ≤-trans
  ; ≤ᴰ-antisym = ≤-antisym
  ; ≤ᴰ-total   = total
  ; ≤ᴰ-irrelevant = ≤-irrelevant
  ; ≤ᴰ-+       = p≤p+q
  ; diff       = diff
  }

-- it is dense: between two values lies a third

ℚ≥0-dense : Dense ℚ≥0ᵀ
ℚ≥0-dense {p} {q} q≰p with ℚ.<-dense (ℚ.≰⇒> (λ r → q≰p (*≤ᵈ* r)))
... | r , p<r , r<q =
  ⟨ r ⟩ {fromWitness (ℚ.≤-trans (nonneg p) (ℚ.<⇒≤ p<r))}
  , (λ { (*≤ᵈ* r≤p) → ℚ.<-irrefl refl (ℚ.<-≤-trans p<r r≤p) })
  , (λ { (*≤ᵈ* q≤r) → ℚ.<-irrefl refl (ℚ.<-≤-trans r<q q≤r) })
