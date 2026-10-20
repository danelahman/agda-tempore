------------------------------------------------------------------------
-- The non-negative rationals are commensurable.                      --
--                                                                    --
-- For a list of durations, the unit is one over the least common    --
-- multiple `D` of their denominators, and the count of `n / d` (in   --
-- lowest terms) is `n · (D / d)`. Both are computed by ℕ arithmetic, --
-- so on literals they normalise to numerals.                         --
------------------------------------------------------------------------

module Syntax.Grades.Exact.Grid.NonNegativeRational where

open import Data.Empty using (⊥-elim)
open import Data.Integer.Base as ℤ using (+_; -[1+_])
import Data.Integer.Properties as ℤ
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Nat.Coprimality using (1-coprimeTo)
open import Data.Nat.DivMod using (m/n*n≡m; n/n≡1)
open import Data.Nat.Divisibility using (_∣_; ∣-trans; m∣m*n; n∣m*n)
open import Data.Nat.LCM using (lcm; m∣lcm[m,n]; n∣lcm[m,n]; gcd*lcm)
open import Data.Nat.GCD using (gcd)
open import Data.Rational.Base as ℚ using (ℚ; mkℚ; normalize; ↥_; ↧ₙ_; 0ℚ)
import Data.Rational.Properties as ℚ
open import Data.Rational.Unnormalised.Base using (mkℚᵘ; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘ

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᵀ)
open import Syntax.Grades.Example.Time.Dense.NonNegativeRational
  using (ℚ≥0; val; nonneg; ≡-val; _/_; *≤ᵈ*)
open import Syntax.Grades.Exact.Grid ℚ≥0ᵀ using (Unit; Commensurable; _×ᴰ_)

------------------------------------------------------------------------
-- Fractions of naturals

private
  -- fractions with cross-multiplied numerators equal are equal

  /-≃ : ∀ a b c d .{{_ : ℕ.NonZero c}} .{{_ : ℕ.NonZero d}} →
        a ℕ.* d ≡ b ℕ.* c → normalize a c ≡ normalize b d
  /-≃ a b (suc c) (suc d) e =
    ℚ.fromℚᵘ-cong {mkℚᵘ (+ a) c} {mkℚᵘ (+ b) d} (*≡* (trans (sym (ℤ.pos-* a (suc d)))
                        (trans (cong +_ e) (ℤ.pos-* b (suc c)))))

  -- fractions over one denominator add as their numerators do

  /-+ : ∀ a b d .{{_ : ℕ.NonZero d}} →
        normalize a d ℚ.+ normalize b d ≡ normalize (a ℕ.+ b) d
  /-+ a b D@(suc d) =
    trans (sym (ℚ.fromℚᵘ-toℚᵘ _))
      (ℚ.fromℚᵘ-cong {y = mkℚᵘ (+ (a ℕ.+ b)) d}
        (ℚᵘ.≃-trans (ℚ.toℚᵘ-homo-+ (normalize a D) (normalize b D))
          (ℚᵘ.≃-trans (ℚᵘ.+-cong (ℚ.toℚᵘ-fromℚᵘ (mkℚᵘ (+ a) d))
                                  (ℚ.toℚᵘ-fromℚᵘ (mkℚᵘ (+ b) d)))
            (*≡* (trans (cong (ℤ._* + D)
                          (trans (cong₂ ℤ._+_ (sym (ℤ.pos-* a D)) (sym (ℤ.pos-* b D)))
                                 (sym (ℤ.pos-+ (a ℕ.* D) (b ℕ.* D)))))
                   (trans (sym (ℤ.pos-* (a ℕ.* D ℕ.+ b ℕ.* D) D))
                     (trans (cong +_ eq) (ℤ.pos-* (a ℕ.+ b) (D ℕ.* D)))))))))
    where
      eq : (a ℕ.* D ℕ.+ b ℕ.* D) ℕ.* D ≡ (a ℕ.+ b) ℕ.* (D ℕ.* D)
      eq = trans (cong (ℕ._* D) (sym (ℕ.*-distribʳ-+ D a b))) (ℕ.*-assoc (a ℕ.+ b) D D)

  -- `k` copies of `1 / d` are `k / d`

  ×-/ : ∀ k d .{{_ : ℕ.NonZero d}} → val (k ×ᴰ (1 / d)) ≡ normalize k d
  ×-/ zero    d = /-≃ 0 0 1 d refl
  ×-/ (suc k) d = trans (cong (normalize 1 d ℚ.+_) (×-/ k d)) (/-+ 1 k d)

  -- a non-negative rational is its numeral numerator over its denominator

  ∣↥∣/↧ : ∀ p → 0ℚ ℚ.≤ p → normalize ℤ.∣ ↥ p ∣ (↧ₙ p) ≡ p
  ∣↥∣/↧ (mkℚ (+ n)    d c) _ = ℚ.normalize-coprime c
  ∣↥∣/↧ (mkℚ -[1+ n ] d c) h = ⊥-elim (ℚ.<-irrefl refl (ℚ.<-≤-trans (ℚ.negative⁻¹ (mkℚ -[1+ n ] d c)) h))

------------------------------------------------------------------------
-- The unit of a list

private
  -- the least common multiple of the denominators

  den : List ℚ≥0 → ℕ
  den []       = 1
  den (q ∷ qs) = lcm (↧ₙ val q) (den qs)

  den-nz : ∀ xs → ℕ.NonZero (den xs)
  den-nz []       = _
  den-nz (q ∷ qs) = ℕ.≢-nonZero λ e →
    ℕ.≢-nonZero⁻¹ ((↧ₙ val q) ℕ.* den qs) {{ℕ.m*n≢0 (↧ₙ val q) (den qs) {{_}} {{den-nz qs}}}}
      (trans (sym (gcd*lcm (↧ₙ val q) (den qs)))
             (trans (cong (gcd (↧ₙ val q) (den qs) ℕ.*_) e) (ℕ.*-zeroʳ (gcd (↧ₙ val q) (den qs)))))

  den-∣ : ∀ {q xs} → q ∈ xs → ↧ₙ val q ∣ den xs
  den-∣ {xs = q ∷ qs}  (here refl) = m∣lcm[m,n] (↧ₙ val q) (den qs)
  den-∣ {xs = q′ ∷ qs} (there p)   = ∣-trans (den-∣ p) (n∣lcm[m,n] (↧ₙ val q′) (den qs))

  cnt : (D : ℕ) → ℚ≥0 → ℕ
  cnt D q = ℤ.∣ ↥ val q ∣ ℕ.* (D ℕ./ ↧ₙ val q)

  cnt-δ : ∀ D .{{_ : ℕ.NonZero D}} → cnt D (1 / D) ≡ 1
  cnt-δ D@(suc d) =
    trans (cong (λ p → ℤ.∣ ↥ p ∣ ℕ.* (D ℕ./ ↧ₙ p)) (ℚ.normalize-coprime (1-coprimeTo D)))
          (trans (ℕ.*-identityˡ (D ℕ./ D)) (n/n≡1 D))

  cnt-× : ∀ D .{{_ : ℕ.NonZero D}} {q} → ↧ₙ val q ∣ D → cnt D q ×ᴰ (1 / D) ≡ q
  cnt-× D {q} d∣D = ≡-val
    (trans (×-/ (cnt D q) D)
      (trans (/-≃ (cnt D q) n D d
               (trans (ℕ.*-assoc n (D ℕ./ d) d)
                 (cong (n ℕ.*_) (m/n*n≡m d∣D))))
             (∣↥∣/↧ (val q) (nonneg q))))
    where
      n = ℤ.∣ ↥ val q ∣
      d = ↧ₙ val q

ℚ≥0-commensurable : Commensurable
ℚ≥0-commensurable xs = record
  { δ       = 1 / D
  ; δ-pos   = λ { (*≤ᵈ* r) → ℚ.<-irrefl refl (ℚ.<-≤-trans (ℚ.positive⁻¹ _ {{ℚ.normalize-pos 1 D}}) r) }
  ; count   = cnt D
  ; count-δ = cnt-δ D
  ; counts  = λ q∈xs → cnt-× D (den-∣ q∈xs)
  }
  where
    D = den xs
    instance
      _ : ℕ.NonZero D
      _ = den-nz xs

------------------------------------------------------------------------
-- The unit and counts compute

private
  _ : Unit.count (ℚ≥0-commensurable (1 / 2 ∷ 3 / 4 ∷ [])) (3 / 4) ≡ 3
  _ = refl

  _ : Unit.δ (ℚ≥0-commensurable (1 / 2 ∷ 3 / 4 ∷ [])) ≡ 1 / 4
  _ = refl
