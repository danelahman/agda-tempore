---------------------------------------------------------
-- Time for temporal effect annotations and presheaves --
---------------------------------------------------------

module Util.Time where

open import Data.Nat public
open import Data.Nat.Properties public

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Util.Equality

-- Time steps and annotations

Time : Set
Time = ℕ

-- Some auxiliary lemmas concerning ∸

n+m≤k⇒m≤k∸n : (n m k : Time) → n + m ≤ k → m ≤ k ∸ n
n+m≤k⇒m≤k∸n zero    m       k       p       = p
n+m≤k⇒m≤k∸n (suc n) zero    k       p       = z≤n
n+m≤k⇒m≤k∸n (suc n) (suc m) (suc k) (s≤s p) = n+m≤k⇒m≤k∸n n (suc m) k p


sucn≤m⇒m+k≤n-contradiction : ∀ {n m k} → suc n ≤ m → m + k ≤ n → ⊥
sucn≤m⇒m+k≤n-contradiction {suc n} {suc m} {zero} (s≤s p) (s≤s q) =
  ≤⇒≯ p (+-monoʳ-≤ 1 (≤-trans (≤-reflexive (sym (+-identityʳ m))) q))
sucn≤m⇒m+k≤n-contradiction {suc n} {suc m} {suc k} (s≤s p) (s≤s q) =
  ≤⇒≯ p (+-monoʳ-≤ 1 (m+n≤o⇒m≤o m q))


n∸m≤zero⇒n∸m≡0 : ∀ {n m} → n ∸ m ≤ zero → n ∸ m ≡ 0
n∸m≤zero⇒n∸m≡0 {.zero} {zero} z≤n = refl
n∸m≤zero⇒n∸m≡0 {zero} {suc m} p = refl
n∸m≤zero⇒n∸m≡0 {suc n} {suc m} p = n∸m≤zero⇒n∸m≡0 {n} {m} p


¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m : ∀ {n m k}
                       → ¬ (k ≤ m)
                       → k ∸ m ≤ n
                       → n + m ∸ k ≡ n ∸ (k ∸ m)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {zero} {zero} {zero} p q =
  refl
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {zero} {suc m} {zero} p q =
  ⊥-elim (p z≤n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {zero} {suc m} {suc k} p q =
  ⊥-elim (p (+-monoʳ-≤ 1 (m∸n≡0⇒m≤n (n∸m≤zero⇒n∸m≡0 {k} {m} q))))
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {zero} {zero} p q =
  ⊥-elim (p z≤n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {zero} {suc k} p q =
  cong (_∸ k) (+-identityʳ  n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {suc m} {zero} p q =
  ⊥-elim (p z≤n)
¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {suc m} {suc k} p q =
  trans
    (cong (_∸ k) (+-suc n m))
    (¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {suc n} {m} {k} (λ r → p (+-monoʳ-≤ 1 r)) q)


m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] : ∀ {n m k}
                         → m ≤ k
                         → ¬ (n + m ≤ k)
                         → n + m ∸ k ≡ n ∸ (k ∸ m)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {zero} {zero} {zero} p q =
  refl
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {zero} {zero} {suc k} p q =
  refl
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {zero} {suc m} {suc k} p q = 
  ⊥-elim (q p)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {zero} {zero} p q =
  cong suc (+-identityʳ _)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {zero} {suc k} p q = 
  cong (_∸ k) (+-identityʳ _)
m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {suc m} {suc k} (s≤s p) q =
  trans
    (cong (_∸ k) (trans (+-comm n (suc m)) (cong suc (+-comm m n))))
    (m≤k⇒¬n+m≤k⇒n+m∸k≡n∸[k∸m] {suc n} {m} {k} p
      (λ r → q (≤-trans (≤-reflexive (cong suc (+-comm n (suc m))))
        (≤-trans (≤-reflexive (cong suc (cong suc (+-comm m n)))) (+-monoʳ-≤ 1 r)))))

τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ : ∀ τ τ₁ τ₂ τ₃ → τ + (τ₁ + τ₂ + τ₃) ≡ τ + (τ₁ + (τ₂ + τ₃))
τ+⟨τ₁+τ₂+τ₃⟩≡τ+⟨τ₁+⟨τ₂+τ₃⟩⟩ τ τ₁ τ₂ τ₃ = 
    begin 
        τ + (τ₁ + τ₂ + τ₃) ≡⟨ cong (τ +_) (+-assoc τ₁ τ₂ τ₃) ⟩  
        τ + (τ₁ + (τ₂ + τ₃))
    ∎

τ-≤-substᵣ : ∀ {τ τ' τ''} → τ' ≡ τ'' → τ ≤ τ'' → τ ≤ τ'
τ-≤-substᵣ refl q = q

τ-≤-substₗ : ∀ {τ τ' τ''} → τ' ≡ τ'' → τ' ≤ τ → τ'' ≤ τ
τ-≤-substₗ refl p = p


step-time-eq : ∀ τ τ₁ τ' τ'' τ''' → (q : τ + τ₁ ≡ τ'' + τ''') → τ + (τ₁ + τ') ≡ τ'' + (τ''' + τ')
step-time-eq τ τ₁ τ' τ'' τ''' q = 
    begin 
        τ + (τ₁ + τ') ≡⟨ sym (+-assoc τ τ₁ τ') ⟩
        (τ + τ₁) + τ' ≡⟨ cong (_+ τ') q ⟩
        (τ'' + τ''') + τ' ≡⟨ +-assoc τ'' τ''' τ' ⟩
        τ'' + (τ''' + τ')
    ∎

m≡n⇒m≤n : ∀ {m n} → m ≡ n → m ≤ n
m≡n⇒m≤n {zero} {n} p = z≤n
m≡n⇒m≤n {suc m} {suc n} p = s≤s (m≡n⇒m≤n (suc-injective p))

m≤n+k⇒m∸k≤n : ∀ m n k → m ≤ n + k → m ∸ k ≤ n
m≤n+k⇒m∸k≤n m n zero p = τ-≤-substᵣ (sym (+-identityʳ n)) p
m≤n+k⇒m∸k≤n zero n (suc k) p = z≤n
m≤n+k⇒m∸k≤n (suc m) zero (suc k) (s≤s p) = τ-≤-substₗ (sym (m≤n⇒m∸n≡0 p)) ≤-refl
m≤n+k⇒m∸k≤n (suc m) (suc n) (suc k) (s≤s p) = 
    m≤n+k⇒m∸k≤n m (suc n) k (τ-≤-substᵣ (sym (+-suc n k)) p)

τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] : ∀ τ τ₁ τ₂ τ₃ τ₄
            → τ + τ₂ ≡ τ₁ + τ₄ 
            → τ + (τ₂ + τ₃) ≡ τ₁ + (τ₄ + τ₃)
τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] τ τ₁ τ₂ τ₃ τ₄ p = 
    begin 
        τ + (τ₂ + τ₃) ≡⟨ sym (+-assoc τ τ₂ τ₃) ⟩
        τ + τ₂ + τ₃ ≡⟨ cong (_+ τ₃) p ⟩
        τ₁ + τ₄ + τ₃ ≡⟨ +-assoc τ₁ τ₄ τ₃ ⟩
        τ₁ + (τ₄ + τ₃) 
    ∎
