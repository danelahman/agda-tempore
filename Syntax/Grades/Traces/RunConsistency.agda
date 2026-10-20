------------------------------------------------------------------------
-- Run consistency: a guarantee and an allowance with a common run.    --
--                                                                     --
-- A guarantee `p` (read in `Traces.Coverage`, at `costˡᵒ`) and an     --
-- allowance `q` (read in `Traces.Allowance`, at `costʰⁱ`) are         --
-- consistent when some run covers the one and stays within the other: --
--                                                                     --
--   ∃ x. p ≼ᶜ x × x ≼ᵃ q                                              --
--                                                                     --
-- `p ⋈[ k , b ] q` is that statement with the run eliminated: it      --
-- walks the guarantee and the allowance together, carrying the        --
-- coverage slack `k` and the allowance budget `b` the run would have  --
-- banked. Its rules are the pairs of rules of the two orders that     --
-- agree on the run's head, read off the guarantee and the allowance:  --
--                                                                     --
--   * `bank`, `skip`  the allowance moves on its own;                 --
--   * `spend`         a delay of the guarantee is paid out of slack,  --
--                     topped up from the budget by a delay of the run --
--                     (a run's delay is slack and expense at once);   --
--   * `match`         an operation both name;                         --
--   * `pay`           an operation of the guarantee, paid out of the  --
--                     budget;                                         --
--   * `fill`          an operation of the allowance the guarantee     --
--                     does not name, banked as slack, the budget      --
--                     having been turned into slack before it lapses. --
--                                                                     --
-- It is sound and complete for the existential (`sound`, `complete`): --
-- the completeness proof rests on `mono`, which says that budget is   --
-- worth at least as much as slack. Every rule shrinks the guarantee   --
-- or the allowance, so it is decided by exhaustive search.            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; s≤s)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_; _⊎-dec_)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Traces.RunConsistency
  {D : Duration} (T : TimeDomain D) (Op : Set)
  (costˡᵒ costʰⁱ : Op → Duration.Carrier D)
  (cost-≤ : (o : Op) → TimeDomain._≤ᴰ_ T (costˡᵒ o) (costʰⁱ o)) where

open import Syntax.Durations.Monus T as M
  using (Carrier; 0ᴰ; _<ᴰ_; _<ᴰ?_; compare; tri<; tri≈; tri>; <⇒≤; ≮0⇒≡0)
open M.Notation

open import Syntax.Grades.Traces.Base T Op
open import Syntax.Grades.Traces.Slack T Op using (size; size⁻; size-inj⁻)

import Syntax.Grades.Traces.Coverage.Core T Op costˡᵒ as C
import Syntax.Grades.Traces.Coverage.Moves T Op costˡᵒ as CM
import Syntax.Grades.Traces.Allowance.Core T Op costʰⁱ as A
import Syntax.Grades.Traces.Allowance.Moves T Op costʰⁱ as AM

open C using (_≼ᶜ[_]_; _≼ᶜ_)
open A using (_≼ᵃ[_]_; _≼ᵃ_)

------------------------------------------------------------------------
-- The statement

Consistent : Trace → Trace → Set
Consistent p q = Σ Trace (λ x → p ≼ᶜ x × x ≼ᵃ q)

------------------------------------------------------------------------
-- The joint relation

infix 4 _⋈[_,_]_

data _⋈[_,_]_ : Trace → Carrier → Carrier → Trace → Set where

  -- the empty guarantee is met by the empty run
  done  : ∀ {k b q}
        → ε ⋈[ k , b ] q

  -- a delay of the allowance is banked as budget
  bank  : ∀ {k b p e q⁻}
        → p ⋈[ k , b + ∣ e ∣⁺ ] inj⁻ q⁻
        → p ⋈[ k , b ] delay e q⁻

  -- an operation of the allowance is skipped
  skip  : ∀ {k b p o q}
        → p ⋈[ k , b ] q
        → p ⋈[ k , b ] operation o q

  -- or performed as filler: the budget becomes slack, then lapses
  fill  : ∀ {k b p o q}
        → p ⋈[ (k + b) + costˡᵒ o , 0ᴰ ] q
        → p ⋈[ k , b ] operation o q

  -- a delay of the guarantee is paid out of slack, topped up by budget
  spend : ∀ {k b d p⁻ q}
        → ∣ d ∣⁺ ≤ k + b
        → inj⁻ p⁻ ⋈[ k ∸ ∣ d ∣⁺ , b ∸ (∣ d ∣⁺ ∸ k) ] q
        → delay d p⁻ ⋈[ k , b ] q

  -- an operation both name; neither slack nor budget crosses it
  match : ∀ {k b o p q}
        → p ⋈[ 0ᴰ , 0ᴰ ] q
        → operation o p ⋈[ k , b ] operation o q

  -- an operation of the guarantee, paid out of the budget
  pay   : ∀ {k b o p q}
        → costʰⁱ o ≤ b
        → p ⋈[ 0ᴰ , b ∸ costʰⁱ o ] q
        → operation o p ⋈[ k , b ] q

------------------------------------------------------------------------
-- Arithmetic

private

  ≰⇒≥ : {d k : Carrier} → ¬ (d ≤ k) → k ≤ d
  ≰⇒≥ {d} {k} ¬le with compare k d
  ... | tri< lt = <⇒≤ lt
  ... | tri≈ eq = ≤-reflexive eq
  ... | tri> gt = ⊥-elim (¬le (<⇒≤ gt))

  -- topping a slack `k` up to `d` costs `d ∸ k`

  top-up : (k b d : Carrier) → k ≤ d → b ∸ (d ∸ k) ≡ (k + b) ∸ d
  top-up k b d le =
    sym (trans (cong ((k + b) ∸_) (sym (m+[n∸m]≡n le)))
               (trans (sym (M.∸-+-assoc (k + b) k (d ∸ k)))
                      (cong (_∸ (d ∸ k)) (M.m+n∸m k b))))

  no-top-up : (b d k : Carrier) → d ≤ k → b ∸ (d ∸ k) ≡ b
  no-top-up b d k le = trans (cong (b ∸_) (M.∸-≤ le)) (M.∸-0 b)

  -- the budget left after topping up is at most what is left in all

  left-≤ : (k b d : Carrier) → b ∸ (d ∸ k) ≤ (k + b) ∸ d
  left-≤ k b d = case (d ≤? k)
    where
      case : Dec (d ≤ k) → b ∸ (d ∸ k) ≤ (k + b) ∸ d
      case (no ¬le) = ≤-reflexive (top-up k b d (≰⇒≥ ¬le))
      case (yes le) =
        subst (_≤ (k + b) ∸ d) (sym (no-top-up b d k le))
              (M.+-≤-∸ (≤-trans le (m≤m+n k b)) (+-monoˡ-≤ b le))

  -- and the slack and budget left add up to what is left in all

  left-sum : (k b d : Carrier) → (k ∸ d) + (b ∸ (d ∸ k)) ≡ (k + b) ∸ d
  left-sum k b d = case (d ≤? k)
    where
      case : Dec (d ≤ k) → (k ∸ d) + (b ∸ (d ∸ k)) ≡ (k + b) ∸ d
      case (yes le) = trans (cong ((k ∸ d) +_) (no-top-up b d k le))
                            (sym (M.+-∸-comm b le))
      case (no ¬le) =
        trans (cong₂ _+_ (M.∸-≤ (≰⇒≥ ¬le)) (top-up k b d (≰⇒≥ ¬le)))
              (+-identityˡ _)

  -- topping up and then paying leaves the slack as paying alone would

  topped-up : (k d : Carrier) → (k + (d ∸ k)) ∸ d ≡ k ∸ d
  topped-up k d = case (d ≤? k)
    where
      case : Dec (d ≤ k) → (k + (d ∸ k)) ∸ d ≡ k ∸ d
      case (yes le) = trans (cong (λ z → (k + z) ∸ d) (M.∸-≤ le))
                            (cong (_∸ d) (+-identityʳ k))
      case (no ¬le) =
        trans (cong (_∸ d) (m+[n∸m]≡n (≰⇒≥ ¬le)))
              (trans (n∸n≡0 d) (sym (M.∸-≤ (≰⇒≥ ¬le))))

  sum-+ : {k₁ b₁ k₂ b₂ : Carrier} (e : Carrier)
        → k₁ + b₁ ≤ k₂ + b₂ → k₁ + (b₁ + e) ≤ k₂ + (b₂ + e)
  sum-+ {k₁} {b₁} {k₂} {b₂} e le =
    subst₂ _≤_ (+-assoc k₁ b₁ e) (+-assoc k₂ b₂ e) (+-monoˡ-≤ e le)

------------------------------------------------------------------------
-- Budget is worth at least as much as slack
--
-- A run's delay turns budget into slack one for one, never the other
-- way, so a state with no less budget and no less of the two together
-- does whatever the other does.

coe⋈ : ∀ {k k' b b' p q} → k ≡ k' → b ≡ b' → p ⋈[ k , b ] q → p ⋈[ k' , b' ] q
coe⋈ refl refl j = j

mono : ∀ {k₁ b₁ k₂ b₂ p q}
     → b₁ ≤ b₂ → k₁ + b₁ ≤ k₂ + b₂
     → p ⋈[ k₁ , b₁ ] q → p ⋈[ k₂ , b₂ ] q
mono hb hs done = done
mono hb hs (bank {e = e} j) = bank (mono (+-monoˡ-≤ ∣ e ∣⁺ hb) (sum-+ ∣ e ∣⁺ hs) j)
mono hb hs (skip j) = skip (mono hb hs j)
mono hb hs (fill {o = o} j) =
  fill (mono ≤-refl (+-monoˡ-≤ 0ᴰ (+-monoˡ-≤ (costˡᵒ o) hs)) j)
mono {k₁} {b₁} {k₂} {b₂} hb hs (spend {d = d} le j) =
  spend le₂ (mono hb' hs' j)
  where
    δ = ∣ d ∣⁺
    le₂ : δ ≤ k₂ + b₂
    le₂ = ≤-trans le hs

    -- what is left in all only grows
    all≤ : (k₁ + b₁) ∸ δ ≤ (k₂ + b₂) ∸ δ
    all≤ = M.∸-monoˡ-≤ δ hs

    hs' : (k₁ ∸ δ) + (b₁ ∸ (δ ∸ k₁)) ≤ (k₂ ∸ δ) + (b₂ ∸ (δ ∸ k₂))
    hs' = subst₂ _≤_ (sym (left-sum k₁ b₁ δ)) (sym (left-sum k₂ b₂ δ)) all≤

    case : Dec (δ ≤ k₂) → b₁ ∸ (δ ∸ k₁) ≤ b₂ ∸ (δ ∸ k₂)
    case (yes le') = subst (b₁ ∸ (δ ∸ k₁) ≤_) (sym (no-top-up b₂ δ k₂ le'))
                           (≤-trans (M.∸-≤-self b₁ (δ ∸ k₁)) hb)
    case (no ¬le') = subst (b₁ ∸ (δ ∸ k₁) ≤_) (sym (top-up k₂ b₂ δ (≰⇒≥ ¬le')))
                           (≤-trans (left-≤ k₁ b₁ δ) all≤)

    hb' : b₁ ∸ (δ ∸ k₁) ≤ b₂ ∸ (δ ∸ k₂)
    hb' = case (δ ≤? k₂)
mono hb hs (match j) = match j
mono {b₁ = b₁} {b₂ = b₂} hb hs (pay {o = o} le j) =
  pay (≤-trans le hb)
      (mono (M.∸-monoˡ-≤ (costʰⁱ o) hb)
            (+-monoʳ-≤ 0ᴰ (M.∸-monoˡ-≤ (costʰⁱ o) hb)) j)

------------------------------------------------------------------------
-- Soundness: the walk builds the run

private

  -- a run padded on the left by a delay of length `τ`, which is slack
  -- to the guarantee and expense to the allowance

  cov-pad′ : ∀ {k p t} (τ : Carrier) (c : Dec (0ᴰ <ᴰ τ))
           → p ≼ᶜ[ k + τ ] t → p ≼ᶜ[ k ] (delay-of τ c ∙ t)
  cov-pad′ {t = t} τ (yes pos) h = CM.absorbR (pos⁺ τ pos) t h
  cov-pad′ {k} τ (no ¬pos) h =
    C.coe (trans (cong (k +_) (≮0⇒≡0 ¬pos)) (+-identityʳ k)) h

  all-pad′ : ∀ {b t q} (τ : Carrier) (c : Dec (0ᴰ <ᴰ τ))
           → τ ≤ b → t ≼ᵃ[ b ∸ τ ] q → (delay-of τ c ∙ t) ≼ᵃ[ b ] q
  all-pad′ {t = t} τ (yes pos) le h = AM.spendL (pos⁺ τ pos) t le h
  all-pad′ {b} τ (no ¬pos) le h =
    A.coe (trans (cong (b ∸_) (≮0⇒≡0 ¬pos)) (M.∸-0 b)) h

  cov-pad : ∀ {k p t} (τ : Carrier) → p ≼ᶜ[ k + τ ] t → p ≼ᶜ[ k ] (⟨ τ ⟩ ∙ t)
  cov-pad τ = cov-pad′ τ (0ᴰ <ᴰ? τ)

  all-pad : ∀ {b t q} (τ : Carrier) → τ ≤ b → t ≼ᵃ[ b ∸ τ ] q → (⟨ τ ⟩ ∙ t) ≼ᵃ[ b ] q
  all-pad τ = all-pad′ τ (0ᴰ <ᴰ? τ)

sound : ∀ {k b p q} → p ⋈[ k , b ] q → Σ Trace (λ x → p ≼ᶜ[ k ] x × x ≼ᵃ[ b ] q)
sound done = ε , C.nil , A.nil
sound (bank j) with sound j
... | x , c , a = x , c , A.bank-delay a
sound (skip j) with sound j
... | x , c , a = x , c , A.skip-op a
sound {k} {b} (fill {o = o} j) with sound j
... | x , c , a =
      ⟨ b ⟩ ∙ operation o x
    , cov-pad b (C.pay-op c)
    , all-pad b ≤-refl (A.keep a)
sound {k} {b} (spend {d = d} le j) with sound j
... | x , c , a =
      ⟨ ∣ d ∣⁺ ∸ k ⟩ ∙ x
    , cov-pad (∣ d ∣⁺ ∸ k)
        (C.use-delay (M.≤-+-∸ ∣ d ∣⁺ k)
                     (C.coe (sym (topped-up k ∣ d ∣⁺)) c))
    , all-pad (∣ d ∣⁺ ∸ k) (M.∸-≤-+ le) a
sound (match j) with sound j
... | x , c , a = operation _ x , C.keep c , A.keep a
sound (pay le j) with sound j
... | x , c , a = operation _ x , C.keep c , A.use-op le a

------------------------------------------------------------------------
-- Completeness: a run and its two derivations give a walk

complete : ∀ {k b p x q} → p ≼ᶜ[ k ] x → x ≼ᵃ[ b ] q → p ⋈[ k , b ] q
complete C.nil _ = done
complete {k} {b} (C.use-delay {d = d} le c) a =
  spend (≤-trans le (m≤m+n k b))
        (coe⋈ refl (sym (no-top-up b ∣ d ∣⁺ k le)) (complete c a))
complete c (A.bank-delay a) = bank (complete c a)
complete c (A.skip-op a)    = skip (complete c a)
complete (C.keep c) (A.keep a)      = match (complete c a)
complete (C.keep c) (A.use-op le a) = pay le (complete c a)
complete {k} {b} (C.pay-op {o = o} c) (A.keep a) =
  fill (mono ≤-refl (+-monoˡ-≤ 0ᴰ (+-monoˡ-≤ (costˡᵒ o) (m≤m+n k b)))
             (complete c a))
complete {k} {b} (C.pay-op {o = o} c) (A.use-op le a) =
  mono (M.∸-≤-self b (costʰⁱ o)) sum (complete c a)
  where
    -- the run's operation banks less slack than it costs budget
    sum : (k + costˡᵒ o) + (b ∸ costʰⁱ o) ≤ k + b
    sum = subst ((k + costˡᵒ o) + (b ∸ costʰⁱ o) ≤_)
                (trans (+-assoc k (costʰⁱ o) (b ∸ costʰⁱ o))
                       (cong (k +_) (m+[n∸m]≡n le)))
                (+-monoˡ-≤ (b ∸ costʰⁱ o) (+-monoʳ-≤ k (cost-≤ o)))
complete {k} {b} (C.del-delay {e = e} c) (A.use-delay le a) =
  mono (M.∸-≤-self b ∣ e ∣⁺)
       (≤-reflexive (trans (+-assoc k ∣ e ∣⁺ (b ∸ ∣ e ∣⁺))
                           (cong (k +_) (m+[n∸m]≡n le))))
       (complete c a)

consistent : ∀ {p q} → p ⋈[ 0ᴰ , 0ᴰ ] q → Consistent p q
consistent = sound

consistent⁻¹ : ∀ {p q} → Consistent p q → p ⋈[ 0ᴰ , 0ᴰ ] q
consistent⁻¹ (_ , c , a) = complete c a

------------------------------------------------------------------------
-- The decision procedure
--
-- Fuelled by the combined size of the two traces, which every rule
-- shrinks. Each head pair admits a few rules, and the search tries
-- them all.

module DecConsistency (_≟ₒ_ : DecidableEquality Op) where

  private
    step : ∀ {n} (a c : ℕ) → a ℕ.+ suc c ℕ.≤ n → suc a ℕ.+ c ℕ.≤ n
    step {n} a c = subst (ℕ._≤ n) (ℕ.+-suc a c)

    drop : ∀ {n} (a c : ℕ) → a ℕ.+ suc c ℕ.≤ n → a ℕ.+ c ℕ.≤ n
    drop a c le = ℕ.≤-trans (ℕ.+-monoʳ-≤ a (ℕ.n≤1+n c)) le

    inj⁻ʳ : ∀ {n} (a : ℕ) (q⁻ : Trace⁻) → a ℕ.+ size⁻ q⁻ ℕ.≤ n
          → a ℕ.+ size (inj⁻ q⁻) ℕ.≤ n
    inj⁻ʳ {n} a q⁻ = subst (λ z → a ℕ.+ z ℕ.≤ n) (sym (size-inj⁻ q⁻))

    inj⁻ˡ : ∀ {n} (p⁻ : Trace⁻) (c : ℕ) → size⁻ p⁻ ℕ.+ c ℕ.≤ n
          → size (inj⁻ p⁻) ℕ.+ c ℕ.≤ n
    inj⁻ˡ {n} p⁻ c = subst (λ z → z ℕ.+ c ℕ.≤ n) (sym (size-inj⁻ p⁻))

  dec : (n : ℕ) (p : Trace) (k b : Carrier) (q : Trace)
      → size p ℕ.+ size q ℕ.≤ n → Dec (p ⋈[ k , b ] q)

  dec n ε k b q le = yes done

  -- an operation of the guarantee against a spent allowance: pay
  dec (suc n) (operation o p) k b ε (s≤s le) =
    map′ (λ (h , j) → pay h j) (λ { (pay h j) → h , j })
         (costʰⁱ o ≤? b ×-dec dec n p 0ᴰ (b ∸ costʰⁱ o) ε le)

  -- against an operation of the allowance: match, pay, skip or fill
  dec (suc n) (operation o p) k b (operation r q) (s≤s le) =
    map′ into from
         (((o ≟ₒ r) ×-dec dec n p 0ᴰ 0ᴰ q (drop (size p) (size q) le))
          ⊎-dec ((costʰⁱ o ≤? b ×-dec dec n p 0ᴰ (b ∸ costʰⁱ o) (operation r q) le)
          ⊎-dec (dec n (operation o p) k b q (step (size p) (size q) le)
          ⊎-dec dec n (operation o p) ((k + b) + costˡᵒ r) 0ᴰ q
                    (step (size p) (size q) le))))
    where
      into : _ → operation o p ⋈[ k , b ] operation r q
      into (inj₁ (refl , j))               = match j
      into (inj₂ (inj₁ (h , j)))           = pay h j
      into (inj₂ (inj₂ (inj₁ j)))          = skip j
      into (inj₂ (inj₂ (inj₂ j)))          = fill j
      from : operation o p ⋈[ k , b ] operation r q → _
      from (match j) = inj₁ (refl , j)
      from (pay h j) = inj₂ (inj₁ (h , j))
      from (skip j)  = inj₂ (inj₂ (inj₁ j))
      from (fill j)  = inj₂ (inj₂ (inj₂ j))

  -- against a delay of the allowance: pay or bank
  dec (suc n) (operation o p) k b (delay e q⁻) (s≤s le) =
    map′ into from
         ((costʰⁱ o ≤? b ×-dec dec n p 0ᴰ (b ∸ costʰⁱ o) (delay e q⁻) le)
          ⊎-dec dec n (operation o p) k (b + ∣ e ∣⁺) (inj⁻ q⁻)
                    (inj⁻ʳ (suc (size p)) q⁻ (step (size p) (size⁻ q⁻) le)))
    where
      into : _ → operation o p ⋈[ k , b ] delay e q⁻
      into (inj₁ (h , j)) = pay h j
      into (inj₂ j)       = bank j
      from : operation o p ⋈[ k , b ] delay e q⁻ → _
      from (pay h j) = inj₁ (h , j)
      from (bank j)  = inj₂ j

  -- a delay of the guarantee against a spent allowance: spend
  dec (suc n) (delay d p⁻) k b ε (s≤s le) =
    map′ (λ (h , j) → spend h j) (λ { (spend h j) → h , j })
         (∣ d ∣⁺ ≤? k + b ×-dec
          dec n (inj⁻ p⁻) (k ∸ ∣ d ∣⁺) (b ∸ (∣ d ∣⁺ ∸ k)) ε (inj⁻ˡ p⁻ 0 le))

  -- against an operation of the allowance: spend, skip or fill
  dec (suc n) (delay d p⁻) k b (operation r q) (s≤s le) =
    map′ into from
         ((∣ d ∣⁺ ≤? k + b ×-dec
           dec n (inj⁻ p⁻) (k ∸ ∣ d ∣⁺) (b ∸ (∣ d ∣⁺ ∸ k)) (operation r q)
               (inj⁻ˡ p⁻ (suc (size q)) le))
          ⊎-dec (dec n (delay d p⁻) k b q (step (size⁻ p⁻) (size q) le)
          ⊎-dec dec n (delay d p⁻) ((k + b) + costˡᵒ r) 0ᴰ q
                    (step (size⁻ p⁻) (size q) le)))
    where
      into : _ → delay d p⁻ ⋈[ k , b ] operation r q
      into (inj₁ (h , j))      = spend h j
      into (inj₂ (inj₁ j))     = skip j
      into (inj₂ (inj₂ j))     = fill j
      from : delay d p⁻ ⋈[ k , b ] operation r q → _
      from (spend h j) = inj₁ (h , j)
      from (skip j)    = inj₂ (inj₁ j)
      from (fill j)    = inj₂ (inj₂ j)

  -- against a delay of the allowance: bank or spend
  dec (suc n) (delay d p⁻) k b (delay e q⁻) (s≤s le) =
    map′ into from
         (dec n (delay d p⁻) k (b + ∣ e ∣⁺) (inj⁻ q⁻)
              (inj⁻ʳ (suc (size⁻ p⁻)) q⁻ (step (size⁻ p⁻) (size⁻ q⁻) le))
          ⊎-dec (∣ d ∣⁺ ≤? k + b ×-dec
                 dec n (inj⁻ p⁻) (k ∸ ∣ d ∣⁺) (b ∸ (∣ d ∣⁺ ∸ k)) (delay e q⁻)
                     (inj⁻ˡ p⁻ (suc (size⁻ q⁻)) le)))
    where
      into : _ → delay d p⁻ ⋈[ k , b ] delay e q⁻
      into (inj₁ j)       = bank j
      into (inj₂ (h , j)) = spend h j
      from : delay d p⁻ ⋈[ k , b ] delay e q⁻ → _
      from (bank j)    = inj₁ j
      from (spend h j) = inj₂ (h , j)

  infix 4 _⋈[_,_]?_ _⋈?_

  _⋈[_,_]?_ : (p : Trace) (k b : Carrier) (q : Trace) → Dec (p ⋈[ k , b ] q)
  p ⋈[ k , b ]? q = dec (size p ℕ.+ size q) p k b q ℕ.≤-refl

  -- consistency, decided

  _⋈?_ : (p q : Trace) → Dec (Consistent p q)
  p ⋈? q = map′ consistent consistent⁻¹ (p ⋈[ 0ᴰ , 0ᴰ ]? q)
