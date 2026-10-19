------------------------------------------------------------------------
-- Fitting one exact word into another by pouring.                    --
--                                                                    --
-- `Pour x a y b` walks the two words in step, `x` from offset `a`    --
-- into its first item and `y` from offset `b` into its first: an     --
-- item of `x` is poured, any amount at a time, into a stretch of `y` --
-- that admits it; an exhausted first item is passed; an operation of --
-- `y` is met by the same operation of `x`, both from their starts.   --
-- A walk from the starts of both words shows that `x` fits `y`.      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Exact.Pour
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Subset using (_∈_; _⊆_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Solver T using (solve; _⊜_; _⊕_)

open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Order T Op n code code-injective

private
  variable
    a b p q : Carrier

  ≮⇒≥ : ¬ (p <ᴰ a) → a ≤ᴰ p
  ≮⇒≥ {p} {a} ¬p with a ≤ᴰ? p
  ... | yes s = s
  ... | no ¬s = ⊥-elim (¬p ¬s)

  split : a ≤ᴰ p → Σ[ q ∈ Carrier ] p ≡ a +ᴰ q
  split r with diff r
  ... | q , e = q , sym e

  <-+ᴸ-cancel : a +ᴰ p <ᴰ a +ᴰ q → p <ᴰ q
  <-+ᴸ-cancel {a} s t = s (+ᴰ-monoʳ-≤ a t)

------------------------------------------------------------------------
-- An item admitted by a stretch

Adm : Item → OpSet → Set
Adm (op o _) S = code o ∈ S
Adm (st _ S′) S = S′ ⊆ S

adm-≤ˡ : ∀ i {S} → Adm i S → ∀ p → labᵢ i p ≤ˡ bud S
adm-≤ˡ (op o d) a p = opl≤bud a
adm-≤ˡ (st d S′) a p = bud≤bud a

------------------------------------------------------------------------
-- The walk

data Pour : Word → Carrier → Word → Carrier → Set where
  done  : Pour [] 0ᴰ [] 0ᴰ
  match : ∀ {o d x y} → Pour x 0ᴰ y 0ᴰ → Pour (op o d ∷ x) 0ᴰ (op o d ∷ y) 0ᴰ
  nextx : ∀ {i x y b} → Pour x 0ᴰ y b → Pour (i ∷ x) (len i) y b
  nexty : ∀ {j x y a} → Pour x a y 0ᴰ → Pour x a (j ∷ y) (len j)
  pour  : ∀ {i x e S y a b} q → Adm i S → a +ᴰ q ≤ᴰ len i → b +ᴰ q ≤ᴰ ∣ e ∣⁺
        → Pour (i ∷ x) (a +ᴰ q) (st e S ∷ y) (b +ᴰ q)
        → Pour (i ∷ x) a (st e S ∷ y) b

------------------------------------------------------------------------
-- A walk is a fit of what remains

private
  -- inside the first item, from an offset
  here-at : ∀ {i w} {a p q} → a +ᴰ q ≤ᴰ len i → p <ᴰ q → lab (i ∷ w) (a +ᴰ p) ≡ labᵢ i (a +ᴰ p)
  here-at {i} {w} {a} r s = lab-here {i} {w} (<-≤-trans (+ᴰ-monoʳ-< a s) r)

Rest : Word → Carrier → Word → Carrier → Set
Rest x a y b = Σ[ R ∈ Carrier ] (dur x ≡ a +ᴰ R) × (dur y ≡ b +ᴰ R)
                 × (∀ p → p <ᴰ R → lab x (a +ᴰ p) ≤ˡ lab y (b +ᴰ p))

pour-rest : ∀ {x a y b} → Pour x a y b → Rest x a y b
pour-rest done = 0ᴰ , sym (+ᴰ-identityˡ 0ᴰ) , sym (+ᴰ-identityˡ 0ᴰ) , λ p r → ⊥-elim (r (0ᴰ-least p))
pour-rest (match {o} {d} {x} {y} w) with pour-rest w
... | R , ex , ey , h =
  ∣ d ∣⁺ +ᴰ R ,
  trans (cong (∣ d ∣⁺ +ᴰ_) (trans ex (+ᴰ-identityˡ R))) (sym (+ᴰ-identityˡ _)) ,
  trans (cong (∣ d ∣⁺ +ᴰ_) (trans ey (+ᴰ-identityˡ R))) (sym (+ᴰ-identityˡ _)) ,
  at
  where
    at : ∀ p → p <ᴰ ∣ d ∣⁺ +ᴰ R → lab (op o d ∷ x) (0ᴰ +ᴰ p) ≤ˡ lab (op o d ∷ y) (0ᴰ +ᴰ p)
    at p r rewrite +ᴰ-identityˡ p = case (p <ᴰ? ∣ d ∣⁺)
      where
        case : Dec (p <ᴰ ∣ d ∣⁺) → lab (op o d ∷ x) p ≤ˡ lab (op o d ∷ y) p
        case (yes s) =
          subst₂ _≤ˡ_ (sym (lab-here {op o d} {x} s)) (sym (lab-here {op o d} {y} s)) ≤ˡ-refl
        case (no ¬s) = past (split (≮⇒≥ ¬s))
          where
            past : Σ[ q ∈ Carrier ] p ≡ ∣ d ∣⁺ +ᴰ q → lab (op o d ∷ x) p ≤ˡ lab (op o d ∷ y) p
            past (q , e) =
              subst (λ z → lab (op o d ∷ x) z ≤ˡ lab (op o d ∷ y) z) (sym e)
                (subst₂ _≤ˡ_ (sym (lab-skip (op o d) x q)) (sym (lab-skip (op o d) y q))
                  (subst₂ (λ u v → lab x u ≤ˡ lab y v) (+ᴰ-identityˡ q) (+ᴰ-identityˡ q)
                    (h q (<-+ᴸ-cancel (subst (_<ᴰ ∣ d ∣⁺ +ᴰ R) e r)))))
pour-rest (nextx {i} {x} {y} {b} w) with pour-rest w
... | R , ex , ey , h =
  R , trans (cong (len i +ᴰ_) (trans ex (+ᴰ-identityˡ R))) refl , ey ,
  λ p r → subst (_≤ˡ lab y (b +ᴰ p))
            (trans (cong (lab x) (+ᴰ-identityˡ p)) (sym (lab-skip i x p))) (h p r)
pour-rest (nexty {j} {x} {y} {a} w) with pour-rest w
... | R , ex , ey , h =
  R , ex , trans (cong (len j +ᴰ_) (trans ey (+ᴰ-identityˡ R))) refl ,
  λ p r → subst (lab x (a +ᴰ p) ≤ˡ_)
            (trans (cong (lab y) (+ᴰ-identityˡ p)) (sym (lab-skip j y p))) (h p r)
pour-rest (pour {i} {x} {e} {S} {y} {a} {b} q ad ra rb w) with pour-rest w
... | R , ex , ey , h =
  q +ᴰ R ,
  trans ex (+ᴰ-assoc a q R) , trans ey (+ᴰ-assoc b q R) , at
  where
    at : ∀ p → p <ᴰ q +ᴰ R → lab (i ∷ x) (a +ᴰ p) ≤ˡ lab (st e S ∷ y) (b +ᴰ p)
    at p r = case (p <ᴰ? q)
      where
        case : Dec (p <ᴰ q) → lab (i ∷ x) (a +ᴰ p) ≤ˡ lab (st e S ∷ y) (b +ᴰ p)
        case (yes s) =
          subst₂ _≤ˡ_ (sym (here-at {i} {x} ra s)) (sym (here-at {st e S} {y} rb s))
            (adm-≤ˡ i ad (a +ᴰ p))
        case (no ¬s) = past (split (≮⇒≥ ¬s))
          where
            past : Σ[ t ∈ Carrier ] p ≡ q +ᴰ t
                 → lab (i ∷ x) (a +ᴰ p) ≤ˡ lab (st e S ∷ y) (b +ᴰ p)
            past (t , eq) =
              subst (λ z → lab (i ∷ x) (a +ᴰ z) ≤ˡ lab (st e S ∷ y) (b +ᴰ z)) (sym eq)
                (subst₂ (λ u v → lab (i ∷ x) u ≤ˡ lab (st e S ∷ y) v)
                  (+ᴰ-assoc a q t) (+ᴰ-assoc b q t)
                  (h t (<-+ᴸ-cancel (subst (_<ᴰ q +ᴰ R) eq r))))

-- a walk from both starts is a fit

pour-⊑ : ∀ {x y} → Pour x 0ᴰ y 0ᴰ → x ⊑ y
pour-⊑ {x} {y} w with pour-rest w
... | R , ex , ey , h =
  fits (trans ex (sym ey))
       (λ p r → subst₂ (λ u v → lab x u ≤ˡ lab y v) (+ᴰ-identityˡ p) (+ᴰ-identityˡ p)
                  (h p (subst (p <ᴰ_) (trans ey (+ᴰ-identityˡ R)) r)))
