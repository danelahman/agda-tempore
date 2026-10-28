------------------------------------------------------------------------
-- Removing and inserting time inside the stretches of a word.        --
--                                                                    --
-- `CutOf w a c w′`: `w′` is `w` with the time from `a` to `a + c`    --
-- taken out. `InsOf w a c b w′`: `w′` is `w` with `c` units of time  --
-- put in at `a`, labelled as `w` is at `b`. Both are stated through   --
-- the labels, and both are preserved by fitting: removing the same   --
-- time from two words that fit keeps them fitting, and so does       --
-- inserting the same time, when what is inserted into the lesser     --
-- word is labelled below what is inserted into the greater.          --
--                                                                    --
-- When the time removed lies inside stretches of a word, removing it --
-- is shrinking those stretches (`cut`); when the time just before    --
-- the insertion point lies inside a stretch, inserting is            --
-- lengthening that stretch (`insert`).                               --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Splice
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Solver T using (solve; _⊜_; _⊕_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective
open import Grades.Exact.Resize T Op n code code-injective running

------------------------------------------------------------------------
-- Arithmetic

private
  variable
    a b c k p q r : Carrier

  ≮⇒≥ : ¬ (p <ᴰ a) → a ≤ᴰ p
  ≮⇒≥ {p} {a} ¬p with a ≤ᴰ? p
  ... | yes s = s
  ... | no ¬s = ⊥-elim (¬p ¬s)

  -- what lies above `a` is `a` followed by something

  split : a ≤ᴰ p → Σ[ q ∈ Carrier ] p ≡ a +ᴰ q
  split r with diff r
  ... | q , e = q , sym e

  -- adding on the left is strictly monotone and cancels

  <-+ᴸ-cancel : a +ᴰ q <ᴰ a +ᴰ r → q <ᴰ r
  <-+ᴸ-cancel {a} s t = s (+ᴰ-monoʳ-≤ a t)

  <-+ᴿ : q <ᴰ r → q +ᴰ a <ᴰ r +ᴰ a
  <-+ᴿ {a = a} = +ᴰ-monoˡ-< a

  <-+ᴸ : q <ᴰ r → a +ᴰ q <ᴰ a +ᴰ r
  <-+ᴸ {a = a} = +ᴰ-monoʳ-< a

  <-≤-+ : p <ᴰ a → p <ᴰ a +ᴰ k
  <-≤-+ {a = a} {k} s = <-≤-trans s (≤ᴰ-+ a k)

  -- the sum is not below its first summand

  ≮-+ : ¬ (a +ᴰ q <ᴰ a)
  ≮-+ {a} {q} s = s (≤ᴰ-+ a q)

------------------------------------------------------------------------
-- Labels of the words involved

lab-++ʳ′ : ∀ x y q → lab (x ++ y) (dur x +ᴰ q) ≡ lab y q
lab-++ʳ′ x y q = trans (lab-++ʳ x y ≮-+) (cong (lab y) (m+n∸m (dur x) q))

private
  lab-st-in : ∀ {d S w} → p <ᴰ ∣ d ∣⁺ → lab (st d S ∷ w) p ≡ bud S
  lab-st-in {d = d} {S} {w} s = lab-here {st d S} {w} s

  lab-stretch-in : ∀ {S τ w} → p <ᴰ τ → lab (stretch S τ ++ w) p ≡ bud S
  lab-stretch-in {p} {S} {τ} {w} s =
    trans (lab-++ˡ (stretch S τ) w (subst (p <ᴰ_) (sym (dur-stretch S τ)) s))
          (lab-stretch S τ s)

  lab-stretch-skip : ∀ S τ w q → lab (stretch S τ ++ w) (τ +ᴰ q) ≡ lab w q
  lab-stretch-skip S τ w q =
    trans (cong (λ z → lab (stretch S τ ++ w) (z +ᴰ q)) (sym (dur-stretch S τ)))
          (lab-++ʳ′ (stretch S τ) w q)

  lab-st-skip : ∀ d S w q → lab (st d S ∷ w) (∣ d ∣⁺ +ᴰ q) ≡ lab w q
  lab-st-skip d S w q = lab-skip (st d S) w q

------------------------------------------------------------------------
-- Removing time

-- the labels in a stretch of time are those of stretches

IsBud : Label → Set
IsBud ℓ = Σ[ S ∈ OpSet ] ℓ ≡ bud S

bud-≤ˡ : ∀ {S ℓ} → bud S ≤ˡ ℓ → IsBud ℓ
bud-≤ˡ (bud≤bud {S′ = S′} _) = S′ , refl

BudOn : Word → Carrier → Carrier → Set
BudOn w a c = ∀ q → q <ᴰ c → IsBud (lab w (a +ᴰ q))

CutOf : Word → Carrier → Carrier → Word → Set
CutOf w a c w′ =
  (dur w′ +ᴰ c ≡ dur w) ×
  (∀ p → p <ᴰ a → lab w′ p ≡ lab w p) ×
  (∀ q → lab w′ (a +ᴰ q) ≡ lab w ((a +ᴰ c) +ᴰ q))

-- removing the same time keeps two words fitting

cut-fit : ∀ {x y x′ y′} → x ⊑ y → CutOf x a c x′ → CutOf y a c y′ → x′ ⊑ y′
cut-fit {a} {c} {x} {y} {x′} {y′} (fits e h) (dx , bx , ax) (dy , by , ay) =
  fits (+ᴰ-cancelʳ c (trans dx (trans e (sym dy)))) at
  where
    in-y : ∀ {p} → p <ᴰ dur y′ → p <ᴰ dur y
    in-y s = <-≤-trans s (subst (dur y′ ≤ᴰ_) dy (≤ᴰ-+ (dur y′) c))
    at : ∀ p → p <ᴰ dur y′ → lab x′ p ≤ˡ lab y′ p
    past : ∀ q → a +ᴰ q <ᴰ dur y′ → lab x′ (a +ᴰ q) ≤ˡ lab y′ (a +ᴰ q)
    past q s =
      subst₂ _≤ˡ_ (sym (ax q)) (sym (ay q))
        (h ((a +ᴰ c) +ᴰ q)
           (subst (_<ᴰ dur y)
                  (solve 3 (λ a q c → (a ⊕ q) ⊕ c ⊜ (a ⊕ c) ⊕ q) refl a q c)
                  (subst ((a +ᴰ q) +ᴰ c <ᴰ_) dy (<-+ᴿ s))))
    at p s with p <ᴰ? a
    ... | yes t = subst₂ _≤ˡ_ (sym (bx p t)) (sym (by p t)) (h p (in-y s))
    ... | no ¬t with split (≮⇒≥ ¬t)
    ...   | q , e = subst (λ z → lab x′ z ≤ˡ lab y′ z) (sym e) (past q (subst (_<ᴰ dur y′) e s))

-- removing nothing

cut-zero : ∀ w a → CutOf w a 0ᴰ w
cut-zero w a =
  +ᴰ-identityʳ (dur w) , (λ _ _ → refl) ,
  (λ q → cong (λ z → lab w (z +ᴰ q)) (sym (+ᴰ-identityʳ a)))

-- removing time from the tail of a word

cut-cons : ∀ i {w w′ a′} → CutOf w a′ c w′ → CutOf (i ∷ w) (len i +ᴰ a′) c (i ∷ w′)
cut-cons {c} i {w} {w′} {a′} (d′ , b′ , a″) =
  trans (+ᴰ-assoc (len i) (dur w′) c) (cong (len i +ᴰ_) d′) , before , after
  where
    before : ∀ p → p <ᴰ len i +ᴰ a′ → lab (i ∷ w′) p ≡ lab (i ∷ w) p
    before p s = case (p <ᴰ? len i)
      where
        case : Dec (p <ᴰ len i) → lab (i ∷ w′) p ≡ lab (i ∷ w) p
        case (yes t) = trans (lab-here {i} {w′} t) (sym (lab-here {i} {w} t))
        case (no ¬t) = case′ (split (≮⇒≥ ¬t))
          where
          case′ : Σ[ r ∈ Carrier ] p ≡ len i +ᴰ r → lab (i ∷ w′) p ≡ lab (i ∷ w) p
          case′ (r , e) =
            subst (λ z → lab (i ∷ w′) z ≡ lab (i ∷ w) z) (sym e)
              (trans (lab-skip i w′ r)
                (trans (b′ r (<-+ᴸ-cancel (subst (_<ᴰ len i +ᴰ a′) e s))) (sym (lab-skip i w r))))
    after : ∀ q → lab (i ∷ w′) ((len i +ᴰ a′) +ᴰ q) ≡ lab (i ∷ w) (((len i +ᴰ a′) +ᴰ c) +ᴰ q)
    after q =
      trans (cong (lab (i ∷ w′)) (+ᴰ-assoc (len i) a′ q))
      (trans (lab-skip i w′ (a′ +ᴰ q))
      (trans (a″ q)
      (trans (sym (lab-skip i w ((a′ +ᴰ c) +ᴰ q)))
             (cong (lab (i ∷ w))
                   (solve 4 (λ l a c q → l ⊕ ((a ⊕ c) ⊕ q) ⊜ ((l ⊕ a) ⊕ c) ⊕ q) refl
                          (len i) a′ c q)))))

-- removing time inside the stretches of a word shrinks them

private
  op-not-bud : ∀ {o δ d} → ¬ IsBud (opl o δ d)
  op-not-bud (_ , ())

private
  keep : ∀ i {w w′} → Shrinks w w′ → Shrinks (i ∷ w) (i ∷ w′)
  keep (op o d) s = op s
  keep (st d S) {w} {w′} s =
    subst (Shrinks (st d S ∷ w)) (cong (_++ w′) (stretch-∣∣ S d)) (st ≤ᴰ-refl s)

  Cut : Word → Carrier → Carrier → Set
  Cut y a c = Σ[ y′ ∈ Word ] Shrinks y y′ × CutOf y a c y′

  go-inside : ∀ d S w a c → Σ[ k ∈ Carrier ] ∣ d ∣⁺ ≡ (a +ᴰ c) +ᴰ k → Cut (st d S ∷ w) a c
  go-over : ∀ d S w a r₀ c′ → ∣ d ∣⁺ ≡ a +ᴰ r₀
          → a +ᴰ (r₀ +ᴰ c′) ≤ᴰ dur (st d S ∷ w) → BudOn (st d S ∷ w) a (r₀ +ᴰ c′)
          → ¬ (a +ᴰ (r₀ +ᴰ c′) ≤ᴰ ∣ d ∣⁺)
          → Cut (st d S ∷ w) a (r₀ +ᴰ c′)

  go-cons : ∀ i w a c → 0ᴰ <ᴰ c → a +ᴰ c ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) a c
          → Dec (a <ᴰ len i) → Cut (i ∷ w) a c
  go-past : ∀ i w a′ c → 0ᴰ <ᴰ c → (len i +ᴰ a′) +ᴰ c ≤ᴰ dur (i ∷ w)
          → BudOn (i ∷ w) (len i +ᴰ a′) c → Cut (i ∷ w) (len i +ᴰ a′) c
  go-shift : ∀ i w a c → 0ᴰ <ᴰ c → a +ᴰ c ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) a c
           → Σ[ a′ ∈ Carrier ] a ≡ len i +ᴰ a′ → Cut (i ∷ w) a c
  go-st : ∀ d S w a c → a +ᴰ c ≤ᴰ dur (st d S ∷ w) → BudOn (st d S ∷ w) a c
        → a <ᴰ ∣ d ∣⁺ → Dec (a +ᴰ c ≤ᴰ ∣ d ∣⁺) → Cut (st d S ∷ w) a c
  go-split : ∀ d S w a c → a +ᴰ c ≤ᴰ dur (st d S ∷ w) → BudOn (st d S ∷ w) a c
           → ¬ (a +ᴰ c ≤ᴰ ∣ d ∣⁺) → Σ[ r₀ ∈ Carrier ] ∣ d ∣⁺ ≡ a +ᴰ r₀ → Cut (st d S ∷ w) a c
  go-split′ : ∀ d S w a c r₀ → ∣ d ∣⁺ ≡ a +ᴰ r₀ → a +ᴰ c ≤ᴰ dur (st d S ∷ w)
            → BudOn (st d S ∷ w) a c → ¬ (a +ᴰ c ≤ᴰ ∣ d ∣⁺)
            → Σ[ c′ ∈ Carrier ] c ≡ r₀ +ᴰ c′ → Cut (st d S ∷ w) a c
  go : ∀ y a c → 0ᴰ <ᴰ c → a +ᴰ c ≤ᴰ dur y → BudOn y a c → Cut y a c
  go []      a c c>0 le bd = ⊥-elim (c>0 (≤ᴰ-trans (≤ᴰ-+ˡ c a) le))
  go (i ∷ w) a c c>0 le bd = go-cons i w a c c>0 le bd (a <ᴰ? len i)

  go-cons i w a c c>0 le bd (no ¬r) = go-shift i w a c c>0 le bd (split (≮⇒≥ ¬r))
  go-cons (op o d) w a c c>0 le bd (yes r) =
    ⊥-elim (op-not-bud (subst IsBud (trans (cong (lab (op o d ∷ w)) (+ᴰ-identityʳ a))
                                           (lab-here {op o d} {w} r))
                                    (bd 0ᴰ c>0)))
  go-cons (st d S) w a c c>0 le bd (yes r) = go-st d S w a c le bd r (a +ᴰ c ≤ᴰ? ∣ d ∣⁺)

  go-shift i w a c c>0 le bd (a′ , e) =
    subst (λ z → Cut (i ∷ w) z c) (sym e)
      (go-past i w a′ c c>0 (subst (λ z → z +ᴰ c ≤ᴰ dur (i ∷ w)) e le)
               (subst (λ z → BudOn (i ∷ w) z c) e bd))

  go-st d S w a c le bd r (yes s) = go-inside d S w a c (split s)
  go-st d S w a c le bd r (no ¬s) = go-split d S w a c le bd ¬s (split (<⇒≤ r))

  go-split d S w a c le bd ¬s (r₀ , dr) =
    go-split′ d S w a c r₀ dr le bd ¬s
      (split (<⇒≤ (<-+ᴸ-cancel {a} (subst (_<ᴰ a +ᴰ c) dr ¬s))))

  go-split′ d S w a c r₀ dr le bd ¬s (c′ , ec) =
    subst (Cut (st d S ∷ w) a) (sym ec)
      (go-over d S w a r₀ c′ dr
         (subst (λ z → a +ᴰ z ≤ᴰ dur (st d S ∷ w)) ec le)
         (subst (BudOn (st d S ∷ w) a) ec bd)
         (subst (λ z → ¬ (a +ᴰ z ≤ᴰ ∣ d ∣⁺)) ec ¬s))

  -- the time removed starts past the first item
  go-past i w a′ c c>0 le bd with go w a′ c c>0 le′ bd′
    where
      le′ : a′ +ᴰ c ≤ᴰ dur w
      le′ = +ᴰ-cancelˡ-≤ (len i)
              (subst (_≤ᴰ len i +ᴰ dur w) (+ᴰ-assoc (len i) a′ c) le)
      bd′ : BudOn w a′ c
      bd′ q s = subst IsBud (trans (cong (lab (i ∷ w)) (+ᴰ-assoc (len i) a′ q))
                                   (lab-skip i w (a′ +ᴰ q)))
                            (bd q s)
  ... | w′ , sw , cw = i ∷ w′ , keep i sw , cut-cons i cw

  -- the time removed ends inside the first stretch
  go-inside d S w a c (k , dk) =
    stretch S (a +ᴰ k) ++ w ,
    st (≤ᴰ-trans (+ᴰ-monoˡ-≤ k (≤ᴰ-+ a c)) (≤ᴰ-reflexive (trans (solve 3 (λ a c k → (a ⊕ c) ⊕ k ⊜ (a ⊕ c) ⊕ k) refl a c k) (sym dk))))
       (Shrinks-refl w) ,
    dur′ , before , after
    where
      dur′ : dur (stretch S (a +ᴰ k) ++ w) +ᴰ c ≡ ∣ d ∣⁺ +ᴰ dur w
      dur′ = trans (cong (_+ᴰ c) (trans (dur-++ (stretch S (a +ᴰ k)) w)
                                        (cong (_+ᴰ dur w) (dur-stretch S (a +ᴰ k)))))
             (trans (solve 4 (λ a k w c → ((a ⊕ k) ⊕ w) ⊕ c ⊜ ((a ⊕ c) ⊕ k) ⊕ w) refl
                             a k (dur w) c)
                    (cong (_+ᴰ dur w) (sym dk)))
      before : ∀ p → p <ᴰ a → lab (stretch S (a +ᴰ k) ++ w) p ≡ lab (st d S ∷ w) p
      before p t = trans (lab-stretch-in (<-≤-+ t))
                         (sym (lab-st-in (<-≤-trans t (subst (a ≤ᴰ_) (sym dk)
                                (≤ᴰ-trans (≤ᴰ-+ a c) (≤ᴰ-+ (a +ᴰ c) k))))))
      past : ∀ m → lab (stretch S (a +ᴰ k) ++ w) (a +ᴰ (k +ᴰ m)) ≡ lab (st d S ∷ w) ((a +ᴰ c) +ᴰ (k +ᴰ m))
      past m =
        trans (cong (lab (stretch S (a +ᴰ k) ++ w)) (sym (+ᴰ-assoc a k m)))
        (trans (lab-stretch-skip S (a +ᴰ k) w m)
        (sym (trans (cong (lab (st d S ∷ w))
                          (trans (sym (+ᴰ-assoc (a +ᴰ c) k m)) (cong (_+ᴰ m) (sym dk))))
                    (lab-st-skip d S w m))))
      after : ∀ q → lab (stretch S (a +ᴰ k) ++ w) (a +ᴰ q) ≡ lab (st d S ∷ w) ((a +ᴰ c) +ᴰ q)
      after q with q <ᴰ? k
      ... | yes t = trans (lab-stretch-in (<-+ᴸ t))
                          (sym (lab-st-in (subst ((a +ᴰ c) +ᴰ q <ᴰ_) (sym dk) (<-+ᴸ t))))
      ... | no ¬t with split (≮⇒≥ ¬t)
      ...   | m , e = subst (λ z → lab (stretch S (a +ᴰ k) ++ w) (a +ᴰ z) ≡ lab (st d S ∷ w) ((a +ᴰ c) +ᴰ z))
                            (sym e) (past m)

  -- the time removed runs on past the first stretch
  go-over d S w a r₀ c′ dr le bd ¬s with go w 0ᴰ c′ c′>0 le′ bd′
    where
      c′>0 : 0ᴰ <ᴰ c′
      c′>0 t = ¬s (≤ᴰ-reflexive (trans (sym (+ᴰ-assoc a r₀ c′))
                                (trans (cong ((a +ᴰ r₀) +ᴰ_) (≤0⇒≡0 t))
                                       (trans (+ᴰ-identityʳ (a +ᴰ r₀)) (sym dr)))))
      le′ : 0ᴰ +ᴰ c′ ≤ᴰ dur w
      le′ = subst (_≤ᴰ dur w) (sym (+ᴰ-identityˡ c′))
              (+ᴰ-cancelˡ-≤ (a +ᴰ r₀)
                (subst₂ _≤ᴰ_ (sym (+ᴰ-assoc a r₀ c′)) (cong (_+ᴰ dur w) dr) le))
      bd′ : BudOn w 0ᴰ c′
      bd′ q t = subst IsBud
                  (trans (cong (lab (st d S ∷ w))
                               (trans (sym (+ᴰ-assoc a r₀ q))
                                      (cong (_+ᴰ q) (sym dr))))
                  (trans (lab-st-skip d S w q)
                         (cong (lab w) (sym (+ᴰ-identityˡ q)))))
                  (bd (r₀ +ᴰ q) (<-+ᴸ t))
  ... | w′ , sw , (dw , _ , aw) =
    stretch S a ++ w′ , st (≤ᴰ-trans (≤ᴰ-+ a r₀) (≤ᴰ-reflexive (sym dr))) sw ,
    dur′ , before , after
    where
      dur′ : dur (stretch S a ++ w′) +ᴰ (r₀ +ᴰ c′) ≡ ∣ d ∣⁺ +ᴰ dur w
      dur′ = trans (cong (_+ᴰ (r₀ +ᴰ c′)) (trans (dur-++ (stretch S a) w′)
                                             (cong (_+ᴰ dur w′) (dur-stretch S a))))
             (trans (solve 4 (λ a w r c → (a ⊕ w) ⊕ (r ⊕ c) ⊜ (a ⊕ r) ⊕ (w ⊕ c)) refl
                             a (dur w′) r₀ c′)
                    (cong₂ _+ᴰ_ (sym dr) dw))
      before : ∀ p → p <ᴰ a → lab (stretch S a ++ w′) p ≡ lab (st d S ∷ w) p
      before p t = trans (lab-stretch-in t)
                         (sym (lab-st-in (<-≤-trans t (subst (a ≤ᴰ_) (sym dr) (≤ᴰ-+ a r₀)))))
      after : ∀ q → lab (stretch S a ++ w′) (a +ᴰ q) ≡ lab (st d S ∷ w) ((a +ᴰ (r₀ +ᴰ c′)) +ᴰ q)
      after q =
        trans (lab-stretch-skip S a w′ q)
        (trans (cong (lab w′) (sym (+ᴰ-identityˡ q)))
        (trans (aw q)
        (sym (trans (cong (lab (st d S ∷ w))
                          (trans (solve 4 (λ a r c q → (a ⊕ (r ⊕ c)) ⊕ q ⊜ (a ⊕ r) ⊕ (c ⊕ q)) refl
                                        a r₀ c′ q)
                                 (cong (_+ᴰ (c′ +ᴰ q)) (sym dr))))
             (trans (lab-st-skip d S w (c′ +ᴰ q))
                    (cong (lab w) (cong (_+ᴰ q) (sym (+ᴰ-identityˡ c′)))))))))

cut : ∀ y a c → a +ᴰ c ≤ᴰ dur y → BudOn y a c
    → Σ[ y′ ∈ Word ] Shrinks y y′ × CutOf y a c y′
cut y a c le bd with 0ᴰ <ᴰ? c
... | no ¬c = y , Shrinks-refl y , subst (λ z → CutOf y a z y) (sym (≮0⇒≡0 ¬c)) (cut-zero y a)
... | yes c>0 = go y a c c>0 le bd

-- removing time from the end of a stretch, and after a prefix

cut-st : ∀ d S w τ k → τ +ᴰ k ≡ ∣ d ∣⁺ → CutOf (st d S ∷ w) τ k (stretch S τ ++ w)
cut-st d S w τ k e = dur′ , before , after
  where
    dur′ : dur (stretch S τ ++ w) +ᴰ k ≡ ∣ d ∣⁺ +ᴰ dur w
    dur′ = trans (cong (_+ᴰ k) (trans (dur-++ (stretch S τ) w) (cong (_+ᴰ dur w) (dur-stretch S τ))))
           (trans (solve 3 (λ t w k → (t ⊕ w) ⊕ k ⊜ (t ⊕ k) ⊕ w) refl τ (dur w) k)
                  (cong (_+ᴰ dur w) e))
    before : ∀ p → p <ᴰ τ → lab (stretch S τ ++ w) p ≡ lab (st d S ∷ w) p
    before p t = trans (lab-stretch-in t)
                       (sym (lab-st-in (<-≤-trans t (subst (τ ≤ᴰ_) e (≤ᴰ-+ τ k)))))
    after : ∀ q → lab (stretch S τ ++ w) (τ +ᴰ q) ≡ lab (st d S ∷ w) ((τ +ᴰ k) +ᴰ q)
    after q = trans (lab-stretch-skip S τ w q)
                    (sym (trans (cong (λ z → lab (st d S ∷ w) (z +ᴰ q)) e) (lab-st-skip d S w q)))

cut-prefix : ∀ u {w w′ a c} → CutOf w a c w′ → CutOf (u ++ w) (dur u +ᴰ a) c (u ++ w′)
cut-prefix []      {w} {w′} {a} {c} cw = subst (λ z → CutOf w z c w′) (sym (+ᴰ-identityˡ a)) cw
cut-prefix (i ∷ u) {w} {w′} {a} {c} cw =
  subst (λ z → CutOf (i ∷ u ++ w) z c (i ∷ u ++ w′)) (sym (+ᴰ-assoc (len i) (dur u) a))
        (cut-cons i (cut-prefix u cw))

------------------------------------------------------------------------
-- Inserting time

InsOf : Word → Carrier → Carrier → Label → Word → Set
InsOf w a c ℓ w′ =
  (dur w′ ≡ dur w +ᴰ c) ×
  (∀ p → p <ᴰ a → lab w′ p ≡ lab w p) ×
  (∀ q → q <ᴰ c → lab w′ (a +ᴰ q) ≡ ℓ) ×
  (∀ q → lab w′ ((a +ᴰ c) +ᴰ q) ≡ lab w (a +ᴰ q))

-- inserting the same time keeps two words fitting

ins-fit : ∀ {x y x′ y′ ℓ ℓ′} → x ⊑ y → a ≤ᴰ dur x → InsOf x a c ℓ x′ → InsOf y a c ℓ′ y′
        → ℓ ≤ˡ ℓ′ → x′ ⊑ y′
ins-fit {a} {c} {x} {y} {x′} {y′} (fits e h) ax (dx , bx , mx , ax′) (dy , by , my , ay′) ℓℓ =
  fits (trans dx (trans (cong (_+ᴰ c) e) (sym dy))) at
  where
    later : ∀ r → (a +ᴰ c) +ᴰ r <ᴰ dur y′ → lab x′ ((a +ᴰ c) +ᴰ r) ≤ˡ lab y′ ((a +ᴰ c) +ᴰ r)
    later r s =
      subst₂ _≤ˡ_ (sym (ax′ r)) (sym (ay′ r))
        (h (a +ᴰ r) (<-+ᴸ-cancel {c}
          (subst₂ _<ᴰ_ (solve 3 (λ a c r → (a ⊕ c) ⊕ r ⊜ c ⊕ (a ⊕ r)) refl a c r)
                       (trans dy (+ᴰ-comm (dur y) c)) s)))
    mid : ∀ q → q <ᴰ c → lab x′ (a +ᴰ q) ≤ˡ lab y′ (a +ᴰ q)
    mid q t = subst₂ _≤ˡ_ (sym (mx q t)) (sym (my q t)) ℓℓ
    past : ∀ q → a +ᴰ q <ᴰ dur y′ → lab x′ (a +ᴰ q) ≤ˡ lab y′ (a +ᴰ q)
    past q s with q <ᴰ? c
    ... | yes t = mid q t
    ... | no ¬t with split (≮⇒≥ ¬t)
    ...   | r , er =
      subst (λ z → lab x′ (a +ᴰ z) ≤ˡ lab y′ (a +ᴰ z)) (sym er)
        (subst (λ z → lab x′ z ≤ˡ lab y′ z) (+ᴰ-assoc a c r)
          (later r (subst (_<ᴰ dur y′) (trans (cong (a +ᴰ_) er) (sym (+ᴰ-assoc a c r))) s)))
    at : ∀ p → p <ᴰ dur y′ → lab x′ p ≤ˡ lab y′ p
    at p s with p <ᴰ? a
    ... | yes t = subst₂ _≤ˡ_ (sym (bx p t)) (sym (by p t))
                    (h p (<-≤-trans t (subst (a ≤ᴰ_) e ax)))
    ... | no ¬t with split (≮⇒≥ ¬t)
    ...   | q , eq = subst (λ z → lab x′ z ≤ˡ lab y′ z) (sym eq) (past q (subst (_<ᴰ dur y′) eq s))

-- inserting time after a first item, and after a prefix

ins-cons : ∀ i {w w′ a′ ℓ} → InsOf w a′ c ℓ w′ → InsOf (i ∷ w) (len i +ᴰ a′) c ℓ (i ∷ w′)
ins-cons {c} i {w} {w′} {a′} {ℓ} (d′ , b′ , m′ , a″) =
  trans (cong (len i +ᴰ_) d′) (sym (+ᴰ-assoc (len i) (dur w) c)) , before , mid , after
  where
    before : ∀ p → p <ᴰ len i +ᴰ a′ → lab (i ∷ w′) p ≡ lab (i ∷ w) p
    before p s = case (p <ᴰ? len i)
      where
        case : Dec (p <ᴰ len i) → lab (i ∷ w′) p ≡ lab (i ∷ w) p
        case (yes t) = trans (lab-here {i} {w′} t) (sym (lab-here {i} {w} t))
        case (no ¬t) = case′ (split (≮⇒≥ ¬t))
          where
          case′ : Σ[ r ∈ Carrier ] p ≡ len i +ᴰ r → lab (i ∷ w′) p ≡ lab (i ∷ w) p
          case′ (r , e) =
            subst (λ z → lab (i ∷ w′) z ≡ lab (i ∷ w) z) (sym e)
              (trans (lab-skip i w′ r)
                (trans (b′ r (<-+ᴸ-cancel (subst (_<ᴰ len i +ᴰ a′) e s))) (sym (lab-skip i w r))))
    mid : ∀ q → q <ᴰ c → lab (i ∷ w′) ((len i +ᴰ a′) +ᴰ q) ≡ ℓ
    mid q t = trans (cong (lab (i ∷ w′)) (+ᴰ-assoc (len i) a′ q))
                    (trans (lab-skip i w′ (a′ +ᴰ q)) (m′ q t))
    after : ∀ q → lab (i ∷ w′) (((len i +ᴰ a′) +ᴰ c) +ᴰ q) ≡ lab (i ∷ w) ((len i +ᴰ a′) +ᴰ q)
    after q =
      trans (cong (lab (i ∷ w′))
                  (solve 4 (λ l a c q → ((l ⊕ a) ⊕ c) ⊕ q ⊜ l ⊕ ((a ⊕ c) ⊕ q)) refl (len i) a′ c q))
      (trans (lab-skip i w′ ((a′ +ᴰ c) +ᴰ q))
      (trans (a″ q)
      (trans (sym (lab-skip i w (a′ +ᴰ q)))
             (cong (lab (i ∷ w)) (sym (+ᴰ-assoc (len i) a′ q))))))

ins-prefix : ∀ u {w w′ a c ℓ} → InsOf w a c ℓ w′ → InsOf (u ++ w) (dur u +ᴰ a) c ℓ (u ++ w′)
ins-prefix []      {w} {w′} {a} {c} {ℓ} iw = subst (λ z → InsOf w z c ℓ w′) (sym (+ᴰ-identityˡ a)) iw
ins-prefix (i ∷ u) {w} {w′} {a} {c} {ℓ} iw =
  subst (λ z → InsOf (i ∷ u ++ w) z c ℓ (i ∷ u ++ w′)) (sym (+ᴰ-assoc (len i) (dur u) a))
        (ins-cons i (ins-prefix u iw))

-- lengthening a stretch at its end

private
  lengthen : D⁺ → Carrier → D⁺
  lengthen d c = pos⁺ (∣ d ∣⁺ +ᴰ c) (<-≤-trans (∣∣⁺-pos d) (≤ᴰ-+ ∣ d ∣⁺ c))

ins-st : ∀ d S w a c → a ≤ᴰ ∣ d ∣⁺ → InsOf (st d S ∷ w) a c (bud S) (st (lengthen d c) S ∷ w)
ins-st d S w a c ad = dur′ , before , mid , after
  where
    d′ = lengthen d c
    dur′ : ∣ d ∣⁺ +ᴰ c +ᴰ dur w ≡ (∣ d ∣⁺ +ᴰ dur w) +ᴰ c
    dur′ = solve 3 (λ d c w → (d ⊕ c) ⊕ w ⊜ (d ⊕ w) ⊕ c) refl ∣ d ∣⁺ c (dur w)
    in′ : ∀ {p} → p <ᴰ ∣ d ∣⁺ → p <ᴰ ∣ d′ ∣⁺
    in′ t = <-≤-+ t
    before : ∀ p → p <ᴰ a → lab (st d′ S ∷ w) p ≡ lab (st d S ∷ w) p
    before p t = trans (lab-st-in {d = d′} (in′ (<-≤-trans t ad))) (sym (lab-st-in (<-≤-trans t ad)))
    mid : ∀ q → q <ᴰ c → lab (st d′ S ∷ w) (a +ᴰ q) ≡ bud S
    mid q t = lab-st-in {d = d′} (<-≤-trans (<-+ᴸ t) (+ᴰ-monoˡ-≤ c ad))
    after : ∀ q → lab (st d′ S ∷ w) ((a +ᴰ c) +ᴰ q) ≡ lab (st d S ∷ w) (a +ᴰ q)
    after q with split ad
    ... | m , dm with q <ᴰ? m
    ...   | yes t =
      trans (lab-st-in {d = d′}
               (subst ((a +ᴰ c) +ᴰ q <ᴰ_)
                      (trans (solve 3 (λ a c m → (a ⊕ c) ⊕ m ⊜ (a ⊕ m) ⊕ c) refl a c m)
                             (cong (_+ᴰ c) (sym dm)))
                      (<-+ᴸ t)))
            (sym (lab-st-in (subst (a +ᴰ q <ᴰ_) (sym dm) (<-+ᴸ t))))
    ...   | no ¬t with split (≮⇒≥ ¬t)
    ...     | r , er =
      subst (λ z → lab (st d′ S ∷ w) ((a +ᴰ c) +ᴰ z) ≡ lab (st d S ∷ w) (a +ᴰ z)) (sym er)
        (trans (cong (lab (st d′ S ∷ w))
                     (trans (solve 4 (λ a c m r → (a ⊕ c) ⊕ (m ⊕ r) ⊜ ((a ⊕ m) ⊕ c) ⊕ r) refl a c m r)
                            (cong (λ z → (z +ᴰ c) +ᴰ r) (sym dm))))
        (trans (lab-st-skip d′ S w r)
        (sym (trans (cong (lab (st d S ∷ w)) (trans (sym (+ᴰ-assoc a m r)) (cong (_+ᴰ r) (sym dm))))
                    (lab-st-skip d S w r)))))

-- inserting time just after an instant inside the stretches of a word
-- lengthens one of them

Ins : Word → Carrier → Carrier → Carrier → Set
Ins y b k c = Σ[ y′ ∈ Word ] Σ[ S ∈ OpSet ] Σ[ q₀ ∈ Carrier ]
              q₀ <ᴰ k × lab y (b +ᴰ q₀) ≡ bud S × Lengthens y y′ × InsOf y (b +ᴰ k) c (bud S) y′

private
  keepL : ∀ i {w w′} → Lengthens w w′ → Lengthens (i ∷ w) (i ∷ w′)
  keepL (op o d) s = op s
  keepL (st d S) s = st ≤ᴰ-refl s

  ins-go : ∀ y b k c → 0ᴰ <ᴰ k → b +ᴰ k ≤ᴰ dur y → BudOn y b k → Ins y b k c
  ins-cons-case : ∀ i w b k c → 0ᴰ <ᴰ k → b +ᴰ k ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) b k
                → Dec (b +ᴰ k ≤ᴰ len i) → Ins (i ∷ w) b k c
  ins-past : ∀ i w b k c → 0ᴰ <ᴰ k → b +ᴰ k ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) b k
           → ¬ (b +ᴰ k ≤ᴰ len i) → Dec (b <ᴰ len i) → Ins (i ∷ w) b k c
  ins-shift : ∀ i w b k c → 0ᴰ <ᴰ k → b +ᴰ k ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) b k
            → Σ[ b′ ∈ Carrier ] b ≡ len i +ᴰ b′ → Ins (i ∷ w) b k c
  ins-in : ∀ i w b k c → 0ᴰ <ᴰ k → b +ᴰ k ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) b k
         → ¬ (b +ᴰ k ≤ᴰ len i) → Σ[ t ∈ Carrier ] len i ≡ b +ᴰ t → Ins (i ∷ w) b k c
  ins-in′ : ∀ i w b k c t → len i ≡ b +ᴰ t → b +ᴰ k ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) b k
          → t <ᴰ k → Σ[ k′ ∈ Carrier ] k ≡ t +ᴰ k′ → Ins (i ∷ w) b k c
  ins-after : ∀ i w b′ k c → 0ᴰ <ᴰ k → (len i +ᴰ b′) +ᴰ k ≤ᴰ dur (i ∷ w)
            → BudOn (i ∷ w) (len i +ᴰ b′) k → Ins (i ∷ w) (len i +ᴰ b′) k c
  ins-across : ∀ i w b t k′ c → 0ᴰ <ᴰ k′ → len i ≡ b +ᴰ t
             → b +ᴰ (t +ᴰ k′) ≤ᴰ dur (i ∷ w) → BudOn (i ∷ w) b (t +ᴰ k′)
             → Ins (i ∷ w) b (t +ᴰ k′) c

  ins-go []      b k c k>0 le bd = ⊥-elim (k>0 (≤ᴰ-trans (≤ᴰ-+ˡ k b) le))
  ins-go (i ∷ w) b k c k>0 le bd = ins-cons-case i w b k c k>0 le bd (b +ᴰ k ≤ᴰ? len i)

  ins-cons-case (op o d) w b k c k>0 le bd (yes s) =
    ⊥-elim (op-not-bud (subst IsBud (trans (cong (lab (op o d ∷ w)) (+ᴰ-identityʳ b))
                                           (lab-here {op o d} {w} (<-≤-trans (<-+ k>0) s)))
                                    (bd 0ᴰ k>0)))
  ins-cons-case (st d S) w b k c k>0 le bd (yes s) =
    st (lengthen d c) S ∷ w , S , 0ᴰ , k>0 ,
    trans (cong (lab (st d S ∷ w)) (+ᴰ-identityʳ b)) (lab-st-in (<-≤-trans (<-+ k>0) s)) ,
    st (≤ᴰ-+ ∣ d ∣⁺ c) (Lengthens-refl w) ,
    ins-st d S w (b +ᴰ k) c s
  ins-cons-case i w b k c k>0 le bd (no ¬s) = ins-past i w b k c k>0 le bd ¬s (b <ᴰ? len i)

  ins-past i w b k c k>0 le bd ¬s (no ¬r) = ins-shift i w b k c k>0 le bd (split (≮⇒≥ ¬r))
  ins-past i w b k c k>0 le bd ¬s (yes r) = ins-in i w b k c k>0 le bd ¬s (split (<⇒≤ r))

  ins-shift i w b k c k>0 le bd (b′ , e) =
    subst (λ z → Ins (i ∷ w) z k c) (sym e)
      (ins-after i w b′ k c k>0 (subst (λ z → z +ᴰ k ≤ᴰ dur (i ∷ w)) e le)
                 (subst (λ z → BudOn (i ∷ w) z k) e bd))

  ins-in i w b k c k>0 le bd ¬s (t , et) =
    ins-in′ i w b k c t et le bd tk (split (<⇒≤ tk))
    where
      tk : t <ᴰ k
      tk = <-+ᴸ-cancel {b} (subst (_<ᴰ b +ᴰ k) et ¬s)

  ins-in′ i w b k c t et le bd tk (k′ , ek) =
    subst (λ z → Ins (i ∷ w) b z c) (sym ek)
      (ins-across i w b t k′ c k′>0 et
         (subst (λ z → b +ᴰ z ≤ᴰ dur (i ∷ w)) ek le)
         (subst (BudOn (i ∷ w) b) ek bd))
    where
      k′>0 : 0ᴰ <ᴰ k′
      k′>0 z = tk (≤ᴰ-reflexive (trans ek (trans (cong (t +ᴰ_) (≤0⇒≡0 z)) (+ᴰ-identityʳ t))))

  ins-after i w b′ k c k>0 le bd with ins-go w b′ k c k>0 le′ bd′
    where
      le′ : b′ +ᴰ k ≤ᴰ dur w
      le′ = +ᴰ-cancelˡ-≤ (len i) (subst (_≤ᴰ len i +ᴰ dur w) (+ᴰ-assoc (len i) b′ k) le)
      bd′ : BudOn w b′ k
      bd′ q s = subst IsBud (trans (cong (lab (i ∷ w)) (+ᴰ-assoc (len i) b′ q))
                                   (lab-skip i w (b′ +ᴰ q)))
                            (bd q s)
  ... | w′ , S , q₀ , q₀<k , eq , lw , iw =
    i ∷ w′ , S , q₀ , q₀<k ,
    trans (cong (lab (i ∷ w)) (+ᴰ-assoc (len i) b′ q₀)) (trans (lab-skip i w (b′ +ᴰ q₀)) eq) ,
    keepL i lw ,
    subst (λ z → InsOf (i ∷ w) z c (bud S) (i ∷ w′)) (sym (+ᴰ-assoc (len i) b′ k)) (ins-cons i iw)

  ins-across i w b t k′ c k′>0 et le bd with ins-go w 0ᴰ k′ c k′>0 le′ bd′
    where
      le′ : 0ᴰ +ᴰ k′ ≤ᴰ dur w
      le′ = subst (_≤ᴰ dur w) (sym (+ᴰ-identityˡ k′))
              (+ᴰ-cancelˡ-≤ (len i)
                (subst (_≤ᴰ len i +ᴰ dur w)
                       (trans (sym (+ᴰ-assoc b t k′)) (cong (_+ᴰ k′) (sym et))) le))
      bd′ : BudOn w 0ᴰ k′
      bd′ q s = subst IsBud
                  (trans (cong (lab (i ∷ w))
                               (trans (sym (+ᴰ-assoc b t q)) (cong (_+ᴰ q) (sym et))))
                  (trans (lab-skip i w q) (cong (lab w) (sym (+ᴰ-identityˡ q)))))
                  (bd (t +ᴰ q) (<-+ᴸ s))
  ... | w′ , S , q₀ , q₀<k′ , eq , lw , iw =
    i ∷ w′ , S , t +ᴰ q₀ , <-+ᴸ q₀<k′ ,
    trans (cong (lab (i ∷ w)) (trans (sym (+ᴰ-assoc b t q₀)) (cong (_+ᴰ q₀) (sym et))))
          (trans (lab-skip i w q₀) (trans (cong (lab w) (sym (+ᴰ-identityˡ q₀))) eq)) ,
    keepL i lw ,
    subst (λ z → InsOf (i ∷ w) z c (bud S) (i ∷ w′))
          (trans (cong (len i +ᴰ_) (+ᴰ-identityˡ k′))
                 (trans (cong (_+ᴰ k′) et) (+ᴰ-assoc b t k′)))
          (ins-cons i iw)

insert : ∀ y b k c → 0ᴰ <ᴰ k → b +ᴰ k ≤ᴰ dur y → BudOn y b k → Ins y b k c
insert = ins-go

------------------------------------------------------------------------
-- Fitting into a set closed under resizing

private
  -- a label above a stretch's label is a stretch's label

  bud-above : ∀ {x y S p} → x ⊑ y → p <ᴰ dur y → lab x p ≡ bud S → IsBud (lab y p)
  bud-above (fits _ h) s e = bud-≤ˡ (subst (_≤ˡ _) e (h _ s))

  -- the labels inside the stretch that follows a prefix

  lab-in : ∀ u d S w {q} → q <ᴰ ∣ d ∣⁺ → lab (u ++ (st d S ∷ w)) (dur u +ᴰ q) ≡ bud S
  lab-in u d S w s = trans (lab-++ʳ′ u (st d S ∷ w) _) (lab-st-in s)

  dur-in : ∀ u d S w {q} → q <ᴰ ∣ d ∣⁺ → dur u +ᴰ q <ᴰ dur (u ++ (st d S ∷ w))
  dur-in u d S w s =
    subst (_ <ᴰ_) (sym (dur-++ u (st d S ∷ w)))
      (<-≤-trans (<-+ᴸ s) (+ᴰ-monoʳ-≤ (dur u) (≤ᴰ-+ ∣ d ∣⁺ (dur w))))

-- a word that fits a member of a set closed under shrinking still fits
-- one when some of its stretches are shortened

shrink-fit : (Y : Lang) → (∀ {y y′} → Y y → Shrinks y y′ → Y y′)
           → ∀ u {x h} → Shrinks x h → ∀ {y} → Y y → u ++ x ⊑ y
           → Σ[ y′ ∈ Word ] Y y′ × u ++ h ⊑ y′
shrink-fit Y closed u [] y∈ xy = _ , y∈ , xy
shrink-fit Y closed u {op o d ∷ w} {op o d ∷ h} (op s) {y} y∈ xy
  with shrink-fit Y closed (u ++ op o d ∷ []) s y∈
         (subst (_⊑ y) (sym (++-assoc u (op o d ∷ []) w)) xy)
... | y′ , y′∈ , fit = y′ , y′∈ , subst (_⊑ y′) (++-assoc u (op o d ∷ []) h) fit
shrink-fit Y closed u {st d S ∷ w} {.(stretch S τ ++ h)} (st {τ = τ} {w′ = h} r s) {y} y∈ xy
  with split r
... | k , dk with cut y (dur u +ᴰ τ) k le bd
  where
    xy-dur = ⊑-dur xy
    le : (dur u +ᴰ τ) +ᴰ k ≤ᴰ dur y
    le = subst (_≤ᴰ dur y)
           (trans (cong (dur u +ᴰ_) dk) (sym (+ᴰ-assoc (dur u) τ k)))
           (subst (dur u +ᴰ ∣ d ∣⁺ ≤ᴰ_)
                  (trans (+ᴰ-assoc (dur u) ∣ d ∣⁺ (dur w))
                         (trans (sym (dur-++ u (st d S ∷ w))) xy-dur))
                  (≤ᴰ-+ (dur u +ᴰ ∣ d ∣⁺) (dur w)))
    bd : BudOn y (dur u +ᴰ τ) k
    bd q t = bud-above xy
               (subst (_<ᴰ dur y) (sym (+ᴰ-assoc (dur u) τ q))
                 (subst (_ <ᴰ_) xy-dur
                   (dur-in u d S w (subst ((τ +ᴰ q) <ᴰ_) (sym dk) (<-+ᴸ t)))))
               (trans (cong (lab (u ++ (st d S ∷ w))) (+ᴰ-assoc (dur u) τ q))
                      (lab-in u d S w (subst ((τ +ᴰ q) <ᴰ_) (sym dk) (<-+ᴸ t))))
...   | y₁ , sy , cy
  with shrink-fit Y closed (u ++ stretch S τ) s (closed y∈ sy)
         (subst (_⊑ y₁) (sym (++-assoc u (stretch S τ) w))
           (cut-fit xy (cut-prefix u (cut-st d S w τ k (sym dk))) cy))
...     | y′ , y′∈ , fit = y′ , y′∈ , subst (_⊑ y′) (++-assoc u (stretch S τ) h) fit

-- a word that fits a member of a set closed under lengthening still
-- fits one when some of its stretches are lengthened

lengthen-fit : (Y : Lang) → (∀ {y y′} → Y y → Lengthens y y′ → Y y′)
             → ∀ u {x h} → Lengthens x h → ∀ {y} → Y y → u ++ x ⊑ y
             → Σ[ y′ ∈ Word ] Y y′ × u ++ h ⊑ y′
lengthen-fit Y closed u [] y∈ xy = _ , y∈ , xy
lengthen-fit Y closed u {op o d ∷ w} {op o d ∷ h} (op s) {y} y∈ xy
  with lengthen-fit Y closed (u ++ op o d ∷ []) s y∈
         (subst (_⊑ y) (sym (++-assoc u (op o d ∷ []) w)) xy)
... | y′ , y′∈ , fit = y′ , y′∈ , subst (_⊑ y′) (++-assoc u (op o d ∷ []) h) fit
lengthen-fit Y closed u {st d S ∷ w} {st d′ S ∷ h} (st r s) {y} y∈ xy
  with split r
... | c , dc with insert y (dur u) ∣ d ∣⁺ c (∣∣⁺-pos d) le bd
  where
    xy-dur = ⊑-dur xy
    le : dur u +ᴰ ∣ d ∣⁺ ≤ᴰ dur y
    le = subst (dur u +ᴰ ∣ d ∣⁺ ≤ᴰ_)
           (trans (+ᴰ-assoc (dur u) ∣ d ∣⁺ (dur w))
                  (trans (sym (dur-++ u (st d S ∷ w))) xy-dur))
           (≤ᴰ-+ (dur u +ᴰ ∣ d ∣⁺) (dur w))
    bd : BudOn y (dur u) ∣ d ∣⁺
    bd q t = bud-above xy (subst (_ <ᴰ_) xy-dur (dur-in u d S w t)) (lab-in u d S w t)
...   | y₁ , S′ , q₀ , q₀<d , eq , ly , iy
  with lengthen-fit Y closed (u ++ st d′ S ∷ []) s (closed y∈ ly)
         (subst (_⊑ y₁) (sym (++-assoc u (st d′ S ∷ []) w))
           (ins-fit xy ax ix iy ℓℓ))
  where
    ax : dur u +ᴰ ∣ d ∣⁺ ≤ᴰ dur (u ++ (st d S ∷ w))
    ax = subst (dur u +ᴰ ∣ d ∣⁺ ≤ᴰ_)
           (trans (+ᴰ-assoc (dur u) ∣ d ∣⁺ (dur w)) (sym (dur-++ u (st d S ∷ w))))
           (≤ᴰ-+ (dur u +ᴰ ∣ d ∣⁺) (dur w))
    d′≡ : st (lengthen d c) S ∷ w ≡ st d′ S ∷ w
    d′≡ = cong (λ z → st z S ∷ w) (∣∣⁺-inj (sym dc))
    ix : InsOf (u ++ (st d S ∷ w)) (dur u +ᴰ ∣ d ∣⁺) c (bud S) (u ++ (st d′ S ∷ w))
    ix = subst (λ z → InsOf (u ++ (st d S ∷ w)) (dur u +ᴰ ∣ d ∣⁺) c (bud S) (u ++ z)) d′≡
           (ins-prefix u (ins-st d S w ∣ d ∣⁺ c ≤ᴰ-refl))
    ℓℓ : bud S ≤ˡ bud S′
    ℓℓ = subst₂ _≤ˡ_ (lab-in u d S w q₀<d) eq
           (⊑-lab xy (dur u +ᴰ q₀) (subst (_ <ᴰ_) (⊑-dur xy) (dur-in u d S w q₀<d)))
...     | y′ , y′∈ , fit = y′ , y′∈ , subst (_⊑ y′) (++-assoc u (st d′ S ∷ []) h) fit
