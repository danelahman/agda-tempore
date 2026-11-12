------------------------------------------------------------------------
-- Finite expressions as grades, in each instance.                    --
--                                                                    --
-- The elements are finite expressions with at least one word,        --
-- compared by the runs they denote (`Exact.Lift`), decided by the    --
-- reader (`Exact.Finite`). Sequencing, union, the empty word and the --
-- unrestricted stretch are the operations; a delay is graded by the  --
-- hull on each side: a wait of at most its length in the upper       --
-- instance, of at least its length in the lower one, the delay zero  --
-- being the empty word.                                              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus

module Grades.Exact.Finite.Grades
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Bool.Base using (Bool; true; false; _∧_) renaming (T to IsTrue)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)
open import Data.List.Base using (List; []; _∷_; _++_; cartesianProductWith)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness; map′)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Hi; fin; ∞; ⁺; ⁻; ⊑⇒≤; ≤⇒⁺⊑⁺; ≤⇒⁻⊑⁻; _⊑ʰ_)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_)

open import Grades.Base using (Grade)
open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective using (_⊑_; lab-∙; fits)
open import Grades.Exact.Lift T Op n code code-injective as L
  using (Lang; 𝟏ᴸ; _·ᴸ_; _∪ᴸ_; ≡ˡ⇒⊑; ⊆⇒≾)
open import Grades.Exact.Expression T Op n code code-injective running
open import Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos

------------------------------------------------------------------------
-- Proper expressions

record Proper′ (s : Instance) : Set where
  constructor ⌜_⌝
  field
    expr     : Expr s
    {proper} : Proper expr

open Proper′ public

private
  ∧-intro : ∀ {a b} → IsTrue a → IsTrue b → IsTrue (a ∧ b)
  ∧-intro {true} _ t = t

  ∧-l : ∀ {a b} → IsTrue (a ∧ b) → IsTrue a
  ∧-l {true} _ = tt

  ∧-r : ∀ {a b} → IsTrue (a ∧ b) → IsTrue b
  ∧-r {true} t = t

  ne-++ : ∀ {A : Set} (xs ys : List A) → IsTrue (nonEmpty xs) → IsTrue (nonEmpty (xs ++ ys))
  ne-++ (_ ∷ _) ys _ = tt

  ne-cp : ∀ {A : Set} (f : A → A → A) (xs ys : List A) → IsTrue (nonEmpty xs) → IsTrue (nonEmpty ys)
        → IsTrue (nonEmpty (cartesianProductWith f xs ys))
  ne-cp f (x ∷ xs) (y ∷ ys) _ _ = tt

  proper-∣ : ∀ {s} (e f : Expr s) → Proper e → Proper f → Proper (e ∣ f)
  proper-∣ e f p q =
    ∧-intro (∧-intro {starFree e} (∧-l p) (∧-l q)) (ne-++ (words e) (words f) (∧-r {starFree e} p))

  proper-· : ∀ {s} (e f : Expr s) → Proper e → Proper f → Proper (e · f)
  proper-· e f p q =
    ∧-intro (∧-intro {starFree e} (∧-l p) (∧-l q))
            (ne-cp _++_ (words e) (words f) (∧-r {starFree e} p) (∧-r {starFree f} q))

  -- a closed upper end has a word, and so has every lower end
  proper-strᵁ : ∀ S τ → Proper (str {upper} S (fin (τ ∣ᶜ ⁺)))
  proper-strᵁ S τ with 0ᴰ <ᴰ? τ
  ... | yes _ = tt
  ... | no _  = tt

  proper-strᴸ : ∀ S c → Proper (str {lower} S c)
  proper-strᴸ S (p ∣ᶜ side) with 0ᴰ <ᴰ? p
  ... | yes _ = tt
  ... | no _ with side
  ...   | ⁺ = tt
  ...   | ⁻ = tt

infixl 7 _·ᵉ_
infixl 6 _∣ᵉ_

_·ᵉ_ _∣ᵉ_ : ∀ {s} → Proper′ s → Proper′ s → Proper′ s
⌜ e ⌝ {p} ·ᵉ ⌜ f ⌝ {q} = ⌜ e · f ⌝ {proper-· e f p q}
⌜ e ⌝ {p} ∣ᵉ ⌜ f ⌝ {q} = ⌜ e ∣ f ⌝ {proper-∣ e f p q}

εᵉ : ∀ {s} → Proper′ s
εᵉ = ⌜ ε ⌝

-- the order

infix 4 _≾ᵉ_

_≾ᵉ_ : ∀ {s} → Proper′ s → Proper′ s → Set
c ≾ᵉ d = ⟦ expr c ⟧ L.≾ ⟦ expr d ⟧

_≾ᵉ?_ : ∀ {s} (c d : Proper′ s) → Dec (c ≾ᵉ d)
c ≾ᵉ? d = (expr c ≾? expr d) (proper-finite (expr c) (proper c)) (proper-finite (expr d) (proper d))

------------------------------------------------------------------------
-- Stretches split and joined

private
  ∙⊑++ : ∀ x y → x ∙ y ⊑ x ++ y
  ∙⊑++ x y = ≡ˡ⇒⊑ (trans (dur-∙ x y) (sym (dur-++ x y)))
                  (λ p _ → lab-∙ x y p)

  ++⊑∙ : ∀ x y → x ++ y ⊑ x ∙ y
  ++⊑∙ x y = ≡ˡ⇒⊑ (trans (dur-++ x y) (sym (dur-∙ x y)))
                  (λ p _ → sym (lab-∙ x y p))

  split⊑ : ∀ S a b → stretch S (a +ᴰ b) ⊑ stretch S a ++ stretch S b
  split⊑ S a b = subst (_⊑ stretch S a ++ stretch S b) (sym (stretch-hom S a b)) (∙⊑++ (stretch S a) (stretch S b))

  join⊑ : ∀ S a b → stretch S a ++ stretch S b ⊑ stretch S (a +ᴰ b)
  join⊑ S a b = subst (stretch S a ++ stretch S b ⊑_) (sym (stretch-hom S a b)) (++⊑∙ (stretch S a) (stretch S b))

------------------------------------------------------------------------
-- The hull of a delay

-- upper: a wait of at most the delay

waitᵁ : Carrier → Proper′ upper
waitᵁ τ = ⌜ str none (fin (τ ∣ᶜ ⁺)) ⌝ {proper-strᵁ none τ}

-- lower: a wait of at least the delay, the delay zero being nothing

at-least′ : (τ : Carrier) → Dec (0ᴰ <ᴰ τ) → Proper′ lower
at-least′ τ (yes _) = ⌜ str none (τ ∣ᶜ ⁻) ⌝ {proper-strᴸ none (τ ∣ᶜ ⁻)}
at-least′ τ (no _)  = εᵉ

waitᴸ : Carrier → Proper′ lower
waitᴸ τ = at-least′ τ (0ᴰ <ᴰ? τ)

private
  stretch-0 : ∀ S → stretch S 0ᴰ ≡ []
  stretch-0 S = stretch-zero S 0ᴰ (λ q → <⇒≢ q refl)

  ≤0 : ∀ {τ} → fin (τ ∣ᶜ ⁺) ⊑ʰ fin (0ᴰ ∣ᶜ ⁺) → τ ≡ 0ᴰ
  ≤0 r = ≤0⇒≡0 (⊑⇒≤ r)

  -- a wait of at most `m + n` is one of at most `m` then one of at most `n`
  upper-split : ∀ m n → strᴸ {upper} none (fin ((m +ᴰ n) ∣ᶜ ⁺)) L.≈ (strᴸ {upper} none (fin (m ∣ᶜ ⁺)) ·ᴸ strᴸ {upper} none (fin (n ∣ᶜ ⁺)))
  upper-split m n = to , from
    where
      parts : ∀ τ → τ ≤ᴰ m +ᴰ n → Σ[ a ∈ Carrier ] Σ[ b ∈ Carrier ] a ≤ᴰ m × b ≤ᴰ n × a +ᴰ b ≡ τ
      parts τ r with τ ≤ᴰ? m
      ... | yes τm = τ , 0ᴰ , τm , 0ᴰ-least n , +ᴰ-identityʳ τ
      ... | no ¬τm = m , τ ∸ᴰ m , ≤ᴰ-refl , ∸-≤-+ r , +-∸ (<⇒≤ ¬τm)
      to : strᴸ none (fin ((m +ᴰ n) ∣ᶜ ⁺)) L.≾ (strᴸ none (fin (m ∣ᶜ ⁺)) ·ᴸ strᴸ none (fin (n ∣ᶜ ⁺)))
      to x (τ , r , refl) with parts τ (⊑⇒≤ r)
      ... | a , b , am , bn , e =
        stretch none a ++ stretch none b ,
        (stretch none a , stretch none b , refl , (a , ≤⇒⁺⊑⁺ am , refl) , (b , ≤⇒⁺⊑⁺ bn , refl)) ,
        subst (λ z → stretch none z ⊑ stretch none a ++ stretch none b) e (split⊑ none a b)
      from : (strᴸ none (fin (m ∣ᶜ ⁺)) ·ᴸ strᴸ none (fin (n ∣ᶜ ⁺))) L.≾ strᴸ none (fin ((m +ᴰ n) ∣ᶜ ⁺))
      from x (_ , _ , refl , (a , ra , refl) , (b , rb , refl)) =
        stretch none (a +ᴰ b) , (a +ᴰ b , ≤⇒⁺⊑⁺ (+ᴰ-mono-≤ (⊑⇒≤ ra) (⊑⇒≤ rb)) , refl) , join⊑ none a b

  -- a wait of at least `m + n` is one of at least `m` then one of at least `n`
  lower-split : ∀ m n → strᴸ {lower} none ((m +ᴰ n) ∣ᶜ ⁻) L.≈ (strᴸ {lower} none (m ∣ᶜ ⁻) ·ᴸ strᴸ {lower} none (n ∣ᶜ ⁻))
  lower-split m n = to , from
    where
      to : strᴸ none ((m +ᴰ n) ∣ᶜ ⁻) L.≾ (strᴸ none (m ∣ᶜ ⁻) ·ᴸ strᴸ none (n ∣ᶜ ⁻))
      to x (τ , r , refl) =
        stretch none m ++ stretch none (τ ∸ᴰ m) ,
        (stretch none m , stretch none (τ ∸ᴰ m) , refl , (m , ≤⇒⁻⊑⁻ ≤ᴰ-refl , refl) ,
         (τ ∸ᴰ m , ≤⇒⁻⊑⁻ (+-≤-∸ m≤τ (⊑⇒≤ r)) , refl)) ,
        subst (λ z → stretch none z ⊑ stretch none m ++ stretch none (τ ∸ᴰ m)) (+-∸ m≤τ) (split⊑ none m (τ ∸ᴰ m))
        where
          m≤τ : m ≤ᴰ τ
          m≤τ = ≤ᴰ-trans (≤ᴰ-+ m n) (⊑⇒≤ r)
      from : (strᴸ none (m ∣ᶜ ⁻) ·ᴸ strᴸ none (n ∣ᶜ ⁻)) L.≾ strᴸ none ((m +ᴰ n) ∣ᶜ ⁻)
      from x (_ , _ , refl , (a , ra , refl) , (b , rb , refl)) =
        stretch none (a +ᴰ b) , (a +ᴰ b , ≤⇒⁻⊑⁻ (+ᴰ-mono-≤ (⊑⇒≤ ra) (⊑⇒≤ rb)) , refl) , join⊑ none a b

------------------------------------------------------------------------
-- The grades
--
-- A grade's order is the reader's decision: `c ≾ᴳ d` holds when every
-- run of `c` fits a run of `d`. It is the order of the
-- denotations, read through the decision, and so proof-irrelevant.

private
  ≈-cong : ∀ {X Y Z : Lang} → X L.≈ Y → Y L.≈ Z → X L.≈ Z
  ≈-cong (a , b) (c , d) = L.≾-trans a c , L.≾-trans d b

  ≈-refl : ∀ {X : Lang} → X L.≈ X
  ≈-refl = L.≾-refl , L.≾-refl

  ≈-sym : ∀ {X Y : Lang} → X L.≈ Y → Y L.≈ X
  ≈-sym (a , b) = b , a

  -- the unrestricted stretches cover every run
  any⊆ᵁ : L.anyᴸ L.⊆ᴸ strᴸ {upper} all ∞
  any⊆ᵁ w (τ , e) = τ , tt , e

  any⊆ᴸ : L.anyᴸ L.⊆ᴸ strᴸ {lower} all (0ᴰ ∣ᶜ ⁻)
  any⊆ᴸ w (τ , e) = τ , ≤⇒⁻⊑⁻ (0ᴰ-least τ) , e

  -- a delay zero, read as at most zero, is nothing
  upper-zero : strᴸ {upper} none (fin (0ᴰ ∣ᶜ ⁺)) L.≈ 𝟏ᴸ
  upper-zero =
    ⊆⇒≾ (λ { x (τ , r , refl) → trans (cong (stretch none) (≤0 r)) (stretch-0 none) }) ,
    ⊆⇒≾ (λ { x refl → 0ᴰ , ≤⇒⁺⊑⁺ ≤ᴰ-refl , sym (stretch-0 none) })

infix 4 _≾ᴳ_

record _≾ᴳ_ {s} (c d : Proper′ s) : Set where
  constructor decided
  field
    by-reader : True (c ≾ᵉ? d)

open _≾ᴳ_ public

private
  T-irr : ∀ {b} → (p q : IsTrue b) → p ≡ q
  T-irr {true} tt tt = refl

  ≾ᴳ-irr : ∀ {s} {c d : Proper′ s} → (p q : c ≾ᴳ d) → p ≡ q
  ≾ᴳ-irr (decided p) (decided q) = cong decided (T-irr p q)

  ↑ : ∀ {s} (c d : Proper′ s) → c ≾ᵉ d → c ≾ᴳ d
  ↑ c d p = decided (fromWitness {a? = c ≾ᵉ? d} p)

  ↓ : ∀ {s} (c d : Proper′ s) → c ≾ᴳ d → c ≾ᵉ d
  ↓ c d p = toWitness {a? = c ≾ᵉ? d} (by-reader p)

  ↑² : ∀ {s} (c d : Proper′ s) → c ≾ᵉ d × d ≾ᵉ c → c ≾ᴳ d × d ≾ᴳ c
  ↑² c d (p , q) = ↑ c d p , ↑ d c q

  _≾ᴳ?_ : ∀ {s} (c d : Proper′ s) → Dec (c ≾ᴳ d)
  c ≾ᴳ? d = map′ (↑ c d) (↓ c d) (c ≾ᵉ? d)

module Common (s : Instance) where

  ·-identityˡᵉ : ∀ (c : Proper′ s) → (εᵉ ·ᵉ c) ≾ᴳ c × c ≾ᴳ (εᵉ ·ᵉ c)
  ·-identityˡᵉ c = ↑² (εᵉ ·ᵉ c) c (L.·-identityˡ ⟦ expr c ⟧)

  ·-identityʳᵉ : ∀ (c : Proper′ s) → (c ·ᵉ εᵉ) ≾ᴳ c × c ≾ᴳ (c ·ᵉ εᵉ)
  ·-identityʳᵉ c = ↑² (c ·ᵉ εᵉ) c (L.·-identityʳ ⟦ expr c ⟧)

  ·-assocᵉ : ∀ (c d e : Proper′ s) → ((c ·ᵉ d) ·ᵉ e) ≾ᴳ (c ·ᵉ (d ·ᵉ e)) × (c ·ᵉ (d ·ᵉ e)) ≾ᴳ ((c ·ᵉ d) ·ᵉ e)
  ·-assocᵉ c d e = ↑² ((c ·ᵉ d) ·ᵉ e) (c ·ᵉ (d ·ᵉ e)) (L.·-assoc ⟦ expr c ⟧ ⟦ expr d ⟧ ⟦ expr e ⟧)

  zero-ˡ : ∀ {c d : Proper′ s} → (c ·ᵉ d) ≾ᴳ εᵉ → c ≾ᴳ εᵉ
  zero-ˡ {c} {d} p = ↑ c εᵉ (L.zero-productˡ (proper-run (expr d) (proper d)) (↓ (c ·ᵉ d) εᵉ p))

  zero-ʳ : ∀ {c d : Proper′ s} → (c ·ᵉ d) ≾ᴳ εᵉ → d ≾ᴳ εᵉ
  zero-ʳ {c} {d} p = ↑ d εᵉ (L.zero-productʳ (proper-run (expr c) (proper c)) (↓ (c ·ᵉ d) εᵉ p))

  refl-ᴳ : ∀ {c : Proper′ s} → c ≾ᴳ c
  refl-ᴳ {c} = ↑ c c L.≾-refl

  trans-ᴳ : ∀ {c d e : Proper′ s} → c ≾ᴳ d → d ≾ᴳ e → c ≾ᴳ e
  trans-ᴳ {c} {d} {e} p q = ↑ c e (L.≾-trans (↓ c d p) (↓ d e q))

  ubˡ-ᴳ : ∀ (c d : Proper′ s) → c ≾ᴳ (c ∣ᵉ d)
  ubˡ-ᴳ c d = ↑ c (c ∣ᵉ d) (L.∪-ubˡ ⟦ expr c ⟧ ⟦ expr d ⟧)

  ubʳ-ᴳ : ∀ (c d : Proper′ s) → d ≾ᴳ (c ∣ᵉ d)
  ubʳ-ᴳ c d = ↑ d (c ∣ᵉ d) (L.∪-ubʳ ⟦ expr c ⟧ ⟦ expr d ⟧)

  lub-ᴳ : ∀ {c d e : Proper′ s} → c ≾ᴳ e → d ≾ᴳ e → (c ∣ᵉ d) ≾ᴳ e
  lub-ᴳ {c} {d} {e} p q = ↑ (c ∣ᵉ d) e (L.∪-lub (↓ c e p) (↓ d e q))

  monoˡ-ᴳ : ∀ {c d e : Proper′ s} → d ≾ᴳ e → (d ·ᵉ c) ≾ᴳ (e ·ᵉ c)
  monoˡ-ᴳ {c} {d} {e} p = ↑ (d ·ᵉ c) (e ·ᵉ c) (L.·-mono (↓ d e p) L.≾-refl)

  monoʳ-ᴳ : ∀ {c d e : Proper′ s} → d ≾ᴳ e → (c ·ᵉ d) ≾ᴳ (c ·ᵉ e)
  monoʳ-ᴳ {c} {d} {e} p = ↑ (c ·ᵉ d) (c ·ᵉ e) (L.·-mono L.≾-refl (↓ d e p))

  distribˡ-ᴳ : ∀ (c d e : Proper′ s) → (c ·ᵉ (d ∣ᵉ e)) ≾ᴳ ((c ·ᵉ d) ∣ᵉ (c ·ᵉ e))
  distribˡ-ᴳ c d e = ↑ (c ·ᵉ (d ∣ᵉ e)) ((c ·ᵉ d) ∣ᵉ (c ·ᵉ e)) (L.·-distribˡ ⟦ expr c ⟧ ⟦ expr d ⟧ ⟦ expr e ⟧)

  distribʳ-ᴳ : ∀ (c d e : Proper′ s) → ((d ∣ᵉ e) ·ᵉ c) ≾ᴳ ((d ·ᵉ c) ∣ᵉ (e ·ᵉ c))
  distribʳ-ᴳ c d e = ↑ ((d ∣ᵉ e) ·ᵉ c) ((d ·ᵉ c) ∣ᵉ (e ·ᵉ c)) (L.·-distribʳ ⟦ expr c ⟧ ⟦ expr d ⟧ ⟦ expr e ⟧)

open Common

-- the upper instance: upper-bound grades

upperᵍ : Grade D
upperᵍ = record
  { Carrier = Proper′ upper
  ; _·_     = _·ᵉ_
  ; 𝟏       = εᵉ
  ; _≾_     = _≾ᴳ_
  ; ⊤       = ⌜ str all ∞ ⌝
  ; _⊔_     = _∣ᵉ_
  ; ι       = waitᵁ
  ; ·-identityˡ = ·-identityˡᵉ upper
  ; ·-identityʳ = ·-identityʳᵉ upper
  ; ·-assoc     = ·-assocᵉ upper
  ; ≾-refl       = λ {c} → refl-ᴳ upper {c}
  ; ≾-trans      = λ {c} {d} {e} → trans-ᴳ upper {c} {d} {e}
  ; ≾-irrelevant = ≾ᴳ-irr
  ; _≾?_         = _≾ᴳ?_
  ; ≾-⊤     = λ c → ↑ c (⌜ str all ∞ ⌝) (L.≾-trans (L.≾-any ⟦ expr c ⟧) (⊆⇒≾ any⊆ᵁ))
  ; ⊔-ubˡ   = ubˡ-ᴳ upper
  ; ⊔-ubʳ   = ubʳ-ᴳ upper
  ; ⊔-lub   = λ {c} {d} {e} → lub-ᴳ upper {c} {d} {e}
  ; ·-monoˡ-≾ = λ {c} {x} {y} → monoˡ-ᴳ upper {c} {x} {y}
  ; ·-monoʳ-≾ = λ {c} {x} {y} → monoʳ-ᴳ upper {c} {x} {y}
  ; ·-distribˡ-⊔-≾ = distribˡ-ᴳ upper
  ; ·-distribʳ-⊔-≾ = distribʳ-ᴳ upper
  ; ≾-zero-productˡ = λ {c} {d} → zero-ˡ upper {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → zero-ʳ upper {c} {d}
  ; ι-zero = ↑² (waitᵁ 0ᴰ) εᵉ upper-zero
  ; ι-plus = λ {m} {n} → ↑² (waitᵁ (m +ᴰ n)) (waitᵁ m ·ᵉ waitᵁ n) (upper-split m n)
  }

-- the lower instance: lower-bound grades

private
  lower-hom : ∀ m n (a : Dec (0ᴰ <ᴰ m)) (b : Dec (0ᴰ <ᴰ n)) (c : Dec (0ᴰ <ᴰ m +ᴰ n))
            → ⟦ expr (at-least′ (m +ᴰ n) c) ⟧ L.≈ (⟦ expr (at-least′ m a) ⟧ ·ᴸ ⟦ expr (at-least′ n b) ⟧)
  lower-hom m n (yes _) (yes _) (yes _) = lower-split m n
  lower-hom m n (yes p) (no ¬q) (yes _) =
    ≈-cong (subst (λ z → strᴸ {lower} none (z ∣ᶜ ⁻) L.≈ strᴸ {lower} none (m ∣ᶜ ⁻))
                  (sym (trans (cong (m +ᴰ_) (≮0⇒≡0 ¬q)) (+ᴰ-identityʳ m))) ≈-refl)
           (≈-sym (L.·-identityʳ _))
  lower-hom m n (no ¬p) (yes q) (yes _) =
    ≈-cong (subst (λ z → strᴸ {lower} none (z ∣ᶜ ⁻) L.≈ strᴸ {lower} none (n ∣ᶜ ⁻))
                  (sym (trans (cong (_+ᴰ n) (≮0⇒≡0 ¬p)) (+ᴰ-identityˡ n))) ≈-refl)
           (≈-sym (L.·-identityˡ _))
  lower-hom m n (no ¬p) (no ¬q) (yes r) =
    ⊥-elim (<⇒≢ r (sym (trans (cong₂ _+ᴰ_ (≮0⇒≡0 ¬p) (≮0⇒≡0 ¬q)) (+ᴰ-identityˡ 0ᴰ))))
  lower-hom m n (no _) (no _) (no _) = ≈-sym (L.·-identityˡ 𝟏ᴸ)
  lower-hom m n (yes p) _ (no ¬r) = ⊥-elim (¬r (<-≤-trans p (≤ᴰ-+ m n)))
  lower-hom m n (no _) (yes q) (no ¬r) = ⊥-elim (¬r (<-≤-trans q (≤ᴰ-+ˡ n m)))

  lower-zero : (c : Dec (0ᴰ <ᴰ 0ᴰ)) → ⟦ expr (at-least′ 0ᴰ c) ⟧ L.≈ 𝟏ᴸ
  lower-zero (yes p) = ⊥-elim (<⇒≢ p refl)
  lower-zero (no _)  = ≈-refl

lowerᵍ : Grade D
lowerᵍ = record
  { Carrier = Proper′ lower
  ; _·_     = _·ᵉ_
  ; 𝟏       = εᵉ
  ; _≾_     = _≾ᴳ_
  ; ⊤       = ⌜ str all (0ᴰ ∣ᶜ ⁻) ⌝ {proper-strᴸ all (0ᴰ ∣ᶜ ⁻)}
  ; _⊔_     = _∣ᵉ_
  ; ι       = waitᴸ
  ; ·-identityˡ = ·-identityˡᵉ lower
  ; ·-identityʳ = ·-identityʳᵉ lower
  ; ·-assoc     = ·-assocᵉ lower
  ; ≾-refl       = λ {c} → refl-ᴳ lower {c}
  ; ≾-trans      = λ {c} {d} {e} → trans-ᴳ lower {c} {d} {e}
  ; ≾-irrelevant = ≾ᴳ-irr
  ; _≾?_         = _≾ᴳ?_
  ; ≾-⊤     = λ c → ↑ c (⌜ str all (0ᴰ ∣ᶜ ⁻) ⌝ {proper-strᴸ all (0ᴰ ∣ᶜ ⁻)}) (L.≾-trans (L.≾-any ⟦ expr c ⟧) (⊆⇒≾ any⊆ᴸ))
  ; ⊔-ubˡ   = ubˡ-ᴳ lower
  ; ⊔-ubʳ   = ubʳ-ᴳ lower
  ; ⊔-lub   = λ {c} {d} {e} → lub-ᴳ lower {c} {d} {e}
  ; ·-monoˡ-≾ = λ {c} {x} {y} → monoˡ-ᴳ lower {c} {x} {y}
  ; ·-monoʳ-≾ = λ {c} {x} {y} → monoʳ-ᴳ lower {c} {x} {y}
  ; ·-distribˡ-⊔-≾ = distribˡ-ᴳ lower
  ; ·-distribʳ-⊔-≾ = distribʳ-ᴳ lower
  ; ≾-zero-productˡ = λ {c} {d} → zero-ˡ lower {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → zero-ʳ lower {c} {d}
  ; ι-zero = ↑² (waitᴸ 0ᴰ) εᵉ (lower-zero (0ᴰ <ᴰ? 0ᴰ))
  ; ι-plus = λ {m} {n} → ↑² (waitᴸ (m +ᴰ n)) (waitᴸ m ·ᵉ waitᴸ n) (lower-hom m n (0ᴰ <ᴰ? m) (0ᴰ <ᴰ? n) (0ᴰ <ᴰ? (m +ᴰ n)))
  }
