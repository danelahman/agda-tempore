------------------------------------------------------------------------
-- Expressions with iteration as grades, in each instance.            --
--                                                                    --
-- The elements are one-sided expressions with at least one word,     --
-- compared by the runs they denote (`Exact.Lift`), decided by the    --
-- automaton of the reader (`Regular.Decide`) in a commensurable time --
-- domain. Sequencing, union, the empty word and the unrestricted     --
-- stretch are the operations; a delay is graded by its hull on each  --
-- side. The Kleene plus of a grade is `e · e*`: the least grade      --
-- above `e` closed under sequencing, with the induction laws, at the --
-- ∀∃ lift of iteration.                                              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus
import Grades.Exact.Grid as Grid

module Grades.Exact.Regular.Grades
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ)
  (commensurable : Grid.Commensurable T) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_) renaming (T to IsTrue)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness; map′)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Hi; fin; ∞; ⁺; ⁻; ⊑⇒≤; ≤⇒⁺⊑⁺; ≤⇒⁻⊑⁻; _⊑ʰ_)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_)

open import Grades.Base using (Grade; Plus; plus)
open import Grades.Hints using (GradeHints)
open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-refl; ⊑-trans)
open import Grades.Exact.Lift T Op n code code-injective as L
  using (Lang; 𝟏ᴸ; _·ᴸ_; _∪ᴸ_; ⊆⇒≾; ⊑-++)
open import Grades.Exact.Expression T Op n code code-injective running
import Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos as Fin′
open import Grades.Exact.Regular.Unroll T Op n code code-injective running
  (Grid.commensurable⇒archimedean T commensurable) κ κ-pos using (split⊑; join⊑)
open import Grades.Exact.Regular.Decide T Op n code code-injective name code-name running
  dense κ κ-pos commensurable using (_≾ᵁ?_; _≾ᴸ?_)

------------------------------------------------------------------------
-- Expressions with a word

inhabited : ∀ {s} → Expr s → Bool
inhabited ε         = true
inhabited {s} (ops A) = Fin′.nonEmpty (Fin′.words {s} (ops A))
inhabited {s} (str S e) = Fin′.nonEmpty (Fin′.words {s} (str S e))
inhabited (e ∣ f)   = inhabited e ∨ inhabited f
inhabited (e · f)   = inhabited e ∧ inhabited f
inhabited (e *)     = true

Proper : ∀ {s} → Expr s → Set
Proper e = IsTrue (inhabited e)

private
  ∧-l : ∀ {a b} → IsTrue (a ∧ b) → IsTrue a
  ∧-l {true} _ = tt

  ∧-r : ∀ {a b} → IsTrue (a ∧ b) → IsTrue b
  ∧-r {true} t = t

  ∧-intro : ∀ {a b} → IsTrue a → IsTrue b → IsTrue (a ∧ b)
  ∧-intro {true} _ t = t

  ∨-introˡ : ∀ {a b} → IsTrue a → IsTrue (a ∨ b)
  ∨-introˡ {true} _ = tt

proper-run : ∀ {s} (e : Expr s) → Proper e → Σ[ x ∈ Word ] ⟦ e ⟧ x
proper-run ε         _ = [] , refl
proper-run {s} (ops A) p = Fin′.proper-run {s} (ops A) p
proper-run {s} (str S e) p = Fin′.proper-run {s} (str S e) p
proper-run (e ∣ f)   p with inhabited e in ie
... | true  = let (x , x∈) = proper-run e (subst IsTrue (sym ie) tt) in x , inj₁ x∈
... | false = let (x , x∈) = proper-run f p in x , inj₂ x∈
proper-run (e · f)   p with proper-run e (∧-l p) | proper-run f (∧-r {inhabited e} p)
... | x , x∈ | y , y∈ = x ++ y , x , y , refl , x∈ , y∈
proper-run (e *)     _ = [] , stop

record Proper′ (s : Instance) : Set where
  constructor ⌜_⌝
  field
    expr     : Expr s
    {proper} : Proper expr

open Proper′ public

infixl 7 _·ᵉ_
infixl 6 _∣ᵉ_

_·ᵉ_ _∣ᵉ_ : ∀ {s} → Proper′ s → Proper′ s → Proper′ s
⌜ e ⌝ {p} ·ᵉ ⌜ f ⌝ {q} = ⌜ e · f ⌝ {∧-intro {inhabited e} p q}
⌜ e ⌝ {p} ∣ᵉ ⌜ f ⌝ {q} = ⌜ e ∣ f ⌝ {∨-introˡ {inhabited e} p}

εᵉ : ∀ {s} → Proper′ s
εᵉ = ⌜ ε ⌝

-- the Kleene plus

_⁺ᵉ : ∀ {s} → Proper′ s → Proper′ s
⌜ e ⌝ {p} ⁺ᵉ = ⌜ e · e * ⌝ {∧-intro {inhabited e} p tt}

-- the order, decided in each instance

infix 4 _≾ᵉ_

_≾ᵉ_ : ∀ {s} → Proper′ s → Proper′ s → Set
c ≾ᵉ d = ⟦ expr c ⟧ L.≾ ⟦ expr d ⟧

_≾ᵉ?_ : ∀ {s} (c d : Proper′ s) → Dec (c ≾ᵉ d)
_≾ᵉ?_ {upper} c d = expr c ≾ᵁ? expr d
_≾ᵉ?_ {lower} c d = expr c ≾ᴸ? expr d

------------------------------------------------------------------------
-- The hull of a delay

waitᵁ : Carrier → Proper′ upper
waitᵁ τ = ⌜ str none (fin (τ ∣ᶜ ⁺)) ⌝ {proper-strᵁ (0ᴰ <ᴰ? τ)}
  where
    proper-strᵁ : (d : Dec (0ᴰ <ᴰ τ)) → IsTrue (Fin′.nonEmpty (Fin′.words {upper} (str none (fin (τ ∣ᶜ ⁺)))))
    proper-strᵁ _ with 0ᴰ <ᴰ? τ
    ... | yes _ = tt
    ... | no _  = tt

at-least′ : (τ : Carrier) → Dec (0ᴰ <ᴰ τ) → Proper′ lower
at-least′ τ (yes p) = ⌜ str none (τ ∣ᶜ ⁻) ⌝ {proper-strᴸ}
  where
    proper-strᴸ : IsTrue (Fin′.nonEmpty (Fin′.words {lower} (str none (τ ∣ᶜ ⁻))))
    proper-strᴸ with 0ᴰ <ᴰ? τ
    ... | yes _ = tt
    ... | no ¬p = ⊥-elim (¬p p)
at-least′ τ (no _)  = εᵉ

waitᴸ : Carrier → Proper′ lower
waitᴸ τ = at-least′ τ (0ᴰ <ᴰ? τ)

private
  stretch-0 : ∀ S → stretch S 0ᴰ ≡ []
  stretch-0 S = stretch-zero S 0ᴰ (λ q → <⇒≢ q refl)

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

  ≈-cong : ∀ {X Y Z : Lang} → X L.≈ Y → Y L.≈ Z → X L.≈ Z
  ≈-cong (a , b) (c , d) = L.≾-trans a c , L.≾-trans d b

  ≈-refl : ∀ {X : Lang} → X L.≈ X
  ≈-refl = L.≾-refl , L.≾-refl

  ≈-sym : ∀ {X Y : Lang} → X L.≈ Y → Y L.≈ X
  ≈-sym (a , b) = b , a

  any⊆ᵁ : L.anyᴸ L.⊆ᴸ strᴸ {upper} all ∞
  any⊆ᵁ w (τ , e) = τ , tt , e

  any⊆ᴸ : L.anyᴸ L.⊆ᴸ strᴸ {lower} all (0ᴰ ∣ᶜ ⁻)
  any⊆ᴸ w (τ , e) = τ , ≤⇒⁻⊑⁻ (0ᴰ-least τ) , e

  upper-zero : strᴸ {upper} none (fin (0ᴰ ∣ᶜ ⁺)) L.≈ 𝟏ᴸ
  upper-zero =
    ⊆⇒≾ (λ { x (τ , r , refl) → trans (cong (stretch none) (≤0⇒≡0 (⊑⇒≤ r))) (stretch-0 none) }) ,
    ⊆⇒≾ (λ { x refl → 0ᴰ , ≤⇒⁺⊑⁺ ≤ᴰ-refl , sym (stretch-0 none) })

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

------------------------------------------------------------------------
-- Kleene's plus at the ∀∃ lift: `X · X*` is the least set above `X`
-- closed under sequencing, and it moves nothing `X` does not move

private
  Star-++ : ∀ {X y z} → Star X y → Star X z → Star X (y ++ z)
  Star-++ stop z∈ = z∈
  Star-++ {X} {z = z} (more {x} {y} x∈ y∈) z∈ = subst (Star X) (sym (++-assoc x y z)) (more x∈ (Star-++ y∈ z∈))

  ≡⊑ : ∀ {x y} → x ≡ y → x ⊑ y
  ≡⊑ refl = ⊑-refl

  module _ (X : Lang) where

    plus-ub : X L.≾ (X ·ᴸ Star X)
    plus-ub x x∈ = x ++ [] , (x , [] , refl , x∈ , stop) , ≡⊑ (sym (++-identityʳ x))

    plus-iter : ((X ·ᴸ Star X) ·ᴸ (X ·ᴸ Star X)) L.≾ (X ·ᴸ Star X)
    plus-iter = ⊆⇒≾ λ { _ (_ , _ , refl , (x₁ , y₁ , refl , x₁∈ , y₁∈) , (x₂ , y₂ , refl , x₂∈ , y₂∈)) →
      x₁ , y₁ ++ (x₂ ++ y₂) , ++-assoc x₁ y₁ (x₂ ++ y₂) , x₁∈ , Star-++ y₁∈ (more x₂∈ y₂∈) }

    plus-least : ∀ {V} → X L.≾ V → (V ·ᴸ V) L.≾ V → (X ·ᴸ Star X) L.≾ V
    plus-least {V} xv vv _ (x , y , refl , x∈ , y∈) = go x x∈ y∈
      where
        go : ∀ x → X x → ∀ {y} → Star X y → Σ[ v ∈ Word ] V v × x ++ y ⊑ v
        go x x∈ stop with xv x x∈
        ... | v , v∈ , xv′ = v , v∈ , ⊑-trans (≡⊑ (++-identityʳ x)) xv′
        go x x∈ (more {x₂} {y′} x₂∈ y′∈) with xv x x∈ | go x₂ x₂∈ y′∈
        ... | v₁ , v₁∈ , f₁ | v₂ , v₂∈ , f₂ with vv (v₁ ++ v₂) (v₁ , v₂ , refl , v₁∈ , v₂∈)
        ...   | v , v∈ , f = v , v∈ , ⊑-trans (⊑-++ f₁ f₂) f

    plus-indˡ : ∀ {Y} → (X ·ᴸ Y) L.≾ Y → ((X ·ᴸ Star X) ·ᴸ Y) L.≾ Y
    plus-indˡ {Y} xy _ (_ , z , refl , (x , y , refl , x∈ , y∈) , z∈) with go y∈ z∈
      where
        go : ∀ {y} → Star X y → ∀ {z} → Y z → Σ[ d ∈ Word ] Y d × y ++ z ⊑ d
        go stop {z} z∈ = z , z∈ , ⊑-refl
        go (more {x′} {y′} x′∈ y′∈) {z} z∈ with go y′∈ z∈
        ... | d₁ , d₁∈ , f₁ with xy (x′ ++ d₁) (x′ , d₁ , refl , x′∈ , d₁∈)
        ...   | d₂ , d₂∈ , f₂ = d₂ , d₂∈ , ⊑-trans (≡⊑ (++-assoc x′ y′ z)) (⊑-trans (⊑-++ (⊑-refl {x′}) f₁) f₂)
    ... | d₁ , d₁∈ , f₁ with xy (x ++ d₁) (x , d₁ , refl , x∈ , d₁∈)
    ...   | d₂ , d₂∈ , f₂ = d₂ , d₂∈ , ⊑-trans (≡⊑ (++-assoc x y z)) (⊑-trans (⊑-++ (⊑-refl {x}) f₁) f₂)

    plus-indʳ : ∀ {Y} → (Y ·ᴸ X) L.≾ Y → (Y ·ᴸ (X ·ᴸ Star X)) L.≾ Y
    plus-indʳ {Y} yx _ (z , _ , refl , z∈ , (x , y , refl , x∈ , y∈)) with yx (z ++ x) (z , x , refl , z∈ , x∈)
    ... | d₁ , d₁∈ , f₁ with go d₁∈ y∈
      where
        go : ∀ {d} → Y d → ∀ {y} → Star X y → Σ[ d′ ∈ Word ] Y d′ × d ++ y ⊑ d′
        go {d} d∈ stop = d , d∈ , ≡⊑ (++-identityʳ d)
        go {d} d∈ (more {x′} {y′} x′∈ y′∈) with yx (d ++ x′) (d , x′ , refl , d∈ , x′∈)
        ... | d₂ , d₂∈ , f₂ with go d₂∈ y′∈
        ...   | d₃ , d₃∈ , f₃ = d₃ , d₃∈ , ⊑-trans (≡⊑ (sym (++-assoc d x′ y′))) (⊑-trans (⊑-++ f₂ (⊑-refl {y′})) f₃)
    ...   | d₂ , d₂∈ , f₂ = d₂ , d₂∈ , ⊑-trans (≡⊑ (sym (++-assoc z x y))) (⊑-trans (⊑-++ f₁ (⊑-refl {y})) f₂)

------------------------------------------------------------------------
-- The grades
--
-- A grade's order is the decision: `c ≾ᴳ d` holds when the runs of `c`
-- are found among those of `d`.

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

-- the order from and to the runs, without unfolding the decision

≾ᴳ-intro : ∀ {s} (c d : Proper′ s) → c ≾ᵉ d → c ≾ᴳ d
≾ᴳ-intro = ↑

≾ᴳ-elim : ∀ {s} (c d : Proper′ s) → c ≾ᴳ d → c ≾ᵉ d
≾ᴳ-elim = ↓

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

  -- the Kleene plus of every grade

  plusᵉ : ∀ (c : Proper′ s) → Plus _·ᵉ_ _≾ᴳ_ c
  plusᵉ c = plus (c ⁺ᵉ)
    (↑ c (c ⁺ᵉ) (plus-ub ⟦ expr c ⟧))
    (↑ (c ⁺ᵉ ·ᵉ c ⁺ᵉ) (c ⁺ᵉ) (plus-iter ⟦ expr c ⟧))
    (λ {v} cv vv → ↑ (c ⁺ᵉ) v (plus-least ⟦ expr c ⟧ (↓ c v cv) (↓ (v ·ᵉ v) v vv)))
    (λ {d} cd → ↑ (c ⁺ᵉ ·ᵉ d) d (plus-indˡ ⟦ expr c ⟧ (↓ (c ·ᵉ d) d cd)))
    (λ {d} dc → ↑ (d ·ᵉ c ⁺ᵉ) d (plus-indʳ ⟦ expr c ⟧ (↓ (d ·ᵉ c) d dc)))

open Common

-- the upper instance: right-sided grades

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

-- its hints: Kleene's plus at every grade

upperʰ : GradeHints upperᵍ
upperʰ = record { 𝟏-least? = nothing ; ·-comm? = nothing ; plus? = λ c → just (plusᵉ upper c) }

-- the lower instance: left-sided grades

lowerᵍ : Grade D
lowerᵍ = record
  { Carrier = Proper′ lower
  ; _·_     = _·ᵉ_
  ; 𝟏       = εᵉ
  ; _≾_     = _≾ᴳ_
  ; ⊤       = ⌜ str all (0ᴰ ∣ᶜ ⁻) ⌝ {⊤-proper}
  ; _⊔_     = _∣ᵉ_
  ; ι       = waitᴸ
  ; ·-identityˡ = ·-identityˡᵉ lower
  ; ·-identityʳ = ·-identityʳᵉ lower
  ; ·-assoc     = ·-assocᵉ lower
  ; ≾-refl       = λ {c} → refl-ᴳ lower {c}
  ; ≾-trans      = λ {c} {d} {e} → trans-ᴳ lower {c} {d} {e}
  ; ≾-irrelevant = ≾ᴳ-irr
  ; _≾?_         = _≾ᴳ?_
  ; ≾-⊤     = λ c → ↑ c (⌜ str all (0ᴰ ∣ᶜ ⁻) ⌝ {⊤-proper}) (L.≾-trans (L.≾-any ⟦ expr c ⟧) (⊆⇒≾ any⊆ᴸ))
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
  where
    ⊤-proper : IsTrue (Fin′.nonEmpty (Fin′.words {lower} (str all (0ᴰ ∣ᶜ ⁻))))
    ⊤-proper with 0ᴰ <ᴰ? 0ᴰ
    ... | yes _ = tt
    ... | no _  = tt

-- its hints: Kleene's plus at every grade

lowerʰ : GradeHints lowerᵍ
lowerʰ = record { 𝟏-least? = nothing ; ·-comm? = nothing ; plus? = λ c → just (plusᵉ lower c) }
