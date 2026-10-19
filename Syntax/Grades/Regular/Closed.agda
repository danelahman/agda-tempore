------------------------------------------------------------------------
-- Regular languages closed downward under a letter preorder.         --
--                                                                    --
-- Given a preorder `R` on letters, a language is closed when it      --
-- holds every word lying letter by letter below one of its words.    --
-- Closed languages are closed under the operations of the regular    --
-- grade -- concatenation, union, iteration, the empty word and the   --
-- set of all words -- so they form a sub-grade of it, ordered by     --
-- inclusion, once a monoid morphism from durations is chosen among   --
-- them. The literal of a language is its downward closure. Kleene's  --
-- plus is declared for every grade.                                  --
------------------------------------------------------------------------

open import Data.Bool.Base using (Bool; T)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Fin.Base using (Fin)

module Syntax.Grades.Regular.Closed
  (k : ℕ) (tick : Fin k)
  (R : Fin k → Fin k → Bool)
  (R-refl : ∀ a → T (R a a))
  (R-trans : ∀ a b c → T (R a b) → T (R b c) → T (R a c)) where

open import Data.Bool.Properties using (T-irrelevant)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (Σ; _×_; _,_; ∃; ∃₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (True; toWitness; T?; recompute; map′)

open import Syntax.Durations.Nat using (ℕᴰ)
open import Syntax.Grades using (Grade; Plus; plus)
open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Inclusion k using (_⊆ᵇ_)
open import Syntax.Grades.Regular.Decide k using (⊆ᵇ-sound; ⊆ᵇ-complete; nonempty?)
open import Syntax.Grades.Regular.Closure k
open import Syntax.Grades.Regular.Constructions k using (_∈*_; none; more)
open import Syntax.Grades.Regular.Grade k tick public
  using (Regular; regular; table; wf′; ∈·⁺; ∈·-elim; ∈⊔⁺ˡ; ∈⊔⁺ʳ; ∈⊔-elim; ∈u⁻; ∈u⁺; ∈⊤)
  renaming (_≾_ to _≾ᴿ_; _·ᴿ_ to _·ᴿ_; _⊔ᴿ_ to _⊔ᴿ_; u to uᴿ; ⊤ to ⊤ᴿ)
import Syntax.Grades.Regular.Grade k tick as G
open import Syntax.Grades.Regular.Grade k tick using (starᴿ; ∈*⁻; ∈*⁺; plusᴿ; c⁺-def)

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Closed languages

Below′ : Word → Word → Set
Below′ = Below R

IsClosed : Regular → Set
IsClosed c = ∀ w v → Below′ w v → v ∈ table c → w ∈ table c

closed? : Regular → Bool
closed? c = ↓ R (table c) ⊆ᵇ table c

closed?-sound : ∀ c → T (closed? c) → IsClosed c
closed?-sound c t w v wv v∈ =
  ⊆ᵇ-sound {↓ R (table c)} {table c} (↓-wf R {table c} (wf′ c)) (wf′ c) t w
    (from (∈-↓ R {table c} (wf′ c) w) (v , wv , v∈))

closed?-complete : ∀ c → IsClosed c → T (closed? c)
closed?-complete c cl =
  ⊆ᵇ-complete {↓ R (table c)} {table c} (↓-wf R {table c} (wf′ c)) (wf′ c)
    λ w w∈ → case (to (∈-↓ R {table c} (wf′ c) w) w∈)
  where
    case : ∀ {w} → (∃ λ v → Below′ w v × v ∈ table c) → w ∈ table c
    case (v , wv , v∈) = cl _ v wv v∈

record Closed : Set where
  constructor closed
  field
    lang        : Regular
    .closedness : T (closed? lang)

open Closed public

closedness′ : (c : Closed) → IsClosed (lang c)
closedness′ (closed l p) = closed?-sound l (recompute (T? (closed? l)) p)

lang-injective : ∀ {c d} → lang c ≡ lang d → c ≡ d
lang-injective {closed l _} {closed .l _} refl = refl

-- a language shown closed

⟨_⟩ᶜ : (c : Regular) → IsClosed c → Closed
⟨ c ⟩ᶜ cl = closed c (closed?-complete c cl)

------------------------------------------------------------------------
-- Words below a concatenation

private
  below-++ : ∀ x {y w} → Below′ w (x ++ y) → ∃₂ λ w₁ w₂ → w ≡ w₁ ++ w₂ × Below′ w₁ x × Below′ w₂ y
  below-++ []      b = [] , _ , refl , [] , b
  below-++ (a ∷ x) (r ∷ b) with below-++ x b
  ... | w₁ , w₂ , refl , b₁ , b₂ = _ ∷ w₁ , w₂ , refl , r ∷ b₁ , b₂

  below-[] : ∀ {w} → Below′ w [] → w ≡ []
  below-[] [] = refl

  below-trans : ∀ {w v t} → Below′ w v → Below′ v t → Below′ w t
  below-trans []       []       = []
  below-trans (r ∷ rs) (s ∷ ss) = R-trans _ _ _ r s ∷ below-trans rs ss

------------------------------------------------------------------------
-- The operations keep languages closed

u : Closed
u = ⟨ uᴿ ⟩ᶜ λ w v wv v∈ → subst (λ z → z ∈ table uᴿ) (sym (helper wv v∈)) ∈u⁺
  where
    helper : ∀ {w v} → Below′ w v → v ∈ table uᴿ → w ≡ []
    helper wv v∈ = below-[] (subst (Below′ _) (∈u⁻ _ v∈) wv)

⊤ : Closed
⊤ = ⟨ ⊤ᴿ ⟩ᶜ λ w _ _ _ → ∈⊤ w

infixl 7 _·_
infixl 6 _⊔_

·-closed : ∀ c d → IsClosed c → IsClosed d → IsClosed (c ·ᴿ d)
·-closed c d cc cd w v wv v∈ =
  ∈·-elim c d (λ z → Below′ w z → w ∈ table (c ·ᴿ d)) v v∈
    (λ x y x∈ y∈ b → case (below-++ x b) x∈ y∈) wv
  where
    case : ∀ {w x y} → (∃₂ λ w₁ w₂ → w ≡ w₁ ++ w₂ × Below′ w₁ x × Below′ w₂ y)
         → x ∈ table c → y ∈ table d → w ∈ table (c ·ᴿ d)
    case (w₁ , w₂ , refl , b₁ , b₂) x∈ y∈ = ∈·⁺ c d w₁ w₂ (cc _ _ b₁ x∈) (cd _ _ b₂ y∈)

_·_ : Closed → Closed → Closed
c · d = ⟨ lang c ·ᴿ lang d ⟩ᶜ (·-closed (lang c) (lang d) (closedness′ c) (closedness′ d))

_⊔_ : Closed → Closed → Closed
c ⊔ d = ⟨ lang c ⊔ᴿ lang d ⟩ᶜ λ w v wv v∈ →
  ∈⊔-elim (lang c) (lang d) (w ∈ table (lang c ⊔ᴿ lang d)) v v∈
    (λ v∈c → ∈⊔⁺ˡ (lang c) (lang d) w (closedness′ c w v wv v∈c))
    (λ v∈d → ∈⊔⁺ʳ (lang c) (lang d) w (closedness′ d w v wv v∈d))

star-closed : ∀ c → IsClosed c → IsClosed (starᴿ c)
star-closed c cc w v wv v∈ = ∈*⁺ c w (go (∈*⁻ c v v∈) wv)
  where
    go : ∀ {v w} → v ∈* table c → Below′ w v → w ∈* table c
    go (none refl)           wv = none (below-[] wv)
    go (more x y refl x∈ ys) wv with below-++ x wv
    ... | w₁ , w₂ , refl , b₁ , b₂ = more w₁ w₂ refl (cc _ _ b₁ x∈) (go ys b₂)

star : Closed → Closed
star c = ⟨ starᴿ (lang c) ⟩ᶜ (star-closed (lang c) (closedness′ c))

-- the literal of a non-empty language: its downward closure

⌜_⌝ : (L : DFA) → {wf : WellFormed L} → {ne : True (nonempty? (↓ R L) (↓-wf R {L} wf))} → Closed
⌜ L ⌝ {wf} {ne} =
  ⟨ regular (↓ R L) (↓-wf R {L} wf) (↓-canonical R {L} wf) (toWitness ne) ⟩ᶜ λ w v wv v∈ →
    case (to (∈-↓ R {L} wf v) v∈) wv
  where
    case : ∀ {v w} → (∃ λ t → Below′ v t × t ∈ L) → Below′ w v → w ∈ ↓ R L
    case (t , vt , t∈) wv = from (∈-↓ R {L} wf _) (t , below-trans wv vt , t∈)

-- the literal of a language shown inhabited

⌜_⌝′ : (L : DFA) → WellFormed L → (∃ λ w → w ∈ L) → Closed
⌜ L ⌝′ wf (w , w∈) =
  ⟨ regular (↓ R L) (↓-wf R {L} wf) (↓-canonical R {L} wf)
            (w , from (∈-↓ R {L} wf w) (w , below-refl w , w∈)) ⟩ᶜ λ w v wv v∈ →
    case (to (∈-↓ R {L} wf v) v∈) wv
  where
    below-refl : ∀ w → Below′ w w
    below-refl []      = []
    below-refl (a ∷ w) = R-refl a ∷ below-refl w
    case : ∀ {v w} → (∃ λ t → Below′ v t × t ∈ L) → Below′ w v → w ∈ ↓ R L
    case (t , vt , t∈) wv = from (∈-↓ R {L} wf _) (t , below-trans wv vt , t∈)

∈-⌜⌝′ : ∀ L {wf i} w → w ∈ table (lang (⌜ L ⌝′ wf i)) → ∃ λ v → Below′ w v × v ∈ L
∈-⌜⌝′ L {wf} w = to (∈-↓ R {L} wf w)

∈-⌜⌝′⁺ : ∀ L {wf i} w v → Below′ w v → v ∈ L → w ∈ table (lang (⌜ L ⌝′ wf i))
∈-⌜⌝′⁺ L {wf} w v wv v∈ = from (∈-↓ R {L} wf w) (v , wv , v∈)

∈-⌜⌝ : ∀ L {wf ne} w → w ∈ table (lang (⌜ L ⌝ {wf} {ne})) → ∃ λ v → Below′ w v × v ∈ L
∈-⌜⌝ L {wf} w = to (∈-↓ R {L} wf w)

∈-⌜⌝⁺ : ∀ L {wf ne} w v → Below′ w v → v ∈ L → w ∈ table (lang (⌜ L ⌝ {wf} {ne}))
∈-⌜⌝⁺ L {wf} w v wv v∈ = from (∈-↓ R {L} wf w) (v , wv , v∈)

------------------------------------------------------------------------
-- The order

infix 4 _≾_

-- inclusion of the languages, wrapped so that the two grades can be
-- read off a comparison

record _≾_ (c d : Closed) : Set where
  constructor ≾-intro
  field
    ≾-lang : lang c ≾ᴿ lang d

open _≾_ public

≾-antisym : ∀ {c d} → c ≾ d → d ≾ c → c ≡ d
≾-antisym {c} {d} (≾-intro p) (≾-intro q) = lang-injective (G.≾-antisym {lang c} {lang d} p q)

-- Kleene's plus

plusᶜ : (c : Closed) → Plus _·_ _≾_ c
plusᶜ c = plus c⁺ (≾-intro (Plus.≾-c⁺ P)) (≾-intro (Plus.c⁺-iter P))
               (λ {v} cv vv → ≾-intro (Plus.c⁺-least P {lang v} (≾-lang cv) (≾-lang vv)))
               (λ {d} cd → ≾-intro (Plus.⁺-indˡ P {lang d} (≾-lang cd)))
               (λ {d} dc → ≾-intro (Plus.⁺-indʳ P {lang d} (≾-lang dc)))
  where
    P = plusᴿ (lang c)
    c⁺ : Closed
    c⁺ = ⟨ Plus.c⁺ P ⟩ᶜ
           (subst IsClosed (sym (c⁺-def (lang c)))
             (·-closed (lang c) (starᴿ (lang c)) (closedness′ c)
               (star-closed (lang c) (closedness′ c))))

-- the monoid laws

·-identityˡ : ∀ c → u · c ≡ c
·-identityˡ c = lang-injective (G.·-identityˡ (lang c))

·-identityʳ : ∀ c → c · u ≡ c
·-identityʳ c = lang-injective (G.·-identityʳ (lang c))

·-assoc : ∀ c d e → (c · d) · e ≡ c · (d · e)
·-assoc c d e = lang-injective (G.·-assoc (lang c) (lang d) (lang e))

------------------------------------------------------------------------
-- The grade, given the durations as closed languages

module WithDurations
  (of-dur : ℕ → Closed)
  (of-dur-zero : of-dur 0 ≡ u)
  (of-dur-plus : ∀ {m n} → of-dur (m + n) ≡ of-dur m · of-dur n) where

  closed-grade : Grade ℕᴰ
  closed-grade = record
    { Carrier         = Closed
    ; _·_             = _·_
    ; u               = u
    ; _≾_             = _≾_
    ; ⊤               = ⊤
    ; _⊔_             = _⊔_
    ; of-dur          = of-dur
    ; ·-identityˡ     = ·-identityˡ
    ; ·-identityʳ     = ·-identityʳ
    ; ·-assoc         = ·-assoc
    ; ≾-refl          = λ {c} → ≾-intro (G.≾-refl {lang c})
    ; ≾-trans         = λ {c} {d} {e} p q → ≾-intro (G.≾-trans {lang c} {lang d} {lang e} (≾-lang p) (≾-lang q))
    ; ≾-antisym       = λ {c} {d} → ≾-antisym {c} {d}
    ; ≾-irrelevant    = λ {c} {d} p q → cong ≾-intro (T-irrelevant (≾-lang p) (≾-lang q))
    ; _≾?_            = λ c d → map′ ≾-intro ≾-lang (T? (table (lang c) ⊆ᵇ table (lang d)))
    ; ≾-⊤             = λ c → ≾-intro (G.≾-⊤ (lang c))
    ; ⊔-ubˡ           = λ c d → ≾-intro (G.⊔-ubˡ (lang c) (lang d))
    ; ⊔-ubʳ           = λ c d → ≾-intro (G.⊔-ubʳ (lang c) (lang d))
    ; ⊔-lub           = λ {c} {d} {e} p q → ≾-intro (G.⊔-lub {lang c} {lang d} {lang e} (≾-lang p) (≾-lang q))
    ; ·-monoˡ-≾       = λ {c} {d} {d′} p → ≾-intro (G.·-monoˡ-≾ {lang c} {lang d} {lang d′} (≾-lang p))
    ; ·-monoʳ-≾       = λ {c} {d} {d′} p → ≾-intro (G.·-monoʳ-≾ {lang c} {lang d} {lang d′} (≾-lang p))
    ; ·-distribˡ-⊔-≾  = λ c d e → ≾-intro (G.·-distribˡ-⊔-≾ (lang c) (lang d) (lang e))
    ; ·-distribʳ-⊔-≾  = λ c d e → ≾-intro (G.·-distribʳ-⊔-≾ (lang c) (lang d) (lang e))
    ; ≾-zero-productˡ = λ {c} {d} p → ≾-intro (G.≾-zero-productˡ {lang c} {lang d} (≾-lang p))
    ; ≾-zero-productʳ = λ {c} {d} p → ≾-intro (G.≾-zero-productʳ {lang c} {lang d} (≾-lang p))
    ; of-dur-zero     = of-dur-zero
    ; of-dur-plus     = λ {m} {n} → of-dur-plus {m} {n}
    ; u-least?        = nothing
    ; plus?           = λ c → just (plusᶜ c)
    ; ·-comm?         = nothing
    }
