------------------------------------------------------------------------
-- Finite expressions: one-sided expressions without iteration, and   --
-- the decision of their order.                                       --
--                                                                    --
-- A finite expression denotes the union of finitely many words of    --
-- letters: a set of operations is the union of its operations, an    --
-- upper stretch whose end admits only zero is the empty word, one    --
-- whose end admits nothing is no word, and a lower stretch admitting --
-- zero is the empty word or a stretch of positive length. Each word  --
-- denotes the runs fitting its letters, and is prime: below a union  --
-- of words only when below one of them. So                           --
--                                                                    --
--   ⟦ e ⟧ ≾ ⟦ f ⟧  iff  every word of e is below some word of f      --
--                                                                    --
-- and the reader decides each comparison of words.                   --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus

module Grades.Exact.Finite
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Bool.Base using (Bool; true; false; _∧_)
  renaming (T to IsTrue)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (inside; outside; _∈_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (x∈⁅y⁆⇒x≡y; x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_; map; cartesianProductWith)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional
  renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻;
         ∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻; map⁺)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Vec.Base as V
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; Hi; fin; ∞; ⁺; ⁻; 0⁺; 0⁻; _⊑ʰ_; _◁_; by-pt; by-side; ⁻≤; ⁺≤⁺; ⊑⇒≤; ⊏-by-pt; ⊏-by-side; ≤⇒⁺⊑⁺; ⟪_,_⟫)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-trans to ⊑ᶜ-trans)
open import Grades.Durations.Intervals.Dense T using (⊑⁻⇒<; module Exact)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective using (_⊑_)
open import Grades.Exact.Lift T Op n code code-injective
open import Grades.Exact.Expression T Op n code code-injective running
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Reader.Upper T Op n code code-injective running
  using (RunU; runU?)
open import Grades.Exact.Reader.Lower T Op n code code-injective running
  using (RunL; runL?)
open import Grades.Exact.Reader.Upper.Close T Op n code code-injective running dense
  using (Valid)
open import Grades.Exact.Reader.Upper.Correct T Op n code code-injective running dense κ κ-pos
  using (symᵁ; ValidW; soundᵁ; completeᵁ)
open import Grades.Exact.Reader.Lower.Read T Op n code code-injective running
  using (ValidL)
open import Grades.Exact.Reader.Lower.Correct T Op n code code-injective running dense κ κ-pos
  using (symᴸ; AllValidL; soundᴸ; completeᴸ)

open RunningTimes.RunningTimes running using (rt; rt-positive)

------------------------------------------------------------------------
-- Finite expressions

starFree : ∀ {s} → Expr s → Bool
starFree ε         = true
starFree (ops _)   = true
starFree (str _ _) = true
starFree (e ∣ f)   = starFree e ∧ starFree f
starFree (e · f)   = starFree e ∧ starFree f
starFree (e *)     = false

Finite : ∀ {s} → Expr s → Set
Finite e = IsTrue (starFree e)

private
  ∧-l : ∀ {a b} → IsTrue (a ∧ b) → IsTrue a
  ∧-l {true} _ = tt
  ∧-r : ∀ {a b} → IsTrue (a ∧ b) → IsTrue b
  ∧-r {true} t = t

------------------------------------------------------------------------
-- The words of an expression

-- the codes in a set of operations

members : ∀ {m} → Subset m → List (Fin m)
members V.[]            = []
members (inside  V.∷ p) = zero ∷ map suc (members p)
members (outside V.∷ p) = map suc (members p)

private
  members⁺ : ∀ {m} {c : Fin m} {A} → c ∈ A → c ∈ˡ members A
  members⁺ {c = zero}  {inside V.∷ p}  V.here       = here refl
  members⁺ {c = suc c} {inside V.∷ p}  (V.there m)  = there (∈-map⁺ suc (members⁺ m))
  members⁺ {c = suc c} {outside V.∷ p} (V.there m)  = ∈-map⁺ suc (members⁺ m)

  members⁻ : ∀ {m} {c : Fin m} {A} → c ∈ˡ members A → c ∈ A
  members⁻ {A = inside V.∷ p}  (here refl) = V.here
  members⁻ {A = inside V.∷ p}  (there m) with ∈-map⁻ suc m
  ... | c′ , m′ , refl = V.there (members⁻ m′)
  members⁻ {A = outside V.∷ p} m with ∈-map⁻ suc m
  ... | c′ , m′ , refl = V.there (members⁻ m′)

-- the words of a stretch letter

strWords : ∀ s → OpSet → End s → List (Word′ s)
strWords upper S ∞                 = (st S ∞ ∷ []) ∷ []
strWords upper S (fin (p ∣ᶜ side)) with 0ᴰ <ᴰ? p
... | yes _ = (st S (fin (p ∣ᶜ side)) ∷ []) ∷ []
... | no _ with side
...   | ⁺ = [] ∷ []
...   | ⁻ = []
strWords lower S (p ∣ᶜ side) with 0ᴰ <ᴰ? p
... | yes _ = (st S (p ∣ᶜ side) ∷ []) ∷ []
... | no _ with side
...   | ⁺ = (st S (p ∣ᶜ ⁺) ∷ []) ∷ []
...   | ⁻ = [] ∷ (st S (0ᴰ ∣ᶜ ⁺) ∷ []) ∷ []

opw : ∀ {s} → Fin n → Word′ s
opw c = op (name c) ∷ []

words : ∀ {s} → Expr s → List (Word′ s)
words ε         = [] ∷ []
words (ops A)   = map opw (members A)
words (str S e) = strWords _ S e
words (e ∣ f)   = words e ++ words f
words (e · f)   = cartesianProductWith _++_ (words e) (words f)
words (e *)     = []

------------------------------------------------------------------------
-- An expression denotes the union of its words

private
  ⟦++⟧⇒ : ∀ {s} (u w : Word′ s) {x} → ⟦ u ++ w ⟧ʷ x → (⟦ u ⟧ʷ ·ᴸ ⟦ w ⟧ʷ) x
  ⟦++⟧⇒ []      w x∈ = [] , _ , refl , refl , x∈
  ⟦++⟧⇒ (ℓ ∷ u) w (x₁ , x′ , refl , x₁∈ , x′∈) with ⟦++⟧⇒ u w x′∈
  ... | x₂ , x₃ , refl , x₂∈ , x₃∈ =
    x₁ ++ x₂ , x₃ , sym (++-assoc x₁ x₂ x₃) , (x₁ , x₂ , refl , x₁∈ , x₂∈) , x₃∈

  ⟦++⟧⇐ : ∀ {s} (u w : Word′ s) {x} → (⟦ u ⟧ʷ ·ᴸ ⟦ w ⟧ʷ) x → ⟦ u ++ w ⟧ʷ x
  ⟦++⟧⇐ []      w (_ , x₂ , refl , refl , x₂∈) = x₂∈
  ⟦++⟧⇐ (ℓ ∷ u) w (_ , x₃ , refl , (x₁ , x₂ , refl , x₁∈ , x₂∈) , x₃∈) =
    x₁ , x₂ ++ x₃ , ++-assoc x₁ x₂ x₃ , x₁∈ , ⟦++⟧⇐ u w (x₂ , x₃ , refl , x₂∈ , x₃∈)

  -- a word of one letter
  one⇒ : ∀ {s} (ℓ : Letter (End s)) {x} → ⟦ ℓ ⟧ˡ x → ⟦ ℓ ∷ [] ⟧ʷ x
  one⇒ ℓ {x} x∈ = x , [] , sym (++-identityʳ′ x) , x∈ , refl
    where
      ++-identityʳ′ : ∀ (x : Word) → x ++ [] ≡ x
      ++-identityʳ′ []      = refl
      ++-identityʳ′ (i ∷ x) = cong (i ∷_) (++-identityʳ′ x)

  one⇐ : ∀ {s} (ℓ : Letter (End s)) {x} → ⟦ ℓ ∷ [] ⟧ʷ x → ⟦ ℓ ⟧ˡ x
  one⇐ ℓ (x₁ , _ , refl , x₁∈ , refl) = subst ⟦ ℓ ⟧ˡ (sym (++-identityʳ′ x₁)) x₁∈
    where
      ++-identityʳ′ : ∀ (x : Word) → x ++ [] ≡ x
      ++-identityʳ′ []      = refl
      ++-identityʳ′ (i ∷ x) = cong (i ∷_) (++-identityʳ′ x)

  -- a set of operations
  ops⇒ : ∀ {s} A {x} → opsᴸ A x → Any (λ (w : Word′ s) → ⟦ w ⟧ʷ x) (map opw (members A))
  ops⇒ {s} A (o , d , a , r , refl) = map⁺ (Any.map hit (members⁺ a))
    where
      hit : ∀ {c} → code o ≡ c → ⟦ opw {s} c ⟧ʷ (op o d ∷ [])
      hit refl = one⇒ {s} (op (name (code o)))
                   (o , d , subst (code o ∈_) (cong ⁅_⁆ (sym (code-name (code o)))) (x∈⁅x⁆ (code o)) , r , refl)

  ops⇐ : ∀ {s} A {x} {w : Word′ s} → w ∈ˡ map opw (members A) → ⟦ w ⟧ʷ x → opsᴸ A x
  ops⇐ {s} A m x∈ with ∈-map⁻ opw m
  ... | c , cm , refl with one⇐ {s} (op (name c)) x∈
  ...   | o , d , a , r , refl =
    o , d , subst (_∈ A) (trans (sym (code-name c)) (sym (x∈⁅y⁆⇒x≡y _ a))) (members⁻ cm) , r , refl

  -- stretch letters
  str⇒ : ∀ s S e {x} → strᴸ {s} S e x → Any (λ w → ⟦ w ⟧ʷ x) (strWords s S e)
  str⇒ upper S ∞ x∈ = here (one⇒ {upper} (st S ∞) x∈)
  str⇒ upper S (fin (p ∣ᶜ side)) x∈ with 0ᴰ <ᴰ? p
  ... | yes _ = here (one⇒ {upper} (st S _) x∈)
  ... | no ¬p with side | x∈
  ...   | ⁺ | τ , a , refl =
    here (trans (cong (stretch S) (≤0⇒≡0 (≤ᴰ-trans (⊑⇒≤ a) (≤ᴰ-reflexive (≮0⇒≡0 ¬p)))))
                (stretch-zero S 0ᴰ (λ q → <⇒≢ q refl)))
  ...   | ⁻ | τ , a , refl = ⊥-elim (¬p (λ z → ⊑⁻⇒<′ a z))
    where
      ⊑⁻⇒<′ : ∀ {τ} → (τ ∣ᶜ ⁺) ⊑ᶜ (p ∣ᶜ ⁻) → p ≤ᴰ 0ᴰ → ⊥
      ⊑⁻⇒<′ r z = ⊑⁻⇒< r refl (≤ᴰ-trans z (0ᴰ-least _))
  str⇒ lower S (p ∣ᶜ side) x∈ with 0ᴰ <ᴰ? p
  ... | yes _ = here (one⇒ {lower} (st S _) x∈)
  ... | no ¬p with side | x∈
  ...   | ⁺ | x∈′ = here (one⇒ {lower} (st S _) x∈′)
  ...   | ⁻ | τ , a , refl = zero-or-more (0ᴰ <ᴰ? τ)
    where
      zero-or-more : Dec (0ᴰ <ᴰ τ) → Any (λ (w : Word′ lower) → ⟦ w ⟧ʷ (stretch S τ))
                                         ([] ∷ (st S (0ᴰ ∣ᶜ ⁺) ∷ []) ∷ [])
      zero-or-more (yes τp) = there (here (one⇒ {lower} (st S (0ᴰ ∣ᶜ ⁺)) (τ , by-pt τp , refl)))
      zero-or-more (no ¬τp) = here (trans (cong (stretch S) (≮0⇒≡0 ¬τp)) (stretch-zero S 0ᴰ (λ q → <⇒≢ q refl)))

  str⇐ : ∀ s S e {x w} → w ∈ˡ strWords s S e → ⟦ w ⟧ʷ x → strᴸ {s} S e x
  str⇐ upper S ∞ (here refl) x∈ = one⇐ {upper} (st S ∞) x∈
  str⇐ upper S (fin (p ∣ᶜ side)) m x∈ with 0ᴰ <ᴰ? p
  str⇐ upper S (fin (p ∣ᶜ side)) (here refl) x∈ | yes _ = one⇐ {upper} (st S _) x∈
  str⇐ upper S (fin (p ∣ᶜ side)) m x∈ | no ¬p with side
  str⇐ upper S (fin (p ∣ᶜ side)) (here refl) refl | no ¬p | ⁺ =
    0ᴰ , ≤⇒⁺⊑⁺′ , sym (stretch-zero S 0ᴰ (λ q → <⇒≢ q refl))
    where
      ≤⇒⁺⊑⁺′ : fin (0ᴰ ∣ᶜ ⁺) ⊑ʰ fin (p ∣ᶜ ⁺)
      ≤⇒⁺⊑⁺′ = ≤⇒⁺⊑⁺ (0ᴰ-least p)
  str⇐ lower S (p ∣ᶜ side) m x∈ with 0ᴰ <ᴰ? p
  str⇐ lower S (p ∣ᶜ side) (here refl) x∈ | yes _ = one⇐ {lower} (st S _) x∈
  str⇐ lower S (p ∣ᶜ side) m x∈ | no ¬p with side
  str⇐ lower S (p ∣ᶜ side) (here refl) x∈ | no ¬p | ⁺ = one⇐ {lower} (st S _) x∈
  str⇐ lower S (p ∣ᶜ side) (here refl) refl | no ¬p | ⁻ =
    0ᴰ , subst (λ z → (z ∣ᶜ ⁻) ⊑ᶜ (0ᴰ ∣ᶜ ⁻)) (sym (≮0⇒≡0 ¬p)) (by-side refl ⁻≤) ,
    sym (stretch-zero S 0ᴰ (λ q → <⇒≢ q refl))
  str⇐ lower S (p ∣ᶜ side) (there (here refl)) x∈ | no ¬p | ⁻ with one⇐ {lower} (st S (0ᴰ ∣ᶜ ⁺)) x∈
  ... | τ , a , e =
    τ , subst (λ z → (z ∣ᶜ ⁻) ⊑ᶜ (τ ∣ᶜ ⁻)) (sym (≮0⇒≡0 ¬p))
               (⊑ᶜ-trans (by-side refl ⁻≤) a) , e

words⇒ : ∀ {s} (e : Expr s) → Finite e → ∀ {x} → ⟦ e ⟧ x → Any (λ w → ⟦ w ⟧ʷ x) (words e)
words⇒ ε         _ refl = here refl
words⇒ (ops A)   _ x∈ = ops⇒ A x∈
words⇒ (str S e) _ x∈ = str⇒ _ S e x∈
words⇒ (e ∣ f)   t (inj₁ x∈) = ++⁺ˡ (words⇒ e (∧-l t) x∈)
words⇒ (e ∣ f)   t (inj₂ x∈) = ++⁺ʳ (words e) (words⇒ f (∧-r {starFree e} t) x∈)
words⇒ (e · f)   t (x₁ , x₂ , refl , x₁∈ , x₂∈)
  with find (words⇒ e (∧-l t) x₁∈) | find (words⇒ f (∧-r {starFree e} t) x₂∈)
... | u , um , u∈ | w , wm , w∈ =
  lose (∈-cartesianProductWith⁺ _++_ um wm) (⟦++⟧⇐ u w (x₁ , x₂ , refl , u∈ , w∈))

words⇐ : ∀ {s} (e : Expr s) → Finite e → ∀ {x w} → w ∈ˡ words e → ⟦ w ⟧ʷ x → ⟦ e ⟧ x
words⇐ ε         _ (here refl) x∈ = x∈
words⇐ (ops A)   _ m x∈ = ops⇐ A m x∈
words⇐ (str S e) _ m x∈ = str⇐ _ S e m x∈
words⇐ (e ∣ f)   t {w = w} m x∈ with ∈-++⁻ (words e) m
... | inj₁ m′ = inj₁ (words⇐ e (∧-l t) m′ x∈)
... | inj₂ m′ = inj₂ (words⇐ f (∧-r {starFree e} t) m′ x∈)
words⇐ (e · f)   t m x∈ with ∈-cartesianProductWith⁻ _++_ (words e) (words f) m
... | u , w , um , wm , refl with ⟦++⟧⇒ u w x∈
...   | x₁ , x₂ , refl , u∈ , w∈ =
  x₁ , x₂ , refl , words⇐ e (∧-l t) um u∈ , words⇐ f (∧-r {starFree e} t) wm w∈

------------------------------------------------------------------------
-- The words of an expression are of the reader's kind

private
  validW-++ : ∀ (u w : Word′ upper) → ValidW u → ValidW w → ValidW (u ++ w)
  validW-++ []           w _        vw = vw
  validW-++ (op _ ∷ u)   w vu       vw = validW-++ u w vu vw
  validW-++ (st _ _ ∷ u) w (p , vu) vw = p , validW-++ u w vu vw

  valid-++ : ∀ (u w : Word′ upper) → Valid u → Valid w → Valid (u ++ w)
  valid-++ []           w _        vw = vw
  valid-++ (op _ ∷ u)   w vu       vw = valid-++ u w vu vw
  valid-++ (st _ _ ∷ u) w (p , vu) vw = p , valid-++ u w vu vw

  validL-++ : ∀ (u w : Word′ lower) → ValidL u → ValidL w → ValidL (u ++ w)
  validL-++ []           w _        vw = vw
  validL-++ (op _ ∷ u)   w vu       vw = validL-++ u w vu vw
  validL-++ (st _ _ ∷ u) w (p , vu) vw = p , validL-++ u w vu vw

-- what the reader asks of the words of each instance

Fine : ∀ s → Word′ s → Set
Fine upper w = ValidW w × Valid w
Fine lower w = ValidL w

private
  fine-++ : ∀ s (u w : Word′ s) → Fine s u → Fine s w → Fine s (u ++ w)
  fine-++ upper u w (a , b) (c , d) = validW-++ u w a c , valid-++ u w b d
  fine-++ lower u w a c = validL-++ u w a c

  fine-str : ∀ s S e {w} → w ∈ˡ strWords s S e → Fine s w
  fine-str upper S ∞ (here refl) = (tt , tt) , (tt , tt)
  fine-str upper S (fin (p ∣ᶜ side)) m with 0ᴰ <ᴰ? p
  fine-str upper S (fin (p ∣ᶜ side)) (here refl) | yes pp = (⊏-by-pt pp , tt) , (by-pt pp , tt)
  fine-str upper S (fin (p ∣ᶜ side)) m | no _ with side
  fine-str upper S (fin (p ∣ᶜ side)) (here refl) | no _ | ⁺ = tt , tt
  fine-str lower S (p ∣ᶜ side) m with 0ᴰ <ᴰ? p
  fine-str lower S (p ∣ᶜ side) (here refl) | yes pp = by-pt pp , tt
  fine-str lower S (p ∣ᶜ side) m | no ¬p with side
  fine-str lower S (p ∣ᶜ side) (here refl) | no ¬p | ⁺ = by-side (sym (≮0⇒≡0 ¬p)) ⁺≤⁺ , tt
  fine-str lower S (p ∣ᶜ side) (here refl) | no ¬p | ⁻ = tt
  fine-str lower S (p ∣ᶜ side) (there (here refl)) | no ¬p | ⁻ = by-side refl ⁺≤⁺ , tt

  fine-op : ∀ s c → Fine s (opw c)
  fine-op upper c = tt , tt
  fine-op lower c = tt

fine : ∀ {s} (e : Expr s) {w} → w ∈ˡ words e → Fine s w
fine {upper} ε (here refl) = tt , tt
fine {lower} ε (here refl) = tt
fine {s} (ops A) m with ∈-map⁻ opw m
... | c , _ , refl = fine-op s c
fine {s} (str S e) m = fine-str s S e m
fine (e ∣ f) m with ∈-++⁻ (words e) m
... | inj₁ m′ = fine e m′
... | inj₂ m′ = fine f m′
fine {s} (e · f) m with ∈-cartesianProductWith⁻ _++_ (words e) (words f) m
... | u , w , um , wm , refl = fine-++ s u w (fine e um) (fine f wm)

------------------------------------------------------------------------
-- The decision

-- the reader's comparison of two words of an instance

Reads : ∀ s → Word′ s → Word′ s → Set
Reads upper w v = RunU (map symᵁ w) v
Reads lower w v = RunL (map symᴸ w) v

reads? : ∀ s w v → Dec (Reads s w v)
reads? upper w v = runU? (map symᵁ w) v
reads? lower w v = runL? (map symᴸ w) v

-- every word of the lesser expression is read against some word of the
-- greater

Below : ∀ {s} → Expr s → Expr s → Set
Below {s} e f = All (λ w → Any (λ v → Reads s w v) (words f)) (words e)

below? : ∀ {s} (e f : Expr s) → Dec (Below e f)
below? {s} e f = all? (λ w → any? (λ v → reads? s w v) (words f)) (words e)

private
  sound-word : ∀ s (w v : Word′ s) → Fine s v → Reads s w v → ⟦ w ⟧ʷ ≾ ⟦ v ⟧ʷ
  sound-word upper w v (_ , val) r = soundᵁ w v val r
  sound-word lower w v _ r = soundᴸ w v r

  allValidL : ∀ (vs : List (Word′ lower)) → (∀ {v} → v ∈ˡ vs → ValidL v) → AllValidL vs
  allValidL []       _ = tt
  allValidL (v ∷ vs) h = h (here refl) , allValidL vs (λ m → h (there m))

  complete-word : ∀ s (w : Word′ s) → Fine s w → ∀ vs → (∀ {v} → v ∈ˡ vs → Fine s v)
                → ⟦ w ⟧ʷ ≾ (λ y → Any (λ v → ⟦ v ⟧ʷ y) vs) → Any (λ v → Reads s w v) vs
  complete-word upper w (vw , _) vs _ f = completeᵁ w vw vs f
  complete-word lower w vw vs h f = completeᴸ w vw vs (allValidL vs h) f

below-sound : ∀ {s} (e f : Expr s) → Finite e → Finite f → Below e f → ⟦ e ⟧ ≾ ⟦ f ⟧
below-sound {s} e f te tf b x x∈ with find (words⇒ e te x∈)
... | w , wm , x∈w with find (All.lookup b wm)
...   | v , vm , r with sound-word s w v (fine f vm) r x x∈w
...     | y , y∈v , fit = y , words⇐ f tf vm y∈v , fit

below-complete : ∀ {s} (e f : Expr s) → Finite e → Finite f → ⟦ e ⟧ ≾ ⟦ f ⟧ → Below e f
below-complete {s} e f te tf g = All.tabulate each
  where
    each : ∀ {w} → w ∈ˡ words e → Any (λ v → Reads s w v) (words f)
    each {w} wm = complete-word s w (fine e wm) (words f) (fine f)
      (λ x x∈ → let (y , y∈ , fit) = g x (words⇐ e te wm x∈) in y , words⇒ f tf y∈ , fit)

-- the order on finite expressions, decided

decide : ∀ {s} (e f : Expr s) → Finite e → Finite f → ⟦ e ⟧ ≾ ⟦ f ⟧ ⇔ Below e f
decide e f te tf = mk⇔ (below-complete e f te tf) (below-sound e f te tf)

_≾?_ : ∀ {s} (e f : Expr s) → Finite e → Finite f → Dec (⟦ e ⟧ ≾ ⟦ f ⟧)
(e ≾? f) te tf = map′ (below-sound e f te tf) (below-complete e f te tf) (below? e f)

------------------------------------------------------------------------
-- An expression with a word denotes some run

private
  module Ex = Exact dense κ κ-pos

  op-run : ∀ {s} o → Σ[ x ∈ Word ] ⟦ op {End s} o ⟧ˡ x
  op-run o with Ex.inhabited (rt o)
  ... | θ , m = op o (pos⁺ θ pos) ∷ [] , o , pos⁺ θ pos , x∈⁅x⁆ (code o) , m , refl
    where
      pos : 0ᴰ <ᴰ θ
      pos = ⊑⁻⇒< (⊑ᶜ-trans (rt-positive o) (proj₁ m)) refl

  run-of : ∀ s (w : Word′ s) → Fine s w → Σ[ x ∈ Word ] ⟦ w ⟧ʷ x
  run-of s [] _ = [] , refl
  run-of upper (op o ∷ w) (vw , val) with op-run {upper} o | run-of upper w (vw , val)
  ... | x₁ , x₁∈ | x₂ , x₂∈ = x₁ ++ x₂ , x₁ , x₂ , refl , x₁∈ , x₂∈
  run-of upper (st S h ∷ w) ((_ , vw) , (z , val)) with run-of upper w (vw , val)
  ... | x₂ , x₂∈ =
    stretch S 0ᴰ ++ x₂ , stretch S 0ᴰ , x₂ , refl , (0ᴰ , z , refl) , x₂∈
  run-of lower (op o ∷ w) vw with op-run {lower} o | run-of lower w vw
  ... | x₁ , x₁∈ | x₂ , x₂∈ = x₁ ++ x₂ , x₁ , x₂ , refl , x₁∈ , x₂∈
  run-of lower (st S c ∷ w) (_ , vw) with Ex.inhabited ⟪ c , ∞ ⟫ | run-of lower w vw
  ... | τ , m | x₂ , x₂∈ = stretch S τ ++ x₂ , stretch S τ , x₂ , refl , (τ , proj₁ m , refl) , x₂∈

nonEmpty : ∀ {A : Set} → List A → Bool
nonEmpty []      = false
nonEmpty (_ ∷ _) = true

-- a finite expression with a word

Proper : ∀ {s} → Expr s → Set
Proper e = IsTrue (starFree e ∧ nonEmpty (words e))

proper-finite : ∀ {s} (e : Expr s) → Proper e → Finite e
proper-finite e p = ∧-l p

proper-run : ∀ {s} (e : Expr s) → Proper e → Σ[ x ∈ Word ] ⟦ e ⟧ x
proper-run {s} e p = go (words e) refl (∧-r {starFree e} p)
  where
    go : ∀ ws → words e ≡ ws → IsTrue (nonEmpty ws) → Σ[ x ∈ Word ] ⟦ e ⟧ x
    go (w ∷ ws) eq _ with run-of s w (fine e (subst (w ∈ˡ_) (sym eq) (here refl)))
    ... | x , x∈ = x , words⇐ e (∧-l p) (subst (w ∈ˡ_) (sym eq) (here refl)) x∈
