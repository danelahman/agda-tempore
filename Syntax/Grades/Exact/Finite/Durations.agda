------------------------------------------------------------------------
-- The duration hull of the finite-expression grades.                 --
--                                                                    --
-- A grade is an expression with a word, so its hull (`Exact.         --
-- Durations`) is an interval, `hullᴾ`: the least interval holding    --
-- the durations of its runs. It is monotone in the grade order and   --
-- sends the empty word to the point zero, sequencing to the sum of   --
-- intervals and the join to the hull of the union.                   --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Finite.Durations
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Bool.Base using (true; _∧_) renaming (T to IsTrue)
open import Data.Maybe.Base using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)

open import Syntax.Durations.Intervals T using (Interval; _⊆ⁱ_; _⊕_; _∪ⁱ_; 0ⁱ)

open import Syntax.Grades.Exact.Expression T Op n code code-injective running
open import Syntax.Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos
  using (starFree; proper-finite; proper-run)
open import Syntax.Grades.Exact.Finite.Grades T Op n code code-injective name code-name running dense κ κ-pos
open import Syntax.Grades.Exact.Durations T Op n code code-injective name code-name running public
open Least dense κ κ-pos public

-- a finite expression has no iteration

noStar : ∀ {s} (e : Expr s) → IsTrue (starFree e) → NoStar e
noStar ε         _ = tt
noStar (ops _)   _ = tt
noStar (str _ _) _ = tt
noStar (e ∣ f)   p = noStar e (∧-l p) , noStar f (∧-r {starFree e} p)
  where
    ∧-l : ∀ {a b} → IsTrue (a ∧ b) → IsTrue a
    ∧-l {true} _ = tt
    ∧-r : ∀ {a b} → IsTrue (a ∧ b) → IsTrue b
    ∧-r {true} t = t
noStar (e · f)   p = noStar e (∧-l p) , noStar f (∧-r {starFree e} p)
  where
    ∧-l : ∀ {a b} → IsTrue (a ∧ b) → IsTrue a
    ∧-l {true} _ = tt
    ∧-r : ∀ {a b} → IsTrue (a ∧ b) → IsTrue b
    ∧-r {true} t = t

------------------------------------------------------------------------
-- The hull of a grade

hullᴾ : ∀ {s} → Proper′ s → Interval
hullᴾ c = hullOf (expr c) (proper-run (expr c) (proper c))

hullᴾ-≡ : ∀ {s} (c : Proper′ s) → hull (expr c) ≡ just (hullᴾ c)
hullᴾ-≡ c = hullOf-≡ (expr c) (proper-run (expr c) (proper c))

-- a grade whose hull computes to an interval has it as its hull

hullᴾ-is : ∀ {s} (c : Proper′ s) {i} → hull (expr c) ≡ just i → hullᴾ c ≡ i
hullᴾ-is c eq = just-injective (trans (sym (hullᴾ-≡ c)) eq)

-- the operations

hullᴾ-ε : ∀ {s} → hullᴾ (εᵉ {s}) ≡ 0ⁱ
hullᴾ-ε {s} = hullᴾ-is (εᵉ {s}) refl

hullᴾ-· : ∀ {s} (c d : Proper′ s) → hullᴾ (c ·ᵉ d) ≡ hullᴾ c ⊕ hullᴾ d
hullᴾ-· c d = hullᴾ-is (c ·ᵉ d) (cong₂ _⊕ʰ_ (hullᴾ-≡ c) (hullᴾ-≡ d))

hullᴾ-∣ : ∀ {s} (c d : Proper′ s) → hullᴾ (c ∣ᵉ d) ≡ hullᴾ c ∪ⁱ hullᴾ d
hullᴾ-∣ c d = hullᴾ-is (c ∣ᵉ d) (cong₂ _∪ʰ_ (hullᴾ-≡ c) (hullᴾ-≡ d))

-- monotonicity

hullᴾ-mono : ∀ {s} {c d : Proper′ s} → c ≾ᴳ d → hullᴾ c ⊆ⁱ hullᴾ d
hullᴾ-mono {c = c} {d} p =
  hull-mono (expr c) (expr d) (noStar (expr c) (proper-finite (expr c) (proper c)))
    (toWitness (by-reader p)) (hullᴾ-≡ c) (hullᴾ-≡ d)
