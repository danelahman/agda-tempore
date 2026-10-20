------------------------------------------------------------------------
-- Worked comparisons of regular-expression bounds, decided in Agda   --
-- and by the reference reader of the design study.                   --
--                                                                    --
-- Two operations, `a` taking more than zero and at most one unit, `b` --
-- at least one and less than two. Each comparison is one of a random --
-- set on which the decision and the reference reader agree; here     --
-- the decision is evaluated.                                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Rational.CrossChecked where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (⁅_⁆; _∪_) renaming (⊥ to none)
open import Data.Product using (_,_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse; isYes)

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
open import Syntax.Durations.Monus ℚ≥0ᵀ using (0ᴰ; _<ᴰ_)
open import Syntax.Durations.Intervals ℚ≥0ᵀ using (fin; ∞; ⁻; ⁺) renaming (_∣_ to _∣ᶜ_)
open import Syntax.Durations.Intervals.Dense ℚ≥0ᵀ using (_∈ⁱ?_)
open import Syntax.Grades.Example.Time.Dense.NonNegativeRational using (_≤?_)
open import Syntax.Grades.Example.Time.Dense.TwoSided
  using (Interval; ]_,_]; [_,_[; ↑_; _/_; #_; _⊑?_; 0⁺; lo)
open import Syntax.Grades.Traces.RunningTimes ℚ≥0ᵀ using (RunningTimes) renaming (fin to bounded)
open import Syntax.Grades.Exact.Grid.NonNegativeRational using (ℚ≥0-commensurable)

------------------------------------------------------------------------
-- The operations

data Op : Set where a b : Op

code : Op → Fin 2
code a = zero
code b = suc zero

name : Fin 2 → Op
name zero = a
name (suc zero) = b

name-code : ∀ o → name (code o) ≡ o
name-code a = refl
name-code b = refl

code-name : ∀ c → code (name c) ≡ c
code-name zero = refl
code-name (suc zero) = refl

rt : Op → Interval
rt a = ] # 0 , ↑ # 1 ]
rt b = [ # 1 , ↑ # 2 [

running : RunningTimes Op
running = record
  { rt = rt
  ; rt-bounded = λ { a → bounded _ ; b → bounded _ }
  ; rt-positive = λ { a → toWitness {a? = 0⁺ ⊑? lo (rt a)} _ ; b → toWitness {a? = 0⁺ ⊑? lo (rt b)} _ }
  ; rt-inhabited = λ { a → 1 / 2 , toWitness {a? = 1 / 2 ∈ⁱ? rt a} _ ; b → # 1 , toWitness {a? = # 1 ∈ⁱ? rt b} _ }
  }

sA sB sAB : _
sA = ⁅ code a ⁆
sB = ⁅ code b ⁆
sAB = ⁅ code a ⁆ ∪ ⁅ code b ⁆

------------------------------------------------------------------------
-- The decision

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

  one-pos : 0ᴰ <ᴰ # 1
  one-pos = toWitnessFalse {a? = # 1 ≤? 0ᴰ} _

open import Syntax.Grades.Exact.Expression ℚ≥0ᵀ Op 2 code code-injective running
open import Syntax.Grades.Exact.Regular.Decide ℚ≥0ᵀ Op 2 code code-injective name code-name running
  ℚ≥0-dense (# 1) one-pos ℚ≥0-commensurable

holds : ∀ {s} → Expr s → Expr s → Bool
holds {upper} e f = isYes (e ≾ᵁ? f)
holds {lower} e f = isYes (e ≾ᴸ? f)

------------------------------------------------------------------------
-- Upper bounds

-- an unbounded wait is an iteration of open stretches
u-unbounded : holds {upper} (str none ∞) ((str sAB (fin ((# 1) ∣ᶜ ⁻))) *) ≡ true
u-unbounded = refl

-- iterated b's leave no room for a stretch of a's
u-only-b : holds {upper} (str sA (fin ((# 2) ∣ᶜ ⁺))) ((ops sB) *) ≡ false
u-only-b = refl

-- an a may run for a whole unit, too long for an open wait of one and a half
u-a-wait : holds {upper} (ops sA) (str none (fin ((3 / 2) ∣ᶜ ⁻))) ≡ false
u-a-wait = refl

-- a closed wait of two is not below an open stretch of two
u-closed-open : holds {upper} (str none (fin ((# 2) ∣ᶜ ⁺))) (str sA (fin ((# 2) ∣ᶜ ⁻))) ≡ false
u-closed-open = refl

------------------------------------------------------------------------
-- Lower bounds

-- a b fits a nested iteration of operations each followed by a stretch
l-nested : holds {lower} (ops sB) ((((ops sAB) · (str sAB ((# 0) ∣ᶜ ⁻))) *) *) ≡ true
l-nested = refl

-- an iteration of operations includes the empty word, below no single one
l-star-empty : holds {lower} ((ops sAB) *) (ops sAB) ≡ false
l-star-empty = refl

-- a wait of at least a half is a wait of more than zero
l-wait : holds {lower} (str none ((1 / 2) ∣ᶜ ⁻)) (str none ((# 0) ∣ᶜ ⁺)) ≡ true
l-wait = refl

-- a single b is not a sequence of two operations around a stretch
l-short : holds {lower} (ops sB) (((ops sA) · (str sA ((1 / 2) ∣ᶜ ⁻))) · (ops sAB)) ≡ false
l-short = refl
