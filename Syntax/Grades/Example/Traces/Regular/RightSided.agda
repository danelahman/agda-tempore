------------------------------------------------------------------------
-- Regular sets of timed traces as upper bounds, at the subset order. --
--                                                                    --
-- A grade is a non-empty regular set of timed traces, read against   --
-- the runs `X` a computation may have as                             --
--                                                                    --
--   X is graded by L   iff   every run in X is permitted by L        --
--                                                                    --
-- where `L` permits a run when the encoding of the run is in `L`.    --
-- Weakening is inclusion, the product sequences runs, the join is    --
-- union, `⊤` permits every run, and `u` permits only the empty run.  --
-- The greatest element, the set of all runs, lies in the carrier and --
-- is not absorbing: `{ ⟨1⟩ } · ⊤` permits only runs beginning with a --
-- delay.                                                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Syntax.Grades.Example.Traces.Regular.RightSided
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.List.Base using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Example.Traces.Regular.Base Op n code code-injective
  using (Word; DFA; _∈_; tick; op; enc; enc-∙; enc-⟨⟩)
open import Syntax.Grades.Traces.Base Op using (Trace; _∙_; ⟨_⟩)

open import Syntax.Grades.Regular.Grade (suc n) zero public

------------------------------------------------------------------------
-- Reading a grade as a set of runs

_permits_ : Regular → Trace → Set
L permits t = enc t ∈ table L

infix 4 _permits_

-- the grade permitting exactly one run

run : Trace → Regular
run t = ⟪ enc t ⟫

permits-run : ∀ t → run t permits t
permits-run t = ∈⟪⟫⁺ (enc t)

-- a single operation

operationᴿ : Op → Regular
operationᴿ o = ⟪ op o ∷ [] ⟫

-- sequencing permitted runs gives a run the product permits

permits-∙ : ∀ L M {s t} → L permits s → M permits t → (L ·ᴿ M) permits (s ∙ t)
permits-∙ L M {s} {t} s∈ t∈ =
  subst (λ v → v ∈ table (L ·ᴿ M)) (sym (enc-∙ s t)) (∈·⁺ L M (enc s) (enc t) s∈ t∈)

-- `of-nat m` permits the delay of duration `m`

permits-⟨⟩ : ∀ m → of-nat m permits ⟨ m ⟩
permits-⟨⟩ m = subst (λ v → v ∈ table (of-nat m)) (sym (enc-⟨⟩ m)) (∈tick⁺ m)

------------------------------------------------------------------------
-- Literals: extended regular expressions over the letters

open import Syntax.Grades.Regular.Expression (suc n) public
open import Syntax.Grades.Regular.Literal (suc n) zero public

-- an operation, and a delay of `m` ticks

‵op : Op → Expr
‵op o = ‵ op o

delay : ℕ → Expr
delay m = tick ^ m

------------------------------------------------------------------------
-- The grade

right-sided : Grade
right-sided = regular-grade
