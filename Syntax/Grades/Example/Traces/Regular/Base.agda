------------------------------------------------------------------------
-- Regular sets of timed traces over a finite set of operations.       --
--                                                                     --
-- A timed trace is a word over `Op ⊎ tick`, a delay `d` being the     --
-- block `tickᵈ`. The operations are coded into `Fin n`, and the       --
-- letters are `Fin (suc n)` with `tick` first.                        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero; suc)

module Syntax.Grades.Example.Traces.Regular.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n) where

open import Data.List.Base using (_∷_; [])

open import Syntax.Grades.Regular.Automaton  (suc n) public
open import Syntax.Grades.Regular.Canonical  (suc n) public
open import Syntax.Grades.Regular.Operations (suc n) public
open import Syntax.Grades.Regular.Inclusion  (suc n) public

tick : Letter
tick = zero

op : Op → Letter
op o = suc (code o)

-- a single operation

⌈_⌉ : Op → DFA
⌈ o ⌉ = ⟦ op o ∷ [] ⟧

-- a delay of `d` ticks

⟨_⟩ : ℕ → DFA
⟨ d ⟩ = tick ^ d

-- the grade structure

u : DFA
u = ε

⊤ : DFA
⊤ = Σ*

_⊔_ : DFA → DFA → DFA
_⊔_ = _∪_

of-nat : ℕ → DFA
of-nat = ⟨_⟩

infixl 6 _⊔_
