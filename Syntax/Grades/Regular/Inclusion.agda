------------------------------------------------------------------------
-- Inclusion of regular languages, by exploring `L & ~M`.             --
--                                                                    --
-- A pair of states `(p , q)` stands for the residual `L_p ∩ ~M_q`;   --
-- its derivative by `a` is the pair of successors, and it holds the  --
-- empty word iff `p` is final and `q` is not. The pairs reachable    --
-- from `(0 , 0)` are explored breadth-first, each with the word that --
-- reached it, and the first pair holding the empty word gives a      --
-- shortest counterexample.                                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
import Data.Nat.Base as ℕ

module Syntax.Grades.Regular.Inclusion (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; not; T)
open import Data.List.Base using (List; []; _∷_; _++_; reverse)
open import Data.Maybe.Base using (Maybe; just; nothing; is-nothing)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁)
open import Data.Unit.Base using (tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Syntax.Grades.Regular.Automaton k

------------------------------------------------------------------------
-- A counterexample to `L ⊆ M`, if there is one

-- the product of `L` and `M`, each pair carrying the word that reached
-- it, reversed; the equality test compares pairs only

-- a pair holding the empty word of `L & ~M`

bad : DFA → DFA → (ℕ × ℕ) × Word → Bool
bad L M ((p , q) , _) = isFinal L p ∧ not (isFinal M q)

witnesses : DFA → DFA → Automaton
witnesses L M = record
  { State = (ℕ × ℕ) × Word
  ; _≟_   = λ { ((p , q) , _) ((p′ , q′) , _) → (p ≡ᵇ p′) ∧ (q ≡ᵇ q′) }
  ; start = (0 , 0) , []
  ; δ     = λ { ((p , q) , vʳ) a → (next L p a , next M q a) , a ∷ vʳ }
  ; final = bad L M
  ; bound = size L ℕ.* size M
  }

-- Prototype: the same search runs on derivatives of the two terms in
-- place of table rows, and finds the same counterexample.

-- the first discovered pair holding a counterexample, whose word is
-- then a shortest one

search : DFA → DFA → List ((ℕ × ℕ) × Word) → Maybe Word
search L M []              = nothing
search L M ((x , vʳ) ∷ xs) =
  if bad L M (x , vʳ) then just (reverse vʳ) else search L M xs

counterexample : DFA → DFA → Maybe Word
counterexample L M = search L M (proj₁ (Explore.discover (witnesses L M)))

_⊆ᵇ_ : DFA → DFA → Bool
L ⊆ᵇ M = is-nothing (counterexample L M)

infix 4 _⊆ᵇ_

------------------------------------------------------------------------
-- A counterexample, checked

Refutation : DFA → DFA → Set
Refutation L M = ∃ λ w → w ∈ L × ¬ (w ∈ M)

refutation-⊈ : ∀ {L M} → Refutation L M → ¬ (L ⊆ M)
refutation-⊈ (w , w∈L , w∉M) L⊆M = w∉M (L⊆M w w∈L)

refute : (L M : DFA) → Maybe (Refutation L M)
refute L M = check (counterexample L M)
  where
  check : Maybe Word → Maybe (Refutation L M)
  check nothing = nothing
  check (just w) with accepts L w in eqL | accepts M w in eqM
  ... | true  | false = just (w , subst T (sym eqL) tt , λ w∈M → subst T eqM w∈M)
  ... | _     | _     = nothing
