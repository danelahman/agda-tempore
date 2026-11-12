------------------------------------------------------------------------
-- The canonical table of a regular language.                         --
--                                                                    --
-- `canon` sends a table to the quotient of its reachable states by   --
-- language equivalence, a complete DFA of its language, with states  --
-- numbered breadth-first. Two steps:                                 --
--                                                                    --
--   * Moore's partition refinement. Round `i` puts two states in one --
--     class iff they agree on every word shorter than `i`; a round   --
--     that adds no class has reached language equivalence.           --
--   * `explore` over the quotient, whose states are the classes, so  --
--     every identification it makes is a language equality.          --
--                                                                    --
-- Canonicity (`Canonicity` below) is the statement that the result   --
-- depends only on the language.                                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)

module Grades.Regular.Canonical (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; map; zipWith; replicate; length)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Grades.Regular.Automaton k

------------------------------------------------------------------------
-- Moore's partition refinement

module Moore (D : DFA) where

  -- a partition assigns each state, in state order, its class: the
  -- least state in the class

  -- a state's signature under a partition: acceptance, then the class
  -- of each successor

  signature : List ℕ → List ℕ → Bool → List ℕ
  signature cs r f = (if f then 1 else 0) ∷ map (cs !_) r

  signatures : List ℕ → List (List ℕ)
  signatures cs = zipWith (signature cs) (rows D) (finals D)

  -- the first position holding a signature

  first : List ℕ → List (List ℕ) → ℕ
  first σ []       = 0
  first σ (τ ∷ τs) = if σ ==ⁿ τ then 0 else suc (first σ τs)

  classify : List (List ℕ) → List ℕ
  classify σs = map (λ σ → first σ σs) σs

  refine : List ℕ → List ℕ
  refine cs = classify (signatures cs)

  -- refine until the partition is stable

  rounds : ℕ → List ℕ → List ℕ
  rounds zero       cs = cs
  rounds (suc fuel) cs = settle (refine cs)
    where
    settle : List ℕ → List ℕ
    settle cs′ = if cs′ ==ⁿ cs then cs else rounds fuel cs′

  -- language equivalence of states, as a partition

  equivalence : List ℕ
  equivalence = rounds (suc (size D)) (replicate (size D) 0)

------------------------------------------------------------------------
-- The quotient by language equivalence

-- a state of the quotient is a class together with a state in it; the
-- equality test compares classes

classes : DFA → List ℕ → Automaton
classes D cs = record
  { State = ℕ × ℕ
  ; _≟_   = λ { (c , _) (c′ , _) → c ≡ᵇ c′ }
  ; start = enter 0
  ; δ     = λ { (_ , p) a → enter (next D p a) }
  ; final = λ { (_ , p) → isFinal D p }
  ; bound = size D
  }
  where
  enter : ℕ → ℕ × ℕ
  enter p = cs ! p , p

quotient : DFA → Automaton
quotient D = classes D (Moore.equivalence D)

------------------------------------------------------------------------
-- Canonical tables

canon : DFA → DFA
canon D = explore (quotient D)

-- the canonical table of an automaton's language

normalise : Automaton → DFA
normalise A = canon (explore A)
