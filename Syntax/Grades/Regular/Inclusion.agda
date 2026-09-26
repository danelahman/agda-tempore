------------------------------------------------------------------------
-- Inclusion of regular languages, by exploring `L & ~M`.              --
--                                                                     --
-- A pair of states `(p , q)` stands for the residual `L_p ∩ ~M_q`;    --
-- its derivative by `a` is the pair of successors, and it holds the   --
-- empty word iff `p` is final and `q` is not. The pairs reachable     --
-- from `(0 , 0)` are explored breadth-first, each with the word that  --
-- reached it, and exploration stops at the first pair holding the     --
-- empty word, whose word is then a shortest counterexample.           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
import Data.Nat.Base as ℕ

module Syntax.Grades.Regular.Inclusion (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; not; T)
open import Data.Bool.ListAction using (or)
open import Data.List.Base using (List; []; _∷_; _++_; reverse)
open import Data.Maybe.Base using (Maybe; just; nothing; is-nothing)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Unit.Base using (tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Syntax.Grades.Regular.Automaton k

------------------------------------------------------------------------
-- A counterexample to `L ⊆ M`, if there is one

module _ (L M : DFA) where

  private
    Pair : Set
    Pair = ℕ × ℕ

    seen? : Pair → List Pair → Bool
    seen? _       []                = false
    seen? (p , q) ((p' , q') ∷ ps) =
      if (p ≡ᵇ p') ∧ (q ≡ᵇ q') then true else seen? (p , q) ps

    -- the unseen successors of a pair, newest first, each with the
    -- reversed word reaching it

    successors : List Letter → Pair → Word
               → List Pair → List (Pair × Word) → List Pair × List (Pair × Word)
    successors []       _       _  seen new = seen , new
    successors (a ∷ as) (p , q) vʳ seen new
      with seen? (next L p a , next M q a) seen
    ... | true  = successors as (p , q) vʳ seen new
    ... | false =
      successors as (p , q) vʳ
        ((next L p a , next M q a) ∷ seen)
        (((next L p a , next M q a) , a ∷ vʳ) ∷ new)

    go : ℕ → List (Pair × Word) → List Pair → Maybe Word
    go _          []                    _    = nothing
    go zero       (_ ∷ _)               _    = nothing
    go (suc fuel) (((p , q) , vʳ) ∷ qs) seen =
      if isFinal L p ∧ not (isFinal M q) then just (reverse vʳ)
      else expand (successors letters (p , q) vʳ seen [])
      where
      expand : List Pair × List (Pair × Word) → Maybe Word
      expand (seen' , new) = go fuel (qs ++ reverse new) seen'

  counterexample : Maybe Word
  counterexample =
    go (size L ℕ.* size M) (((0 , 0) , []) ∷ []) ((0 , 0) ∷ [])

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

------------------------------------------------------------------------
-- Non-emptiness: every state of an explored table is reachable

inhabited : DFA → Bool
inhabited D = or (finals D)

------------------------------------------------------------------------
-- Specifications, proved in a later stage

-- no counterexample is found only when there is none

Inclusion-complete : Set
Inclusion-complete = ∀ L M → WellFormed L → WellFormed M
                   → counterexample L M ≡ nothing → L ⊆ M

-- a counterexample is found whenever there is one

Inclusion-sound : Set
Inclusion-sound = ∀ L M → L ⊆ M → counterexample L M ≡ nothing
