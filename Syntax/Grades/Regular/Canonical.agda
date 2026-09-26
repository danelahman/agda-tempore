------------------------------------------------------------------------
-- The canonical table of a regular language.                          --
--                                                                     --
-- `canon` sends a table to the minimal complete DFA of its language,  --
-- with states numbered breadth-first. Two steps:                      --
--                                                                     --
--   * Moore's partition refinement. Round `i` puts two states in one  --
--     class iff they agree on every word shorter than `i`; a round    --
--     that adds no class has reached language equivalence.            --
--   * `explore` over the quotient, whose states are the classes, so   --
--     every identification it makes is a language equality.          --
--                                                                     --
-- Canonicity (`Canonicity` below) is the statement that the result    --
-- depends only on the language.                                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)

module Syntax.Grades.Regular.Canonical (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; map; zipWith; replicate; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Data.Product.Base as Product

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Syntax.Grades.Regular.Automaton k

------------------------------------------------------------------------
-- Moore's partition refinement

module Moore (D : DFA) where

  -- a partition assigns each state its class, in state order; classes
  -- are numbered in order of first occurrence

  -- a state's signature under a partition: acceptance, then the class
  -- of each successor

  signature : List ℕ → List ℕ → Bool → List ℕ
  signature cs r f = (if f then 1 else 0) ∷ map (cs !_) r

  number : List ℕ → List (List ℕ × ℕ) → Maybe ℕ
  number σ []             = nothing
  number σ ((τ , c) ∷ τs) = if σ ==ⁿ τ then just c else number σ τs

  -- the partition with one class per signature, and its class count

  classify : List (List ℕ) → List (List ℕ × ℕ) → ℕ → List ℕ × ℕ
  classify []       known n = [] , n
  classify (σ ∷ σs) known n with number σ known
  ... | just c  = Product.map₁ (c ∷_) (classify σs known n)
  ... | nothing = Product.map₁ (n ∷_) (classify σs ((σ , n) ∷ known) (suc n))

  refine : List ℕ → List ℕ × ℕ
  refine cs = classify (zipWith (signature cs) (rows D) (finals D)) [] 0

  rounds : ℕ → List ℕ → ℕ → List ℕ × ℕ
  rounds zero       cs n = cs , n
  rounds (suc fuel) cs n with refine cs
  ... | cs' , n' = if n' ≡ᵇ n then (cs' , n') else rounds fuel cs' n'

  -- language equivalence of states, as a partition

  equivalence : List ℕ × ℕ
  equivalence = rounds (suc (size D)) (replicate (size D) 0) 1

------------------------------------------------------------------------
-- The quotient by language equivalence

-- the first state of each class; classes are numbered by first
-- occurrence, so class `c` first occurs as the `c`-th new number

representatives : ℕ → ℕ → List ℕ → List ℕ
representatives i n []       = []
representatives i n (c ∷ cs) =
  if c ≡ᵇ n then i ∷ representatives (suc i) (suc n) cs
            else representatives (suc i) n cs

-- the automaton of classes, given the partition, the class count and
-- the representatives

classes : DFA → List ℕ → ℕ → List ℕ → Automaton
classes D cs n reps = record
  { State = ℕ
  ; _≟_   = _≡ᵇ_
  ; start = cs ! 0
  ; δ     = λ c a → cs ! next D (reps ! c) a
  ; final = λ c → isFinal D (reps ! c)
  ; bound = n
  }

quotient : DFA → Automaton
quotient D = quot (Moore.equivalence D)
  where
  quot : List ℕ × ℕ → Automaton
  quot (cs , n) = classes D cs n (representatives 0 0 cs)

------------------------------------------------------------------------
-- Canonical tables

canon : DFA → DFA
canon D = explore (quotient D)

-- the canonical table of an automaton's language

normalise : Automaton → DFA
normalise A = canon (explore A)

------------------------------------------------------------------------
-- Specifications, proved in a later stage

-- tables and automata recognise the same languages

Explore-correct : Set₁
Explore-correct = ∀ A → Lawful A
                → WellFormed (explore A)
                × (∀ w → accepts (explore A) w ≡ Automaton.accepts A w)

Canon-correct : Set
Canon-correct = ∀ D → WellFormed D
              → WellFormed (canon D) × (∀ w → accepts (canon D) w ≡ accepts D w)

-- the canonical table is a function of the language
--
-- Proof plan. Call a table *reduced* if its states are reachable and
-- pairwise language-inequivalent. (1) Moore: at the fixpoint two states
-- share a class iff their languages agree, so `quotient D` is reduced up
-- to its equality test and recognises D's language. (2) Lockstep: for
-- automata A, B whose equality tests are language equality, and whose
-- start states have equal languages, `explore A ≡ explore B`, by
-- induction on the fuel with the invariant that the `seen` lists and the
-- queues are pointwise related by language equality, so each `number`
-- lookup answers alike, rows and final bits agree entry by entry. (3)
-- Fuel: both runs stop with an empty queue, since the reachable classes
-- number at most the bound.

Canonicity : Set
Canonicity = ∀ D E → WellFormed D → WellFormed E
           → (∀ w → accepts D w ≡ accepts E w) → canon D ≡ canon E

-- a canonical table is its own canonical form (from `Canonicity`
-- applied to `Canon-correct`)

Canon-idempotent : Set
Canon-idempotent = ∀ D → WellFormed D → canon (canon D) ≡ canon D
