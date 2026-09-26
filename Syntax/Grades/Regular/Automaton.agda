------------------------------------------------------------------------
-- Deterministic automata over a finite alphabet, and their tables.    --
--                                                                     --
-- The alphabet is `Fin k`. An `Automaton` has an arbitrary state type --
-- with a Boolean equality test and a bound on its reachable states;   --
-- the constructions on languages are automata of this kind. A `DFA`   --
-- is a table: state `q` is row `q`, whose `a`-th entry is the target  --
-- of letter `a`, and state 0 is the start.                            --
--                                                                     --
-- `explore` numbers the reachable states of an automaton in breadth-  --
-- first order, letters in increasing order, and returns its table.    --
-- Its only decisions are the automaton's equality tests.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _≤_; _<_)

module Syntax.Grades.Regular.Automaton (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; length; map; allFin)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Letters and words

Letter : Set
Letter = Fin k

Word : Set
Word = List Letter

letters : List Letter
letters = allFin k

_≟ᴸ_ : Letter → Letter → Bool
a ≟ᴸ b = toℕ a ≡ᵇ toℕ b

------------------------------------------------------------------------
-- Automata

record Automaton : Set₁ where
  field
    State : Set
    _≟_   : State → State → Bool
    start : State
    δ     : State → Letter → State
    final : State → Bool
    bound : ℕ

  δ* : State → Word → State
  δ* q []      = q
  δ* q (a ∷ w) = δ* (δ q a) w

  accepts : Word → Bool
  accepts w = final (δ* start w)

-- the conditions under which `explore` is correct: `_≟_` is an
-- equivalence, a congruence on the `Good` states, which are closed under
-- transitions, and `bound` of them represent every `Good` state up to it

record Lawful (A : Automaton) : Set₁ where
  open Automaton A
  field
    Good       : State → Set
    good-start : Good start
    good-δ     : ∀ {p} a → Good p → Good (δ p a)
    ≟-refl     : ∀ p → T (p ≟ p)
    ≟-sym      : ∀ {p q} → T (p ≟ q) → T (q ≟ p)
    ≟-trans    : ∀ {p q r} → T (p ≟ q) → T (q ≟ r) → T (p ≟ r)
    ≟-final    : ∀ {p q} → Good p → Good q → T (p ≟ q) → final p ≡ final q
    ≟-δ        : ∀ {p q} → Good p → Good q → T (p ≟ q)
               → ∀ a → T (δ p a ≟ δ q a)
    enum       : List State
    enum-bound : length enum ≤ bound
    enum-cover : ∀ {p} → Good p → Any (λ q → T (p ≟ q)) enum

-- `_≟_` identifies `Good` states with equal residuals

Reduced : (A : Automaton) → Lawful A → Set
Reduced A LA = ∀ {p q} → Good p → Good q
             → (∀ w → final (δ* p w) ≡ final (δ* q w)) → T (p ≟ q)
  where open Automaton A
        open Lawful LA

------------------------------------------------------------------------
-- Tables

record DFA : Set where
  constructor dfa
  field
    rows   : List (List ℕ)
    finals : List Bool

open DFA public

-- total lookup, out of range at a default

lookupOr : {A : Set} → A → List A → ℕ → A
lookupOr d []       _       = d
lookupOr d (x ∷ xs) zero    = x
lookupOr d (x ∷ xs) (suc i) = lookupOr d xs i

_!_ : List ℕ → ℕ → ℕ
_!_ = lookupOr 0

next : DFA → ℕ → Letter → ℕ
next D q a = lookupOr [] (rows D) q ! toℕ a

isFinal : DFA → ℕ → Bool
isFinal D = lookupOr false (finals D)

size : DFA → ℕ
size D = length (rows D)

-- a table is well formed when it has a start state, a final bit per
-- state, and a row of in-range targets per state, one per letter

WellFormed : DFA → Set
WellFormed D = 0 < size D
             × length (finals D) ≡ size D
             × All (λ r → length r ≡ k × All (_< size D) r) (rows D)

automaton : DFA → Automaton
automaton D = record
  { State = ℕ
  ; _≟_   = _≡ᵇ_
  ; start = 0
  ; δ     = next D
  ; final = isFinal D
  ; bound = size D
  }

-- the language of a table

run : DFA → ℕ → Word → ℕ
run D q []      = q
run D q (a ∷ w) = run D (next D q a) w

accepts : DFA → Word → Bool
accepts D w = isFinal D (run D 0 w)

_∈_ : Word → DFA → Set
w ∈ D = T (accepts D w)

_⊆_ : DFA → DFA → Set
L ⊆ M = ∀ w → w ∈ L → w ∈ M

-- equality of tables

_==ⁿ_ : List ℕ → List ℕ → Bool
[]       ==ⁿ []       = true
(m ∷ ms) ==ⁿ (n ∷ ns) = (m ≡ᵇ n) ∧ (ms ==ⁿ ns)
_        ==ⁿ _        = false

_==ᵇ_ : List Bool → List Bool → Bool
[]           ==ᵇ []           = true
(true  ∷ bs) ==ᵇ (true  ∷ cs) = bs ==ᵇ cs
(false ∷ bs) ==ᵇ (false ∷ cs) = bs ==ᵇ cs
_            ==ᵇ _            = false

_==ʳ_ : List (List ℕ) → List (List ℕ) → Bool
[]       ==ʳ []       = true
(r ∷ rs) ==ʳ (s ∷ ss) = (r ==ⁿ s) ∧ (rs ==ʳ ss)
_        ==ʳ _        = false

_==ᴰ_ : DFA → DFA → Bool
L ==ᴰ M = (rows L ==ʳ rows M) ∧ (finals L ==ᵇ finals M)

infix 4 _==ᴰ_

------------------------------------------------------------------------
-- Breadth-first exploration

-- the element at a position

_‼_ : {A : Set} → List A → ℕ → Maybe A
[]       ‼ _     = nothing
(x ∷ xs) ‼ zero  = just x
(x ∷ xs) ‼ suc i = xs ‼ i

module Explore (A : Automaton) where

  open Automaton A

  -- `D` lists the states discovered so far, in order of discovery; a
  -- state's number is its position in `D`

  index : State → List State → Maybe ℕ
  index q []       = nothing
  index q (p ∷ ps) = if q ≟ p then just 0 else Maybe.map suc (index q ps)

  visit : State → List State → ℕ × List State
  visit q D with index q D
  ... | just i  = i , D
  ... | nothing = length D , D ++ q ∷ []

  row : List Letter → State → List State → List ℕ × List State
  row []       q D = [] , D
  row (a ∷ as) q D with visit (δ q a) D
  ... | i , D′ with row as q D′
  ...   | is , D″ = i ∷ is , D″

  -- state `i` is the next to process; `rs` holds the rows of states
  -- `0 … i - 1`

  go : ℕ → ℕ → List State → List (List ℕ) → List State × List (List ℕ)
  go zero       i D rs = D , rs
  go (suc fuel) i D rs with D ‼ i
  ... | nothing = D , rs
  ... | just q with row letters q D
  ...   | r , D′ = go fuel (suc i) D′ (rs ++ r ∷ [])

  table : List State × List (List ℕ) → DFA
  table (D , rs) = dfa rs (map final D)

  discover : List State × List (List ℕ)
  discover = go bound 0 (start ∷ []) []

  explore : DFA
  explore = table discover

open Explore public using (explore)
