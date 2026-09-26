------------------------------------------------------------------------
-- Operations on regular languages, held as canonical tables.          --
--                                                                     --
-- Each operation is a finite-state automaton, explored, and then      --
-- canonicalised unless the automaton is already reduced. A state      --
-- stands for a residual language, and each transition is              --
-- Brzozowski's derivative equation on residuals:                      --
--                                                                     --
--   a⁻¹(L ∪ M)  = a⁻¹L ∪ a⁻¹M                  (pairs of states)      --
--   a⁻¹(L · M)  = (a⁻¹L) · M ∪ [ε ∈ L] a⁻¹M    (a state and a set)    --
--   a⁻¹(L *)    = (a⁻¹L) · L *                 (a set of states)      --
--                                                                     --
-- Termination is the finiteness of the state types; the bound each    --
-- automaton carries is their size.                                    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
import Data.Nat.Base as ℕ

module Syntax.Grades.Regular.Operations (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.List.Base using (List; []; _∷_; map; foldr; replicate; length)
open import Data.Bool.ListAction using (any)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Canonical k

------------------------------------------------------------------------
-- Finite sets of states, as strictly increasing lists

insert : ℕ → List ℕ → List ℕ
insert n []       = n ∷ []
insert n (m ∷ ms) =
  if n ≡ᵇ m then m ∷ ms
  else if n <ᵇ m then n ∷ m ∷ ms
  else m ∷ insert n ms

fromList : List ℕ → List ℕ
fromList = foldr insert []

------------------------------------------------------------------------
-- A single word
--
-- State `just i`: the residual after the first `i` letters of `w`.
-- State `nothing`: the empty residual.

module Single (w : Word) where

  step : Maybe ℕ → Letter → Maybe ℕ
  step nothing  a = nothing
  step (just i) a with w ‼ i
  ... | just b  = if a ≟ᴸ b then just (suc i) else nothing
  ... | nothing = nothing

  accepting : Maybe ℕ → Bool
  accepting nothing  = false
  accepting (just i) = i ≡ᵇ length w

  same : Maybe ℕ → Maybe ℕ → Bool
  same nothing  nothing  = true
  same (just i) (just j) = i ≡ᵇ j
  same _        _        = false

  word : Automaton
  word = record
    { State = Maybe ℕ
    ; _≟_   = same
    ; start = just 0
    ; δ     = step
    ; final = accepting
    ; bound = suc (suc (length w))
    }

open Single public using (word)

------------------------------------------------------------------------
-- Every word

everything : Automaton
everything = record
  { State = ⊤
  ; _≟_   = λ _ _ → true
  ; start = tt
  ; δ     = λ _ _ → tt
  ; final = λ _ → true
  ; bound = 1
  }

------------------------------------------------------------------------
-- Boolean combinations: the product automaton

product : (Bool → Bool → Bool) → Automaton → Automaton → Automaton
product f A B = record
  { State = A.State × B.State
  ; _≟_   = λ { (p , q) (p' , q') → (p A.≟ p') ∧ (q B.≟ q') }
  ; start = A.start , B.start
  ; δ     = λ { (p , q) a → A.δ p a , B.δ q a }
  ; final = λ { (p , q) → f (A.final p) (B.final q) }
  ; bound = A.bound ℕ.* B.bound
  }
  where
  module A = Automaton A
  module B = Automaton B

δ*-product : (f : Bool → Bool → Bool) (A B : Automaton)
           → ∀ p q w
           → Automaton.δ* (product f A B) (p , q) w
           ≡ (Automaton.δ* A p w , Automaton.δ* B q w)
δ*-product f A B p q []      = refl
δ*-product f A B p q (a ∷ w) =
  δ*-product f A B (Automaton.δ A p a) (Automaton.δ B q a) w

accepts-product : (f : Bool → Bool → Bool) (A B : Automaton) → ∀ w
                → Automaton.accepts (product f A B) w
                ≡ f (Automaton.accepts A w) (Automaton.accepts B w)
accepts-product f A B w
  rewrite δ*-product f A B (Automaton.start A) (Automaton.start B) w = refl

------------------------------------------------------------------------
-- Concatenation: the subset construction
--
-- State `(p , S)` stands for `L_p · M ∪ ⋃_{q ∈ S} M_q`, with `0 ∈ S`
-- whenever `p` is final.

module Concatenation (A : Automaton) (M : DFA) where

  module A = Automaton A

  enter : A.State → List ℕ → A.State × List ℕ
  enter p S = p , (if A.final p then insert 0 S else S)

  _≟ˢ_ : List ℕ → List ℕ → Bool
  _≟ˢ_ = _==ⁿ_

  concatenation : Automaton
  concatenation = record
    { State = A.State × List ℕ
    ; _≟_   = λ { (p , S) (p' , S') → (p A.≟ p') ∧ (S ≟ˢ S') }
    ; start = enter A.start []
    ; δ     = λ { (p , S) a →
                  enter (A.δ p a) (fromList (map (λ q → next M q a) S)) }
    ; final = λ { (p , S) → any (isFinal M) S }
    ; bound = A.bound ℕ.* 2 ℕ.^ size M
    }

open Concatenation public using (concatenation)

------------------------------------------------------------------------
-- Kleene star: a set construction
--
-- State `nothing` stands for `L *`; state `just S` for
-- `⋃_{q ∈ S} L_q · L *`, with `0 ∈ S` whenever some member is final.

module Iteration (L : DFA) where

  close : List ℕ → List ℕ
  close S = if any (isFinal L) S then insert 0 S else S

  step : Maybe (List ℕ) → Letter → Maybe (List ℕ)
  step nothing  a = just (close (next L 0 a ∷ []))
  step (just S) a = just (close (fromList (map (λ q → next L q a) S)))

  accepting : Maybe (List ℕ) → Bool
  accepting nothing  = true
  accepting (just S) = any (isFinal L) S

  same : Maybe (List ℕ) → Maybe (List ℕ) → Bool
  same nothing  nothing  = true
  same (just S) (just T) = S ==ⁿ T
  same _        _        = false

  iteration : Automaton
  iteration = record
    { State = Maybe (List ℕ)
    ; _≟_   = same
    ; start = nothing
    ; δ     = step
    ; final = accepting
    ; bound = suc (2 ℕ.^ size L)
    }

open Iteration public using (iteration)

------------------------------------------------------------------------
-- The operations on canonical tables

-- `word w` and `everything` are reduced, so exploring them already gives
-- canonical tables

⟦_⟧ : Word → DFA
⟦ w ⟧ = explore (word w)

ε : DFA
ε = ⟦ [] ⟧

_^_ : Letter → ℕ → DFA
a ^ n = ⟦ replicate n a ⟧

Σ* : DFA
Σ* = explore everything

_∪_ : DFA → DFA → DFA
L ∪ M = normalise (product _∨_ (automaton L) (automaton M))

_·_ : DFA → DFA → DFA
L · M = normalise (concatenation (automaton L) M)

_* : DFA → DFA
L * = normalise (iteration L)

infixl 6 _∪_
infixl 7 _·_
infix  8 _*
