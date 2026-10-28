-------------------------------------------------------------------------
-- Intersection, complement, and the single letters.                   --
--                                                                     --
-- Intersection is the product automaton at `_∧_`; the complement of a --
-- complete deterministic automaton flips its final states. Both are   --
-- lawful when their arguments are, and are canonicalised like the     --
-- other operations.                                                   --
-------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _<_; _≤_; z≤n; s≤s)

module Grades.Regular.Boolean (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; not; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≤-refl)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import Grades.Regular.Automaton k
open import Grades.Regular.Canonical k
open import Grades.Regular.Operations k using (product; accepts-product)
open import Grades.Regular.Explore k using (explore-wf)
open import Grades.Regular.Canonicity k
  using (canon-idempotent; normalise-wf; normalise-accepts)
open import Grades.Regular.Constructions k using (lawful-table; accepts-table; lawful-product)
open import Grades.Regular.Constructions.Base k using (lawful-exact; ≡ᵇ-refl)

------------------------------------------------------------------------
-- Complement

complement : Automaton → Automaton
complement A = record A { final = λ p → not (Automaton.final A p) }

δ*-complement : ∀ A p w → Automaton.δ* (complement A) p w ≡ Automaton.δ* A p w
δ*-complement A p []      = refl
δ*-complement A p (a ∷ w) = δ*-complement A (Automaton.δ A p a) w

accepts-complement : ∀ A w → Automaton.accepts (complement A) w ≡ not (Automaton.accepts A w)
accepts-complement A w = cong (λ q → not (Automaton.final A q)) (δ*-complement A (Automaton.start A) w)

lawful-complement : ∀ A → Lawful A → Lawful (complement A)
lawful-complement A LA = record
  { Good       = Good
  ; good-start = good-start
  ; good-δ     = good-δ
  ; ≟-refl     = ≟-refl
  ; ≟-sym      = ≟-sym
  ; ≟-trans    = ≟-trans
  ; ≟-final    = λ g g′ t → cong not (≟-final g g′ t)
  ; ≟-δ        = ≟-δ
  ; enum       = enum
  ; enum-bound = enum-bound
  ; enum-cover = enum-cover
  }
  where open Lawful LA

------------------------------------------------------------------------
-- Any single letter
--
-- State 0: nothing read; 1: one letter read; 2: more than one.

one : Automaton
one = record
  { State = ℕ
  ; _≟_   = _≡ᵇ_
  ; start = 0
  ; δ     = λ q _ → if q ≡ᵇ 0 then 1 else 2
  ; final = λ q → q ≡ᵇ 1
  ; bound = 3
  }

private
  one-good : ∀ {q} (a : Letter) → q < 3 → Automaton.δ one q a < 3
  one-good {zero}  a _ = s≤s (s≤s z≤n)
  one-good {suc q} a _ = s≤s (s≤s (s≤s z≤n))

  one-cover : ∀ {q} → q < 3 → q ∈ˡ (0 ∷ 1 ∷ 2 ∷ [])
  one-cover {zero}          _                     = here refl
  one-cover {suc zero}      _                     = there (here refl)
  one-cover {suc (suc zero)} _                    = there (there (here refl))
  one-cover {suc (suc (suc q))} (s≤s (s≤s (s≤s ())))

lawful-one : Lawful one
lawful-one =
  lawful-exact one (λ {p} {q} t → ≡ᵇ⇒≡ p q t) ≡ᵇ-refl
    (_< 3) (s≤s z≤n) one-good (0 ∷ 1 ∷ 2 ∷ []) ≤-refl one-cover

accepts-one : ∀ w → T (Automaton.accepts one w) ⇔ (∃ λ a → w ≡ a ∷ [])
accepts-one w = mk⇔ (to w) (λ { (a , refl) → tt })
  where
  stuck : ∀ w → Automaton.δ* one 2 w ≡ 2
  stuck []      = refl
  stuck (a ∷ w) = stuck w

  to : ∀ w → T (Automaton.accepts one w) → ∃ λ a → w ≡ a ∷ []
  to []          ()
  to (a ∷ [])    _ = a , refl
  to (a ∷ b ∷ w) t rewrite stuck w with t
  ... | ()

------------------------------------------------------------------------
-- The operations on canonical tables

_∩_ : DFA → DFA → DFA
L ∩ M = normalise (product _∧_ (automaton L) (automaton M))

∁_ : DFA → DFA
∁ L = normalise (complement (automaton L))

Σ₁ : DFA
Σ₁ = normalise one

infixl 7 _∩_
infix  8 ∁_

module _ {L M : DFA} (wfL : WellFormed L) (wfM : WellFormed M) where

  private
    A  = product _∧_ (automaton L) (automaton M)
    LA = lawful-product _∧_ (automaton L) (automaton M) (lawful-table L wfL) (lawful-table M wfM)

  ∩-wf : WellFormed (L ∩ M)
  ∩-wf = normalise-wf A LA

  ∩-canonical : canon (L ∩ M) ≡ L ∩ M
  ∩-canonical = canon-idempotent (explore A) (explore-wf A LA)

  ∩-accepts : ∀ w → accepts (L ∩ M) w ≡ (accepts L w ∧ accepts M w)
  ∩-accepts w =
    trans (normalise-accepts A LA w)
      (trans (accepts-product _∧_ (automaton L) (automaton M) w)
             (cong₂ _∧_ (accepts-table L w) (accepts-table M w)))

module _ {L : DFA} (wfL : WellFormed L) where

  private
    A  = complement (automaton L)
    LA = lawful-complement (automaton L) (lawful-table L wfL)

  ∁-wf : WellFormed (∁ L)
  ∁-wf = normalise-wf A LA

  ∁-canonical : canon (∁ L) ≡ ∁ L
  ∁-canonical = canon-idempotent (explore A) (explore-wf A LA)

  ∁-accepts : ∀ w → accepts (∁ L) w ≡ not (accepts L w)
  ∁-accepts w =
    trans (normalise-accepts A LA w)
      (trans (accepts-complement (automaton L) w) (cong not (accepts-table L w)))

Σ₁-wf : WellFormed Σ₁
Σ₁-wf = normalise-wf one lawful-one

Σ₁-canonical : canon Σ₁ ≡ Σ₁
Σ₁-canonical = canon-idempotent (explore one) (explore-wf one lawful-one)

∈-Σ₁ : ∀ w → w ∈ Σ₁ ⇔ (∃ λ a → w ≡ a ∷ [])
∈-Σ₁ w = mk⇔ (λ t → to (accepts-one w) (subst T (normalise-accepts one lawful-one w) t))
             (λ h → subst T (sym (normalise-accepts one lawful-one w)) (from (accepts-one w) h))
  where open Function.Bundles.Equivalence using (to; from)
        import Function.Bundles
