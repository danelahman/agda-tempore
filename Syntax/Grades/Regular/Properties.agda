------------------------------------------------------------------------
-- The operations on canonical tables are correct.                     --
--                                                                     --
-- Each operation returns a well-formed canonical table (one that      --
-- `canon` fixes) recognising the language it is named for.            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

module Syntax.Grades.Regular.Properties (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; _∨_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality

open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Canonical k
open import Syntax.Grades.Regular.Operations k
open import Syntax.Grades.Regular.Explore k using (explore-wf; explore-accepts)
open import Syntax.Grades.Regular.Canonicity k
  using (canon-idempotent; normalise-wf; normalise-accepts; explore-canonical)
open import Syntax.Grades.Regular.Constructions k

open Equivalence using (to; from)

private
  T-subst : ∀ {a b : Bool} → a ≡ b → T a ⇔ T b
  T-subst refl = mk⇔ (λ t → t) (λ t → t)

  _∘⇔_ : ∀ {A B C : Set} → B ⇔ C → A ⇔ B → A ⇔ C
  g ∘⇔ f = mk⇔ (λ a → to g (to f a)) (λ c → from f (from g c))

------------------------------------------------------------------------
-- Single words

⟦⟧-wf : ∀ w → WellFormed ⟦ w ⟧
⟦⟧-wf w = explore-wf (word w) (lawful-word w)

⟦⟧-canonical : ∀ w → canon ⟦ w ⟧ ≡ ⟦ w ⟧
⟦⟧-canonical w = explore-canonical (word w) (lawful-word w) (reduced-word w)

∈-⟦⟧ : ∀ w v → v ∈ ⟦ w ⟧ ⇔ v ≡ w
∈-⟦⟧ w v = accepts-word w v ∘⇔ T-subst (explore-accepts (word w) (lawful-word w) v)

------------------------------------------------------------------------
-- Every word

Σ*-wf : WellFormed Σ*
Σ*-wf = explore-wf everything lawful-everything

Σ*-canonical : canon Σ* ≡ Σ*
Σ*-canonical = explore-canonical everything lawful-everything reduced-everything

∈-Σ* : ∀ v → v ∈ Σ*
∈-Σ* v = subst T (sym (trans (explore-accepts everything lawful-everything v)
                             (accepts-everything v))) _

------------------------------------------------------------------------
-- Union

module _ {L M : DFA} (wfL : WellFormed L) (wfM : WellFormed M) where

  private
    A  = product _∨_ (automaton L) (automaton M)
    LA = lawful-product _∨_ (automaton L) (automaton M) (lawful-table L wfL) (lawful-table M wfM)

  ∪-wf : WellFormed (L ∪ M)
  ∪-wf = normalise-wf A LA

  ∪-canonical : canon (L ∪ M) ≡ L ∪ M
  ∪-canonical = canon-idempotent (explore A) (explore-wf A LA)

  ∪-accepts : ∀ w → accepts (L ∪ M) w ≡ (accepts L w ∨ accepts M w)
  ∪-accepts w =
    trans (normalise-accepts A LA w)
      (trans (accepts-product _∨_ (automaton L) (automaton M) w)
             (cong₂ _∨_ (accepts-table L w) (accepts-table M w)))

------------------------------------------------------------------------
-- Concatenation

module _ {L M : DFA} (wfL : WellFormed L) (wfM : WellFormed M) where

  private
    A  = concatenation (automaton L) M
    LA = lawful-concatenation L M wfL wfM

  ·-wf : WellFormed (L · M)
  ·-wf = normalise-wf A LA

  ·-canonical : canon (L · M) ≡ L · M
  ·-canonical = canon-idempotent (explore A) (explore-wf A LA)

  ∈-· : ∀ w → w ∈ (L · M) ⇔ (∃₂ λ u v → w ≡ u ++ v × u ∈ L × v ∈ M)
  ∈-· w = accepts-concatenation L M wfL wfM w ∘⇔ T-subst (normalise-accepts A LA w)

------------------------------------------------------------------------
-- Iteration

module _ {L : DFA} (wfL : WellFormed L) where

  private
    A  = iteration L
    LA = lawful-iteration L wfL

  *-wf : WellFormed (L *)
  *-wf = normalise-wf A LA

  *-canonical : canon (L *) ≡ L *
  *-canonical = canon-idempotent (explore A) (explore-wf A LA)

  ∈-* : ∀ w → w ∈ (L *) ⇔ w ∈* L
  ∈-* w = accepts-iteration L wfL w ∘⇔ T-subst (normalise-accepts A LA w)
