------------------------------------------------------------------------
-- Whether two regular languages meet.                                --
--                                                                    --
-- A common word of `L` and `M` is a word of `L` outside the          --
-- complement of `M`, the table of `M` with its final bits flipped.   --
-- So the counterexample search of `L ⊆ ∁ M` (`Regular.Inclusion`),   --
-- exploring the pairs of states of `L` and `M` reachable together,   --
-- decides whether `L ∩ M` is inhabited, and finds a common word when --
-- it is.                                                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _<_; s≤s)

module Grades.Regular.Meet (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; not)
open import Data.Bool.Properties using (not-involutive)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Properties using (length-map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no; recompute)

open import Grades.Regular.Automaton k
open import Grades.Regular.Basics k using (run-<; start-<; T-not⁺; T-not⁻)
open import Grades.Regular.Inclusion k using (counterexample)
open import Grades.Regular.Decide k using (counterexample-sound; counterexample-complete; wellFormed?)

------------------------------------------------------------------------
-- The complement of a table, on the same states

flip : DFA → DFA
flip D = dfa (rows D) (map not (finals D))

private
  lookup-not : ∀ fs {q} → q < length fs → lookupOr false (map not fs) q ≡ not (lookupOr false fs q)
  lookup-not (f ∷ fs) {zero}  _        = refl
  lookup-not (f ∷ fs) {suc q} (s≤s lt) = lookup-not fs lt

  run-flip : ∀ D q w → run (flip D) q w ≡ run D q w
  run-flip D q []      = refl
  run-flip D q (a ∷ w) = run-flip D (next D q a) w

module _ {M : DFA} (wf : WellFormed M) where

  flip-wf : WellFormed (flip M)
  flip-wf = proj₁ wf , trans (length-map not (finals M)) (proj₁ (proj₂ wf)) , proj₂ (proj₂ wf)

  flip-accepts : ∀ w → accepts (flip M) w ≡ not (accepts M w)
  flip-accepts w rewrite run-flip M 0 w =
    lookup-not (finals M) (subst (run M 0 w <_) (sym (proj₁ (proj₂ wf))) (run-< M wf w (start-< M wf)))

------------------------------------------------------------------------
-- A common word, decided

Meet : DFA → DFA → Set
Meet L M = ∃ λ w → w ∈ L × w ∈ M

-- the tables' well-formedness is irrelevant to the search, so it is
-- taken irrelevantly and never evaluated in deciding

module _ {L M : DFA} where

  private
    module _ (wfM : WellFormed M) where
      ∈-flip⁻ : ∀ w → ¬ (w ∈ flip M) → w ∈ M
      ∈-flip⁻ w w∉ with accepts M w in e
      ... | true  = _
      ... | false = w∉ (subst T (sym (trans (flip-accepts {M} wfM w) (cong not e))) _)

      ∈-flip⁺ : ∀ w → w ∈ M → ¬ (w ∈ flip M)
      ∈-flip⁺ w w∈ w∈′ = T-not⁻ (subst T (flip-accepts {M} wfM w) w∈′) w∈

    just≢nothing : ∀ {v : Word} → just v ≢ nothing
    just≢nothing ()

    decide : WellFormed L → WellFormed M → (r : Maybe Word) → counterexample L (flip M) ≡ r
           → Dec (Meet L M)
    decide wfL wfM (just w) eq = yes (w , proj₁ s , ∈-flip⁻ wfM w (proj₂ s))
      where s = counterexample-sound {L} {flip M} wfL (flip-wf {M} wfM) eq
    decide wfL wfM nothing  eq = no λ (w , w∈L , w∈M) →
      just≢nothing (trans (sym (proj₂ (counterexample-complete {L} {flip M} wfL (flip-wf {M} wfM)
                                         {w} w∈L (∈-flip⁺ wfM w w∈M)))) eq)

  meet? : .(WellFormed L) → .(WellFormed M) → Dec (Meet L M)
  meet? wfL wfM =
    decide (recompute (wellFormed? L) wfL) (recompute (wellFormed? M) wfM) (counterexample L (flip M)) refl
