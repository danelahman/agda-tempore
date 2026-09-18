------------------------------------------------------------------------
-- A time-ticks Kripke frame for the subset grade of upper bounds.     --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only elapsed time, --
-- so a grade is read through the durations of the runs it lists, and  --
-- moving between worlds may take no longer than one of them:          --
--                                                                    --
--   w ⊑ᵗ[ Q ] w'   iff   w' ≤ w + duration q   for some q ∈ Q         --
--                                                                    --
-- The quantifier is existential because the grade's own order is      --
-- inclusion in the permitting direction: a weaker grade lists *more*  --
-- runs, so a condition that must survive weakening has to be met by   --
-- one listed run rather than by all of them.                          --
--                                                                    --
-- READING. The grade is a cap on which runs may occur; the tick world --
-- keeps only how long the slowest of them takes, so `⌈ write ⌉` and   --
-- `⟨ 3 ⟩` -- distinct grades here, neither below the other -- reach   --
-- the same time points.                                               --
--                                                                    --
-- Covariance is immediate: a listed run of the smaller grade is       --
-- literally a listed run of the larger one, the comparison between    --
-- traces being equality.                                              --
--                                                                    --
-- The grade's `any-run` lists no run at all, so it relates            --
-- every pair of worlds.                                               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costʰⁱ : Op → ℕ) where

open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-mono-≤; +-identityʳ)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ using (∈-⊑)
open import Syntax.Grades.Example.Traces.Subsets.RightSided Op _≟ₒ_
  using (right-sided; Permits; permitting_; any-run; _·ᵖ_; _≾_)

open import DenotationalSemantics.Model.World

open Durations costʰⁱ
open WithDecEq _≟ₒ_ using (True-irr)

------------------------------------------------------------------------
-- The frame

_⊑ᵗ[_]_ : ℕ → Permits → ℕ → Set
w ⊑ᵗ[ (permitting Q) ] w' =
  True (any? (λ q → w' ≤? (w + duration q)) (traces Q))
w ⊑ᵗ[ any-run ]      w' = ⊤

-- reflexivity at the unit grade `{ ε }`: the only permitted run takes
-- no time, and none has passed

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ (permitting u) ] w
⊑ᵗ-refl {w} = fromWitness (here (≤-reflexive (sym (+-identityʳ w))))

-- transitivity multiplies the grades: the two advances compose into the
-- one the sequenced run allows, whose duration is the sum

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P ·ᵖ Q ] w''
⊑ᵗ-trans {permitting _} {any-run}    p q = tt
⊑ᵗ-trans {any-run}    {_}      p q = tt
⊑ᵗ-trans {permitting P} {permitting Q} {w} {w'} {w''} p q
  with find (toWitness p) | find (toWitness q)
... | t₁ , t₁∈P , w'≤w+t₁ | t₂ , t₂∈Q , w''≤w'+t₂ =
      fromWitness
        (Any.map (λ r → subst (λ z → w'' ≤ w + duration z) r bound)
                 (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q))
  where
    bound : w'' ≤ w + duration (t₁ ∙ t₂)
    bound =
      ≤-trans (≤-trans w''≤w'+t₂ (+-mono-≤ w'≤w+t₁ ≤-refl))
              (≤-reflexive
                (trans (+-assoc w (duration t₁) (duration t₂))
                       (cong (w +_) (sym (duration-∙ t₁ t₂)))))

-- covariance: the run that witnessed the advance is itself listed by
-- the weaker grade

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {_}      {any-run}    rel p = tt
⊑ᵗ-mono {any-run}    {permitting _} ()
⊑ᵗ-mono {permitting P} {permitting Q} {w} {w'} rel p
  with find (toWitness p)
... | t , t∈P , w'≤w+t =
      fromWitness
        (Any.map (λ r → subst (λ z → w' ≤ w + duration z) r w'≤w+t)
                 (∈-⊑ rel t∈P))

⊑ᵗ-irrelevant : ∀ {Q w w'} → (p q : w ⊑ᵗ[ Q ] w') → p ≡ q
⊑ᵗ-irrelevant {permitting Q} {w} {w'} p q =
  True-irr (any? (λ t → w' ≤? (w + duration t)) (traces Q)) p q
⊑ᵗ-irrelevant {any-run}    tt tt = refl

ticks : World right-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {Q} → ⊑ᵗ-irrelevant {Q}
  }
