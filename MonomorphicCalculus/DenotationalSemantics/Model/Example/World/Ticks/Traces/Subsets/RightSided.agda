------------------------------------------------------------------------
-- A time-ticks Kripke frame for the subset grade of upper bounds.    --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only elapsed      --
-- time, and a grade is read through the durations of the runs it     --
-- lists: moving between worlds goes forward and takes no longer than --
-- one of them.                                                       --
--                                                                    --
--   w ⊑[ Q ] w'   iff   w ≤ w'   and                                 --
--                       w' ≤ w + duration q   for some q ∈ Q         --
--                                                                    --
-- The quantifier is existential, following the order of the grade,   --
-- which is inclusion in the permitting direction: a weaker grade     --
-- lists more runs, and a condition preserved by weakening is met     --
-- by one listed run rather than by all.                              --
--                                                                    --
-- The grade bounds which runs may occur; the tick world records only --
-- the duration of the slowest, so `⌈ write ⌉` and `⟨ 3 ⟩`, distinct  --
-- and incomparable grades, reach the same time points.               --
--                                                                    --
-- Covariance holds because a listed run of the smaller grade is a    --
-- listed run of the larger one, the comparison of traces being       --
-- equality.                                                          --
--                                                                    --
-- The grade `any-run` lists no run and reaches every world ahead.    --
--                                                                    --
-- The relation is the bound restricted to forward moves. The unit    --
-- `{ ε }` is not least, but its run takes no time, and without       --
-- `w ≤ w'` the unit grade would reach the past.                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → ℕ) where

open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant; +-assoc; +-mono-≤;
         +-identityʳ)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Grades.Traces.Durations ℕᵀ Op

open import Grades.Examples.Traces.Subsets.Base
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans using (∈-⊑)
open import Grades.Examples.Traces.Subsets.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (right-sided; Permits; permitting_; any-run; _·ᵖ_; _≾_)

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Action using (forward)

open Durations costʰⁱ

------------------------------------------------------------------------
-- The frame

-- The bound: advance no further than one of the listed runs takes; at
-- `any-run` there is no run to stay within.

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
                 (nf-∈⁺ (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q)))
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

-- the bound as a frame

private
  bounded : World right-sided
  bounded = record
    { W             = ℕ
    ; _⊑[_]_       = _⊑ᵗ[_]_
    ; ⊑-refl       = ⊑ᵗ-refl
    ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
    ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
    ; ⊑-irrelevant = λ {Q} → ⊑ᵗ-irrelevant {Q}
    }

-- The frame: the bound, forward moves only.

ticks : World right-sided
ticks = forward bounded _≤_ ≤-refl ≤-trans ≤-irrelevant

-- the relation it states

⊑-def : ∀ {w Q w'}
      → World._⊑[_]_ ticks w Q w' ≡ ((w ≤ w') × (w ⊑ᵗ[ Q ] w'))
⊑-def = refl
