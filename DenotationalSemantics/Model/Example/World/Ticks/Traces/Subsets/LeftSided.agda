------------------------------------------------------------------------
-- A time-ticks Kripke frame for the subset grade of lower bounds.     --
--                                                                    --
-- Worlds are time points `ℕ`, and a grade lists runs that must remain --
-- reachable. Advancing has to leave room for every one of them:       --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w + duration p ≤ w'   for *all* p ∈ P        --
--                                                                    --
-- The quantifier is universal, and forced to be: a weaker grade lists --
-- *fewer* runs here, so only a condition asked of every listed run    --
-- survives weakening. That is the mirror of the cap's frame, where a  --
-- weaker grade lists more and the condition is existential -- the     --
-- quantifier follows the direction of inclusion, not the endpoint.    --
--                                                                    --
-- READING. A tick world sees only durations, so what it makes of the  --
-- grade is "at least as long as the *slowest* demanded run" -- where  --
-- the coverage floor of `Ticks.Traces.Timed.LeftSided`, whose set is  --
-- read disjunctively, yields the fastest instead.                     --
--                                                                    --
-- The grade's `no-demand` demands no run at all, so it relates        --
-- every pair of worlds.                                               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costˡᵒ : Op → ℕ) where

open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-mono-≤; +-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_; all?)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ using (∈-⊑)
open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (left-sided; Demands; demanding_; no-demand; _·ᵈ_; _≾_)

open import DenotationalSemantics.Model.World

open Durations costˡᵒ
open WithDecEq _≟ₒ_ using (True-irr)

------------------------------------------------------------------------
-- The frame

_⊑ᵗ[_]_ : ℕ → Demands → ℕ → Set
w ⊑ᵗ[ (demanding P) ] w' = True (all? (λ p → (w + duration p) ≤? w') (traces P))
w ⊑ᵗ[ no-demand ]     w' = ⊤

-- reflexivity at the unit grade `{ ε }`: the only demanded run takes no
-- time, and none has passed

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ (demanding u) ] w
⊑ᵗ-refl {w} = fromWitness (≤-reflexive (+-identityʳ w) ∷ [])

-- transitivity multiplies the grades: every demanded run of the product
-- splits into one from each factor, and the two advances compose

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P ·ᵈ Q ] w''
⊑ᵗ-trans {demanding _} {no-demand}     p q = tt
⊑ᵗ-trans {no-demand}     {_}      p q = tt
⊑ᵗ-trans {demanding P} {demanding Q} {w} {w'} {w''} p q =
  fromWitness (All.tabulate step)
  where
    step : {r : Trace} → r ∈ (traces P ·ˢ traces Q) → (w + duration r) ≤ w''
    step {r} r∈
      with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) r∈
    ... | a , b , a∈P , b∈Q , refl =
          ≤-trans
            (≤-reflexive
              (trans (cong (w +_) (duration-∙ a b))
                     (sym (+-assoc w (duration a) (duration b)))))
            (≤-trans (+-mono-≤ (All.lookup (toWitness p) a∈P) ≤-refl)
                     (All.lookup (toWitness q) b∈Q))

-- covariance: the weaker grade demands a sub-list, and the condition
-- already held of every member of the larger one

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {_}      {no-demand}     rel p = tt
⊑ᵗ-mono {no-demand}     {demanding _} ()
⊑ᵗ-mono {demanding P} {demanding Q} {w} {w'} rel p =
  fromWitness (All.tabulate (λ r∈Q → All.lookup (toWitness p) (∈-⊑ rel r∈Q)))

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {demanding P} {w} {w'} p q =
  True-irr (all? (λ t → (w + duration t) ≤? w') (traces P)) p q
⊑ᵗ-irrelevant {no-demand}     tt tt = refl

ticks : World left-sided
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
