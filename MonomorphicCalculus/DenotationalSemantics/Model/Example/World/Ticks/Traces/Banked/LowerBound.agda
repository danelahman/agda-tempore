------------------------------------------------------------------------
-- A time-ticks Kripke frame for the trace grade of guarantees.       --
--                                                                    --
-- Worlds are time points of the time domain. A tick world records    --
-- only elapsed time, and a grade is read through the durations of    --
-- the guarantees it lists: moving between worlds takes at least one  --
-- of them.                                                           --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w + duration p ≤ w'   for some p ∈ P        --
--                                                                    --
-- The quantifier is existential, as in the order of the grade:       --
-- `P ≾ P'` requires each guarantee of `P` to be weakened by one of   --
-- `P'`, so the witnessing guarantee is transported, and it takes no  --
-- longer at the far end, `duration` being monotone for the coverage  --
-- order.                                                             --
--                                                                    --
-- This is a lower-bound frame with the bound read off a              --
-- trace of the grade; the tick world records how long the operations --
-- of that trace take, not which operations it demands.               --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Relation.Nullary using (¬_)

open import Grades.Durations using (Duration; TimeDomain)

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Traces.Banked.LowerBound
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M using (Carrier)
open M.Notation
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Grades.Traces.Durations T Op
open import Grades.Traces.Coverage T Op costˡᵒ using (duration-≼ᶜ)

open import Grades.Examples.Traces.Banked.LowerBound
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (lower-bound; _≾_; Antichain; traces; 𝟏; _·_; _∙_; _·ˢ_;
         n-◃⁻; ◃-∈; True-irr)

open import MonomorphicCalculus.DenotationalSemantics.Model.World

open Durations costˡᵒ

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: advance at least as far as one of the
-- listed guarantees takes.

_⊑ᵗ[_]_ : Carrier → Antichain → Carrier → Set
w ⊑ᵗ[ P ] w' = True (any? (λ p → (w + duration p) ≤? w') (traces P))

-- reflexivity at the unit grade `{ ε }`: the empty guarantee demands no
-- time to pass, and none has

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ 𝟏 ] w
⊑ᵗ-refl {w} = fromWitness (here (≤-reflexive (+-identityʳ w)))

-- transitivity multiplies the grades: the two advances compose into the
-- one the sequenced guarantee demands, whose duration is the sum

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} {w'} {w''} p q
  with find (toWitness p) | find (toWitness q)
... | t₁ , t₁∈P , w+t₁≤w' | t₂ , t₂∈Q , w'+t₂≤w''
        with find (n-◃⁻ (traces P ·ˢ traces Q)
                        (◃-∈ (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q)))
...     | t , t∈PQ , t≼t₁∙t₂ =
          fromWitness
            (Any.map (λ r → subst (λ z → (w + duration z) ≤ w'') r bound) t∈PQ)
  where
    sequenced : (w + duration (t₁ ∙ t₂)) ≤ w''
    sequenced =
      ≤-trans (≤-reflexive
                (trans (cong (w +_) (duration-∙ t₁ t₂))
                       (sym (+-assoc w (duration t₁) (duration t₂)))))
              (≤-trans (+-mono-≤ w+t₁≤w' ≤-refl) w'+t₂≤w'')

    bound : (w + duration t) ≤ w''
    bound = ≤-trans (+-mono-≤ ≤-refl (duration-≼ᶜ t≼t₁∙t₂)) sequenced

-- covariance: the guarantee that witnessed the advance is weakened by
-- one of the weaker grade's, which therefore takes no longer

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {P} {Q} {w} {w'} rel p
  with find (toWitness p)
... | t , t∈P , w+t≤w'
        with find (toWitness (rel t (fromWitness t∈P)))
...     | t' , t'∈Q , t'≼t =
          fromWitness
            (Any.map (λ r → subst (λ z → (w + duration z) ≤ w') r bound) t'∈Q)
  where
    bound : (w + duration t') ≤ w'
    bound = ≤-trans (+-mono-≤ ≤-refl (duration-≼ᶜ t'≼t)) w+t≤w'

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} {w'} p q =
  True-irr (any? (λ t → (w + duration t) ≤? w') (traces P)) p q

ticks : World lower-bound
ticks = record
  { W             = Carrier
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
