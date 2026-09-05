------------------------------------------------------------------------
-- A time-ticks Kripke frame for the (right-sided) sets of traces as    --
-- the resource grades.                                                 --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only the elapsed   --
-- time, not which continuation trace produced it, so a set-of-traces   --
-- grade `P` reaches exactly those worlds lying an *exact* trace         --
-- duration ahead:                                                      --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w' = w + duration t   for some trace t of P   --
--                                                                    --
-- Because the reachable worlds are a finite set of durations and       --
-- equality of ticks is decidable, the accessibility is phrased in the  --
-- proof-irrelevant `True`-of-a-decision form.                          --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.Ticks.SetOfTraces
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.Nat using (_+_; _≟_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op

open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
  using (right-sided-traces; _≾_)

open import DenotationalSemantics.Model.World

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)

-- Accessibility on time ticks: reach exactly the worlds an exact trace
-- duration of `P` ahead.

_⊑ᵗ[_]_ : ℕ → NeTraces → ℕ → Set
w ⊑ᵗ[ P ] w' = True (any? (λ t → w' ≟ (w + duration t)) (traces P))

-- reflexivity at the unit grade `{ ε }`: the empty trace has duration
-- zero, so the world does not advance

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} = fromWitness (here (sym (+-identityʳ w)))

-- transitivity multiplies the grades: the two traces sequence into a
-- trace of the product whose duration is the sum of the durations

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} {w'} {w''} p q
  with find (toWitness p) | find (toWitness q)
... | t₁ , t₁∈P , eq₁ | t₂ , t₂∈Q , eq₂ =
      fromWitness
        (Any.map (λ r → subst (λ z → w'' ≡ w + duration z) r eq)
                 (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q))
  where
    eq : w'' ≡ w + duration (t₁ ∙ t₂)
    eq = begin
           w''
         ≡⟨ eq₂ ⟩
           w' + duration t₂
         ≡⟨ cong (_+ duration t₂) eq₁ ⟩
           (w + duration t₁) + duration t₂
         ≡⟨ +-assoc w (duration t₁) (duration t₂) ⟩
           w + (duration t₁ + duration t₂)
         ≡⟨ cong (w +_) (sym (duration-∙ t₁ t₂)) ⟩
           w + duration (t₁ ∙ t₂)
         ∎

-- covariance: a larger set of traces gives a larger accessibility, as
-- the witnessing trace still lives in the larger set with the same
-- duration

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {P} {Q} {w} {w'} rel p
  with find (toWitness p)
... | t , t∈P , eq =
      fromWitness
        (Any.map (λ r → subst (λ z → w' ≡ w + duration z) r eq)
                 (toWitness (rel t (fromWitness t∈P))))

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} {w'} p q =
  True-irr (any? (λ t → w' ≟ (w + duration t)) (traces P)) p q

-- The frame.

ticks : World right-sided-traces
ticks = record
  { W             = ℕ
  ; _⊑[_]_       = _⊑ᵗ[_]_
  ; ⊑-refl       = ⊑ᵗ-refl
  ; ⊑-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
