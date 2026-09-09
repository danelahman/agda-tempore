------------------------------------------------------------------------
-- A trace-history Kripke frame for the two-sided subset intervals.    --
--                                                                    --
-- Worlds are timed traces, and a grade `[ P , Q ]` reaches the        --
-- histories obtained by appending one continuation answering to both  --
-- endpoints:                                                         --
--                                                                    --
--   w ⊑ᵇ[ [ P , Q ] ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'             --
--                                and  P ⊆ { cont }                   --
--                                and  cont ∈ Q                       --
--                                                                    --
-- Unlike the tick frame, which is the plain pair of its halves, this  --
-- one shares the continuation: what the floor demands and what the    --
-- cap permits are asked of the same run.                              --
--                                                                    --
-- Which is why the cap's condition is, here, redundant. `P ⊆ {cont}`  --
-- with `P` non-empty puts `cont` in `P`, and the grade's coherence    --
-- field puts `P` inside `Q`. The field is kept because the frame is   --
-- the conjunction of its two halves and reads better as one, but the  --
-- observation is the same one the one-sided floor frame makes: at     --
-- this order a lower bound already pins the continuation exactly, so  --
-- a single history has nothing left to say about the upper one.       --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subsets.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Base using (List; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ using (∈-⊑)
open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; lo; hi; uᵇ; _·ᵇ_; two-sided; _≾ᵇ_)

open WithDecEq _≟ₒ_
  using (_⊑_; _≟ᵀ_; _∈?_; ⊑-refl; ⊑-trans; ⊑-·ˢ; True-irr; liftˢ-irrelevant)

⊑-irr : {xs ys : List Trace} → (p q : xs ⊑ ys) → p ≡ q
⊑-irr = liftˢ-irrelevant {R = _≡_} {R? = _≟ᵀ_}

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (i : TwoSided) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont     : Trace                             -- continuation
    demanded : traces (lo i) ⊑ [ cont ]          -- every demanded run is it
    listed   : True (cont ∈? traces (hi i))      -- and it is permitted
    extends  : w ∙ cont ≡ w'                     -- `w'` extends `w`

open _⊑ᵇ[_]_

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ uᵇ ] w
⊑ᵇ-refl {w} =
  mkᵇ ε (⊑-refl {traces u}) (fromWitness {a? = ε ∈? traces u} (here refl))
      (∙-identityʳ w)

⊑ᵇ-trans : ∀ {i₁ i₂ w w' w''}
         → w ⊑ᵇ[ i₁ ] w' → w' ⊑ᵇ[ i₂ ] w'' → w ⊑ᵇ[ i₁ ·ᵇ i₂ ] w''
⊑ᵇ-trans {i₁} {i₂} {w} (mkᵇ t₁ d₁ l₁ eq₁) (mkᵇ t₂ d₂ l₂ eq₂) =
  mkᵇ (t₁ ∙ t₂)
      (⊑-·ˢ d₁ d₂)
      (fromWitness
        (∈-cartesianProductWith⁺ _∙_ (toWitness l₁) (toWitness l₂)))
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

⊑ᵇ-mono : ∀ {i₁ i₂ w w'} → i₁ ≾ᵇ i₂ → w ⊑ᵇ[ i₁ ] w' → w ⊑ᵇ[ i₂ ] w'
⊑ᵇ-mono {i₁} {i₂} (l , h) (mkᵇ cont d n eq) =
  mkᵇ cont
      (⊑-trans {traces (lo i₂)} {traces (lo i₁)} l d)
      (fromWitness (∈-⊑ h (toWitness n)))
      eq

⊑ᵇ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵇ[ i ] w') → p ≡ q
⊑ᵇ-irrelevant {i} {w} (mkᵇ cont d n refl) (mkᵇ cont' d' n' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong₂ (λ x y → mkᵇ cont x y refl)
              (⊑-irr d d')
              (True-irr (cont ∈? traces (hi i)) n n')

------------------------------------------------------------------------
-- The frame.

histories : World two-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {i₁} {i₂} → ⊑ᵇ-trans {i₁} {i₂}
  ; ⊑-mono        = λ {i₁} {i₂} → ⊑ᵇ-mono {i₁} {i₂}
  ; ⊑-irrelevant  = λ {i} → ⊑ᵇ-irrelevant {i}
  }
