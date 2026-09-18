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
--                                                                    --
-- The top `⊤ᵍ` is adjoined to the pair as a whole, and constrains the --
-- continuation at neither endpoint.                                  --
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
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op

open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ using (∈-⊑)
open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; lo; hi; two-sided; Interval; only_; ⊤ᵍ; uᴵ; _·ᴵ_; _≾ᴵ_)

open WithDecEq _≟ₒ_
  using (_⊑_; _≟ᵀ_; _∈?_; ⊑-refl; ⊑-trans; ⊑-·ˢ; True-irr; liftˢ-irrelevant)

⊑-irr : {xs ys : List Trace} → (p q : xs ⊑ ys) → p ≡ q
⊑-irr = liftˢ-irrelevant {R = _≡_} {R? = _≟ᵀ_}

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories

-- the two conditions on the continuation, both vacuous at `⊤ᵍ`

Demanded : Trace → Interval → Set
Demanded cont (only i) = traces (lo i) ⊑ [ cont ]
Demanded cont ⊤ᵍ       = ⊤

Listed : Trace → Interval → Set
Listed cont (only i) = True (cont ∈? traces (hi i))
Listed cont ⊤ᵍ       = ⊤

Demanded-irr : (cont : Trace) (i : Interval) → (p q : Demanded cont i) → p ≡ q
Demanded-irr _ (only _) = ⊑-irr
Demanded-irr _ ⊤ᵍ       tt tt = refl

Listed-irr : (cont : Trace) (i : Interval) → (p q : Listed cont i) → p ≡ q
Listed-irr cont (only i) = True-irr (cont ∈? traces (hi i))
Listed-irr _    ⊤ᵍ       tt tt = refl

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (i : Interval) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont     : Trace                             -- continuation
    demanded : Demanded cont i                   -- every demanded run is it
    listed   : Listed cont i                     -- and it is permitted
    extends  : w ∙ cont ≡ w'                     -- `w'` extends `w`

open _⊑ᵇ[_]_

-- appending the two continuations in turn extends across both

extends-∙ : (w t₁ t₂ : Trace) {w' w'' : Trace}
          → w ∙ t₁ ≡ w' → w' ∙ t₂ ≡ w'' → w ∙ (t₁ ∙ t₂) ≡ w''
extends-∙ w t₁ t₂ eq₁ eq₂ =
  trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂)

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ uᴵ ] w
⊑ᵇ-refl {w} =
  mkᵇ ε (⊑-refl {traces u}) (fromWitness {a? = ε ∈? traces u} (here refl))
      (∙-identityʳ w)

⊑ᵇ-trans : ∀ {i₁ i₂ w w' w''}
         → w ⊑ᵇ[ i₁ ] w' → w' ⊑ᵇ[ i₂ ] w'' → w ⊑ᵇ[ i₁ ·ᴵ i₂ ] w''
⊑ᵇ-trans {only _} {⊤ᵍ}    {w} (mkᵇ t₁ _ _ eq₁) (mkᵇ t₂ _ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {⊤ᵍ}    {_}      {w} (mkᵇ t₁ _ _ eq₁) (mkᵇ t₂ _ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {only i₁} {only i₂} {w} (mkᵇ t₁ d₁ l₁ eq₁) (mkᵇ t₂ d₂ l₂ eq₂) =
  mkᵇ (t₁ ∙ t₂)
      (⊑-·ˢ d₁ d₂)
      (fromWitness
        (∈-cartesianProductWith⁺ _∙_ (toWitness l₁) (toWitness l₂)))
      (extends-∙ w t₁ t₂ eq₁ eq₂)

⊑ᵇ-mono : ∀ {i₁ i₂ w w'} → i₁ ≾ᴵ i₂ → w ⊑ᵇ[ i₁ ] w' → w ⊑ᵇ[ i₂ ] w'
⊑ᵇ-mono {_}       {⊤ᵍ}     rel (mkᵇ cont _ _ eq) = mkᵇ cont tt tt eq
⊑ᵇ-mono {⊤ᵍ}     {only _}  ()
⊑ᵇ-mono {only i₁} {only i₂} (l , h) (mkᵇ cont d n eq) =
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
              (Demanded-irr cont i d d')
              (Listed-irr cont i n n')

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
