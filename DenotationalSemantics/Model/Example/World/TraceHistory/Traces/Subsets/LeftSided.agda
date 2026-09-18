------------------------------------------------------------------------
-- A trace-history Kripke frame for the subset grade of lower bounds.  --
--                                                                    --
-- Worlds are timed traces. A grade `P` lists runs that must remain    --
-- reachable, and a history reaches another by appending a             --
-- continuation that answers to every one of them:                     --
--                                                                    --
--   w ⊑ᵇ[ P ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'  and  P ⊆ { cont }   --
--                                                                    --
-- The condition is universal in `P`, as covariance demands: weakening --
-- here drops listed runs.                                             --
--                                                                    --
-- READING, and what it exposes. `P ⊆ { cont }` says every demanded    --
-- run *is* the continuation, so for a non-singleton grade no world is --
-- reachable at all: one history is one run, and it cannot be two. The --
-- tick frame does not see this -- there a grade is only a number of   --
-- ticks, and several demanded runs collapse into their slowest.       --
--                                                                    --
-- That is the frame stating what the grade already says: a            --
-- non-singleton lower bound is a claim about a computation's          --
-- branching, and a single observed history is no witness for it.      --
--                                                                    --
-- The grade's `no-demand` demands no run, so it leaves the            --
-- continuation unconstrained and asks only that `w'` extend `w`.      --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subsets.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Base using (List; [_])
open import Data.Unit using (⊤; tt)

open import Syntax.Grades.Traces.Sets Op

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (left-sided; Demands; demanding_; no-demand; _·ᵈ_; _≾_)

open WithDecEq _≟ₒ_
  using (_⊑_; _≟ᵀ_; ⊑-refl; ⊑-trans; ⊑-·ˢ; liftˢ-irrelevant)

-- the subset order is the lift at equality, so its irrelevance is the
-- lift's -- with the lifted relation pinned, which nothing else fixes

⊑-irr : {xs ys : List Trace} → (p q : xs ⊑ ys) → p ≡ q
⊑-irr = liftˢ-irrelevant {R = _≡_} {R? = _≟ᵀ_}

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories

-- the condition on the continuation, vacuous at `no-demand`

Demanded : Trace → Demands → Set
Demanded cont (demanding P) = traces P ⊑ [ cont ]
Demanded cont no-demand       = ⊤

Demanded-irr : (cont : Trace) (P : Demands) → (p q : Demanded cont P) → p ≡ q
Demanded-irr _ (demanding _) = ⊑-irr
Demanded-irr _ no-demand       tt tt = refl

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (P : Demands) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont     : Trace                     -- continuation
    demanded : Demanded cont P           -- every demanded run is it
    extends  : w ∙ cont ≡ w'             -- `w'` extends `w`

open _⊑ᵇ[_]_

-- appending the two continuations in turn extends across both

extends-∙ : (w t₁ t₂ : Trace) {w' w'' : Trace}
          → w ∙ t₁ ≡ w' → w' ∙ t₂ ≡ w'' → w ∙ (t₁ ∙ t₂) ≡ w''
extends-∙ w t₁ t₂ eq₁ eq₂ =
  trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂)

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ (demanding u) ] w
⊑ᵇ-refl {w} = mkᵇ ε (⊑-refl {traces u}) (∙-identityʳ w)

-- transitivity multiplies the grades: the product's demands are the
-- pairwise products, and the singleton product is the singleton of the
-- sequenced continuation

⊑ᵇ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵇ[ P ] w' → w' ⊑ᵇ[ Q ] w'' → w ⊑ᵇ[ P ·ᵈ Q ] w''
⊑ᵇ-trans {demanding _} {no-demand}    {w} (mkᵇ t₁ _ eq₁) (mkᵇ t₂ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {no-demand}    {_}      {w} (mkᵇ t₁ _ eq₁) (mkᵇ t₂ _ eq₂) =
  mkᵇ (t₁ ∙ t₂) tt (extends-∙ w t₁ t₂ eq₁ eq₂)
⊑ᵇ-trans {demanding P} {demanding Q} {w} (mkᵇ t₁ d₁ eq₁) (mkᵇ t₂ d₂ eq₂) =
  mkᵇ (t₁ ∙ t₂) (⊑-·ˢ d₁ d₂) (extends-∙ w t₁ t₂ eq₁ eq₂)

-- covariance: the weaker grade demands a sub-list of what the stronger
-- one did, and the continuation already answered to all of that

⊑ᵇ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵇ[ P ] w' → w ⊑ᵇ[ Q ] w'
⊑ᵇ-mono {_}      {no-demand}    rel (mkᵇ cont _ eq) = mkᵇ cont tt eq
⊑ᵇ-mono {no-demand}    {demanding _} ()
⊑ᵇ-mono {demanding P} {demanding Q} rel (mkᵇ cont d eq) =
  mkᵇ cont (⊑-trans {traces Q} {traces P} rel d) eq

⊑ᵇ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵇ[ P ] w') → p ≡ q
⊑ᵇ-irrelevant {P} {w} (mkᵇ cont d refl) (mkᵇ cont' d' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl = cong (λ z → mkᵇ cont z refl) (Demanded-irr cont P d d')

------------------------------------------------------------------------
-- The frame.

histories : World left-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᵇ[_]_
  ; ⊑-refl        = ⊑ᵇ-refl
  ; ⊑-trans       = λ {P} {Q} → ⊑ᵇ-trans {P} {Q}
  ; ⊑-mono        = λ {P} {Q} → ⊑ᵇ-mono {P} {Q}
  ; ⊑-irrelevant  = λ {P} → ⊑ᵇ-irrelevant {P}
  }
