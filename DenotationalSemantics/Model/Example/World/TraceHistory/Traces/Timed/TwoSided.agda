------------------------------------------------------------------------
-- A trace-history Kripke frame for the two-sided trace intervals.     --
--                                                                    --
-- Worlds are timed traces, and a grade `[ P , Q ]` reaches the        --
-- histories obtained by appending one continuation that answers to    --
-- both endpoints:                                                    --
--                                                                    --
--   w ⊑ᵇ[ [ P , Q ] ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'             --
--                                and  p ≼ᶜ cont  for some p ∈ P      --
--                                and  cont ≼ᵃ q  for some q ∈ Q      --
--                                                                    --
-- Unlike the tick frame, which is literally the pair of its two       --
-- halves, this one shares the continuation between them: what the     --
-- floor demands and what the cap permits are demanded of the same     --
-- run. That is the frame's whole point -- a history remembers which   --
-- operations occurred, so the two endpoints can talk about them       --
-- rather than only about how long they took.                         --
--                                                                    --
-- The two comparisons run in opposite directions, and at different    --
-- orders: the guarantee is covered by the continuation, the           --
-- continuation stays within the allowance.                           --
--                                                                    --
-- The cap alone carries `unbounded`, which lists no allowance         --
-- and so caps the continuation not at all.                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ costʰⁱ : Op → ℕ)
  (cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans

open import Syntax.Grades.Traces.Coverage Op costˡᵒ
  using (_≼ᶜ_; ≼ᶜ-refl; ≼ᶜ-trans) renaming (mono-∙ to mono-∙ᶜ)
open import Syntax.Grades.Traces.Coverage.Decidable Op costˡᵒ
  using (module DecCoverage)

open import Syntax.Grades.Traces.Allowance Op costʰⁱ
  using (_≼ᵃ_; ≼ᵃ-refl; ≼ᵃ-trans) renaming (mono-∙ to mono-∙ᵃ)
open import Syntax.Grades.Traces.Allowance.Decidable Op costʰⁱ
  using (module DecAllowance)

open import Syntax.Grades.Example.Traces.Timed.TwoSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos
  using (TwoSided; lo; hi; uᵗˢ; _·ᵗˢ_; two-sided; _≾ᵗˢ_)

-- the cap endpoint is the right-sided grade's carrier, `unbounded` and
-- all

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (Bounds; within_; unbounded; _·ᵇ_) renaming (_≾_ to _≾ʰⁱ_)

open DecCoverage _≟ₒ_ using (_≼ᶜ?_)
open DecAllowance _≟ₒ_ using (_≼ᵃ?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation that covers one of
-- the listed guarantees and stays within one of the listed allowances.

-- the cap's condition on the continuation, vacuous at `unbounded`

Within : Trace → Bounds → Set
Within cont (within Q) = True (any? (λ q → cont ≼ᵃ? q) (traces Q))
Within cont unbounded       = ⊤

-- sequencing two continuations stays within the sequenced allowance

Within-∙ : (t₁ t₂ : Trace) (Q₁ Q₂ : Bounds)
         → Within t₁ Q₁ → Within t₂ Q₂ → Within (t₁ ∙ t₂) (Q₁ ·ᵇ Q₂)
Within-∙ _  _  (within _)  unbounded        _  _  = tt
Within-∙ _  _  unbounded        _         _  _  = tt
Within-∙ t₁ t₂ (within Q₁) (within Q₂) n₁ n₂
  with find (toWitness n₁) | find (toWitness n₂)
... | x , x∈Q , t₁≼x | y , y∈Q' , t₂≼y =
      fromWitness
        (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼ᵃ_) eq (mono-∙ᵃ t₁≼x t₂≼y))
                 (nf-∈⁺ (∈-cartesianProductWith⁺ _∙_ x∈Q y∈Q')))

-- the allowance the continuation stayed within is replaced by one of
-- the weaker grade's

Within-≾ : (cont : Trace) (Q₁ Q₂ : Bounds)
         → Q₁ ≾ʰⁱ Q₂ → Within cont Q₁ → Within cont Q₂
Within-≾ _    _         unbounded        _ _ = tt
Within-≾ _    unbounded        (within _)  ()
Within-≾ cont (within Q₁) (within Q₂) h n
  with find (toWitness n)
... | t , t∈Q , cont≼t
        with find (toWitness (h t (fromWitness t∈Q)))
...     | t' , t'∈Q' , t≼t' =
          fromWitness
            (Any.map (λ e → subst (cont ≼ᵃ_) e (≼ᵃ-trans cont≼t t≼t')) t'∈Q')

Within-irr : (cont : Trace) (Q : Bounds) → (p q : Within cont Q) → p ≡ q
Within-irr cont (within Q) = True-irr (any? (λ q → cont ≼ᵃ? q) (traces Q))
Within-irr _    unbounded       tt tt = refl

infix 5 _⊑ᵇ[_]_

record _⊑ᵇ[_]_ (w : Trace) (i : TwoSided) (w' : Trace) : Set where
  constructor mkᵇ
  field
    cont    : Trace                                     -- continuation
    covers  : True (any? (λ p → p ≼ᶜ? cont) (traces (lo i)))
                                                        -- covers a guarantee
    bounded : Within cont (hi i)                        -- within an allowance
    extends : w ∙ cont ≡ w'                             -- `w'` extends `w`

open _⊑ᵇ[_]_

-- reflexivity at the unit grade: the empty continuation covers the
-- empty guarantee and stays within the empty allowance

⊑ᵇ-refl : ∀ {w} → w ⊑ᵇ[ uᵗˢ ] w
⊑ᵇ-refl {w} =
  mkᵇ ε
      (fromWitness {a? = any? (λ p → p ≼ᶜ? ε) (traces u)} (here (≼ᶜ-refl ε)))
      (fromWitness {a? = any? (λ q → ε ≼ᵃ? q) (traces u)} (here (≼ᵃ-refl ε)))
      (∙-identityʳ w)

-- transitivity multiplies the grades, sequencing the one continuation
-- against both endpoints at once

⊑ᵇ-trans : ∀ {i₁ i₂ w w' w''}
         → w ⊑ᵇ[ i₁ ] w' → w' ⊑ᵇ[ i₂ ] w'' → w ⊑ᵇ[ i₁ ·ᵗˢ i₂ ] w''
⊑ᵇ-trans {i₁} {i₂} {w} (mkᵇ t₁ c₁ n₁ eq₁) (mkᵇ t₂ c₂ n₂ eq₂)
  with find (toWitness c₁) | find (toWitness c₂)
... | a , a∈P , a≼t₁ | b , b∈P' , b≼t₂ =
      mkᵇ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst (_≼ᶜ (t₁ ∙ t₂)) eq (mono-∙ᶜ a≼t₁ b≼t₂))
                     (nf-∈⁺ (∈-cartesianProductWith⁺ _∙_ a∈P b∈P'))))
          (Within-∙ t₁ t₂ (hi i₁) (hi i₂) n₁ n₂)
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

-- covariance: each witness is replaced along its own endpoint's order,
-- the continuation staying put

⊑ᵇ-mono : ∀ {i₁ i₂ w w'} → i₁ ≾ᵗˢ i₂ → w ⊑ᵇ[ i₁ ] w' → w ⊑ᵇ[ i₂ ] w'
⊑ᵇ-mono {i₁} {i₂} (l , h) (mkᵇ cont c n eq) =
  mkᵇ cont (fromWitness covers') (Within-≾ cont (hi i₁) (hi i₂) h n) eq
  where
    covers' : Any (λ p → p ≼ᶜ cont) (traces (lo i₂))
    covers' with find (toWitness c)
    ... | t , t∈P , t≼cont
            with find (toWitness (l t (fromWitness t∈P)))
    ...     | t' , t'∈P' , t'≼t =
              Any.map (λ e → subst (_≼ᶜ cont) e (≼ᶜ-trans t'≼t t≼cont)) t'∈P'

-- proof irrelevance: the continuation is determined by left
-- cancellation, and both witnesses are irrelevant proofs

⊑ᵇ-irrelevant : ∀ {i w w'} → (p q : w ⊑ᵇ[ i ] w') → p ≡ q
⊑ᵇ-irrelevant {i} {w} (mkᵇ cont c n refl) (mkᵇ cont' c' n' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong₂ (λ x y → mkᵇ cont x y refl)
              (True-irr (any? (λ p → p ≼ᶜ? cont) (traces (lo i))) c c')
              (Within-irr cont (hi i) n n')

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
