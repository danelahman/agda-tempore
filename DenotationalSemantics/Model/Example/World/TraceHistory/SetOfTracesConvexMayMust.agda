------------------------------------------------------------------------
-- A may/must trace-history Kripke frame for convexly ordered sets of  --
-- traces as the resource grades.                                      --
--                                                                    --
-- Worlds are timed traces, recording the history observed so far. A   --
-- resource grade `P` is read as a set of demands, and reaching `w'`   --
-- from `w` by a continuation `cont` asks for both:                     --
--                                                                    --
--   * may:  `t ≼ cont` for *some* `t ∈ P` -- the continuation does    --
--           at least what some demand asks for;                       --
--   * must: `duration t ≤ duration cont` for *every* `t ∈ P` -- it    --
--           takes at least every demand's time.                        --
--                                                                    --
-- The Σ-shaped half is covariant along the Smyth lift of the sub-     --
-- trace preorder, and the Π-shaped one along the Hoare lift (its      --
-- body is `≼`-downward closed in the demand), so `⊑-mono` consumes    --
-- both halves of the convex order. Neither half implies the other:    --
-- the may half constrains the shape of the continuation, the must     --
-- half its cost.                                                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.SetOfTracesConvexMayMust
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.Nat.Base using (_+_; _≤_)
open import Data.Nat.Properties
  using (_≤?_; ≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; n≤0⇒n≡0; m+n≡0⇒m≡0)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op c
open import Syntax.Grades.Traces.SubtraceDuration Op c using (duration-≼)

open import Syntax.Grades.Example.TraceSet.Convex Op _≟ₒ_ c
  using (traces-convex; _≾_; module Separation)

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `cont` that covers
-- some member of `P` and takes at least every member's time.

infix 5 _⊑ᶜ[_]_

record _⊑ᶜ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkᶜ
  field
    cont    : Trace                                          -- continuation
    covered : True (any? (λ t → t ≼? cont) (traces P))       -- covers a member
    budget  : True (all? (λ t → duration t ≤? duration cont) -- takes at least
                         (traces P))                          -- every member's time
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ᶜ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation, which
-- already covers the sole member `ε` and is asked for no time

⊑ᶜ-refl : ∀ {w} → w ⊑ᶜ[ u ] w
⊑ᶜ-refl {w} =
  mkᶜ ε
      (fromWitness {a? = any? (λ t → t ≼? ε) (traces u)} εcov)
      (fromWitness {a? = all? (λ t → duration t ≤? duration ε) (traces u)}
                   (All.tabulate εbud))
      (∙-identityʳ w)
  where
    εcov : Any (λ t → t ≼ ε) (traces u)
    εcov = here (≼-refl ε)

    εbud : ∀ {x} → x ∈ traces u → duration x ≤ duration ε
    εbud x∈ = subst (λ z → duration z ≤ duration ε) (sym (∈-[ε]⁻ x∈)) ≤-refl

-- transitivity multiplies the grades, sequencing the two continuations:
-- the covered members multiply, and so do the two budgets, because the
-- duration is a monoid homomorphism for sequencing

⊑ᶜ-trans : ∀ {P Q w w' w''}
         → w ⊑ᶜ[ P ] w' → w' ⊑ᶜ[ Q ] w'' → w ⊑ᶜ[ P · Q ] w''
⊑ᶜ-trans {P} {Q} {w} (mkᶜ t₁ cov₁ bud₁ eq₁) (mkᶜ t₂ cov₂ bud₂ eq₂)
  with find (toWitness cov₁) | find (toWitness cov₂)
... | a , a∈P , a≼t₁ | b , b∈Q , b≼t₂ =
      mkᶜ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst (_≼ (t₁ ∙ t₂)) eq (mono-∙ a≼t₁ b≼t₂))
                     (∈-cartesianProductWith⁺ _∙_ a∈P b∈Q)))
          (fromWitness (All.tabulate bud))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    bud : ∀ {r} → r ∈ (traces P ·ˢ traces Q)
        → duration r ≤ duration (t₁ ∙ t₂)
    bud r∈ with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) r∈
    ... | x , y , x∈P , y∈Q , refl =
          ≤-trans (≤-reflexive (duration-∙ x y))
                  (≤-trans (+-mono-≤ (All.lookup (toWitness bud₁) x∈P)
                                     (All.lookup (toWitness bud₂) y∈Q))
                           (≤-reflexive (sym (duration-∙ t₁ t₂))))

-- covariance: the may half is transported along the Smyth half of the
-- grade order, the must half along the Hoare half -- a member of the
-- weaker set sits inside a member of the stronger one, whose budget it
-- therefore inherits

⊑ᶜ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᶜ[ P ] w' → w ⊑ᶜ[ Q ] w'
⊑ᶜ-mono {P} {Q} (hoare , smyth) (mkᶜ cont cov bud eq) =
  mkᶜ cont (fromWitness may) (fromWitness (All.tabulate must)) eq
  where
    may : Any (λ t → t ≼ cont) (traces Q)
    may with find (toWitness cov)
    ... | t , t∈P , t≼cont
            with find (toWitness (smyth t (fromWitness t∈P)))
    ...     | t' , t'∈Q , t'≼t =
              Any.map (λ e → subst (_≼ cont) e (≼-trans t'≼t t≼cont)) t'∈Q

    must : ∀ {t} → t ∈ traces Q → duration t ≤ duration cont
    must {t} t∈Q with find (toWitness (hoare t (fromWitness t∈Q)))
    ... | s , s∈P , t≼s =
          ≤-trans (duration-≼ t≼s) (All.lookup (toWitness bud) s∈P)

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and both witnesses are irrelevant proofs

⊑ᶜ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᶜ[ P ] w') → p ≡ q
⊑ᶜ-irrelevant {P} {w} (mkᶜ cont cov bud refl) (mkᶜ cont' cov' bud' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong₂ (λ z z' → mkᶜ cont z z' refl)
              (True-irr (any? (λ t → t ≼? cont) (traces P)) cov cov')
              (True-irr (all? (λ t → duration t ≤? duration cont) (traces P))
                        bud bud')

------------------------------------------------------------------------
-- The frame.

histories : World traces-convex
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ᶜ[_]_
  ; ⊑-refl        = ⊑ᶜ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ᶜ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} → ⊑ᶜ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant  = λ {ρ} → ⊑ᶜ-irrelevant {ρ}
  }

------------------------------------------------------------------------
-- The Hoare half is load-bearing
--
-- For an operation of non-zero cost, the unit `{ ε }` and
-- `Separation`'s set `Q = { ε , o }` are related by the Smyth lift
-- (`Separation.Q≽u`, which is the Smyth half of `u ≾ Q`) yet `⊑ᶜ` does
-- not transport from `u` to `Q`: the operation `Q` demands is not
-- afforded by a continuation that takes no time. So the Smyth half
-- alone does not give `⊑-mono` for this frame -- the Hoare half, which
-- fails here (`Separation.¬Q≼u`), is what the must condition needs.

module MustSeparation (o : Op) (co : ¬ (c o ≡ 0)) where

  open Separation o co using (⟨o⟩; Q; Q≽u; ¬Q≼u)

  step : ε ⊑ᶜ[ u ] ε
  step = ⊑ᶜ-refl

  ¬step : ¬ (ε ⊑ᶜ[ Q ] ε)
  ¬step (mkᶜ cont cov bud eq) = co (m+n≡0⇒m≡0 (c o) (n≤0⇒n≡0 dur≤0))
    where
      cont≡ : cont ≡ ε
      cont≡ = trans (sym (∙-identityˡ cont)) eq

      dur≤0 : duration ⟨o⟩ ≤ 0
      dur≤0 = subst (λ z → duration ⟨o⟩ ≤ duration z) cont≡
                    (All.lookup (toWitness bud) (there (here refl)))

  ⊑ᶜ-needs-hoare : ¬ ({w w' : Trace} → w ⊑ᶜ[ u ] w' → w ⊑ᶜ[ Q ] w')
  ⊑ᶜ-needs-hoare f = ¬step (f step)
