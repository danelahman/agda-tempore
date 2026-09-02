------------------------------------------------------------------------
-- A may/must trace-history Kripke frame for convexly ordered sets of  --
-- traces as the resource grades.                                      --
--                                                                    --
-- Worlds are timed traces, recording the history observed so far. A   --
-- resource grade `P` is read as a set of admissible schedules, and    --
-- reaching `w'` from `w` by a continuation `cont` asks for both:      --
--                                                                    --
--   * may:  `cont ≼ t` for *some* `t ∈ P` -- the continuation does    --
--           only what some schedule permits;                          --
--   * must: `duration cont ≤ duration t` for *every* `t ∈ P` -- it    --
--           stays within every schedule's time budget.                --
--                                                                    --
-- The Σ-shaped half is covariant along the Hoare lift of the sub-     --
-- trace preorder, and the Π-shaped one along the Smyth lift (its      --
-- body is `≼`-upward closed), so `⊑-mono` consumes both halves of     --
-- the convex order. Neither half implies the other: the may half      --
-- constrains the shape of the continuation, the must half its cost.   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.SetOfTracesConvexWithMayMustHistories
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

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op
open import Syntax.Grades.Traces.SubtraceDuration Op c using (duration-≼)

open import Syntax.Grades.SetOfTracesConvex Op _≟ₒ_
  using (traces-convex; _≾_; module Separation)

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `cont` that some
-- member of `P` covers and every member of `P` affords.

infix 5 _⊑ᶜ[_]_

record _⊑ᶜ[_]_ (w : Trace) (P : NeTraces) (w' : Trace) : Set where
  constructor mkᶜ
  field
    cont    : Trace                                          -- continuation
    covered : True (any? (λ t → cont ≼? t) (traces P))       -- ≼ some member
    budget  : True (all? (λ t → duration cont ≤? duration t) -- affordable for
                         (traces P))                          -- every member
    extends : w ∙ cont ≡ w'                                  -- `w'` extends `w`

open _⊑ᶜ[_]_

-- reflexivity at the unit grade `{ ε }`: the empty continuation, which
-- is a sub-trace of the sole member `ε` and costs nothing

⊑ᶜ-refl : ∀ {w} → w ⊑ᶜ[ u ] w
⊑ᶜ-refl {w} =
  mkᶜ ε
      (fromWitness {a? = any? (λ t → ε ≼? t) (traces u)} εcov)
      (fromWitness {a? = all? (λ t → duration ε ≤? duration t) (traces u)}
                   (All.tabulate εbud))
      (∙-identityʳ w)
  where
    εcov : Any (λ t → ε ≼ t) (traces u)
    εcov = here (≼-refl ε)

    εbud : ∀ {x} → x ∈ traces u → duration ε ≤ duration x
    εbud x∈ = subst (λ z → duration ε ≤ duration z) (sym (∈-[ε]⁻ x∈)) ≤-refl

-- transitivity multiplies the grades, sequencing the two continuations:
-- the covering members multiply, and so do the two budgets, because the
-- duration is a monoid homomorphism for sequencing

⊑ᶜ-trans : ∀ {P Q w w' w''}
         → w ⊑ᶜ[ P ] w' → w' ⊑ᶜ[ Q ] w'' → w ⊑ᶜ[ P · Q ] w''
⊑ᶜ-trans {P} {Q} {w} (mkᶜ t₁ cov₁ bud₁ eq₁) (mkᶜ t₂ cov₂ bud₂ eq₂)
  with find (toWitness cov₁) | find (toWitness cov₂)
... | a , a∈P , t₁≼a | b , b∈Q , t₂≼b =
      mkᶜ (t₁ ∙ t₂)
          (fromWitness
            (Any.map (λ eq → subst ((t₁ ∙ t₂) ≼_) eq (mono-∙ t₁≼a t₂≼b))
                     (∈-cartesianProductWith⁺ _∙_ a∈P b∈Q)))
          (fromWitness (All.tabulate bud))
          (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
  where
    bud : ∀ {r} → r ∈ (traces P ·ˢ traces Q)
        → duration (t₁ ∙ t₂) ≤ duration r
    bud r∈ with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) r∈
    ... | x , y , x∈P , y∈Q , refl =
          ≤-trans (≤-reflexive (duration-∙ t₁ t₂))
                  (≤-trans (+-mono-≤ (All.lookup (toWitness bud₁) x∈P)
                                     (All.lookup (toWitness bud₂) y∈Q))
                           (≤-reflexive (sym (duration-∙ x y))))

-- covariance: the may half is transported along the Hoare half of the
-- grade order, the must half along the Smyth half -- a member of the
-- larger set is above a member of the smaller one, whose budget it
-- therefore inherits

⊑ᶜ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᶜ[ P ] w' → w ⊑ᶜ[ Q ] w'
⊑ᶜ-mono {P} {Q} (hoare , smyth) (mkᶜ cont cov bud eq) =
  mkᶜ cont (fromWitness may) (fromWitness (All.tabulate must)) eq
  where
    may : Any (λ t → cont ≼ t) (traces Q)
    may with find (toWitness cov)
    ... | t , t∈P , cont≼t
            with find (toWitness (hoare t (fromWitness t∈P)))
    ...     | t' , t'∈Q , t≼t' =
              Any.map (λ e → subst (cont ≼_) e (≼-trans cont≼t t≼t')) t'∈Q

    must : ∀ {t} → t ∈ traces Q → duration cont ≤ duration t
    must {t} t∈Q with find (toWitness (smyth t (fromWitness t∈Q)))
    ... | s , s∈P , s≼t =
          ≤-trans (All.lookup (toWitness bud) s∈P) (duration-≼ s≼t)

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and both witnesses are irrelevant proofs

⊑ᶜ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᶜ[ P ] w') → p ≡ q
⊑ᶜ-irrelevant {P} {w} (mkᶜ cont cov bud refl) (mkᶜ cont' cov' bud' eq')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl =
        cong₂ (λ z z' → mkᶜ cont z z' refl)
              (True-irr (any? (λ t → cont ≼? t) (traces P)) cov cov')
              (True-irr (all? (λ t → duration cont ≤? duration t) (traces P))
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
-- The Smyth half is load-bearing
--
-- For an operation of non-zero cost, `Separation`'s sets `P = { o }`
-- and `Q = { ε , o }` are related by the Hoare lift (`Separation.P≼Q`)
-- yet `⊑ᶜ` does not transport from `P` to `Q`: the empty schedule of
-- `Q` leaves no budget for the operation. So the Hoare half alone does
-- not give `⊑-mono` for this frame.

module MustSeparation (o : Op) (co : ¬ (c o ≡ 0)) where

  open Separation o using (⟨o⟩; P; Q)

  step : ε ⊑ᶜ[ P ] ⟨o⟩
  step =
    mkᶜ ⟨o⟩
        (fromWitness {a? = any? (λ t → ⟨o⟩ ≼? t) (traces P)}
                     (here (≼-refl ⟨o⟩)))
        (fromWitness {a? = all? (λ t → duration ⟨o⟩ ≤? duration t) (traces P)}
                     (All.tabulate bud))
        (∙-identityˡ ⟨o⟩)
    where
      bud : ∀ {x} → x ∈ traces P → duration ⟨o⟩ ≤ duration x
      bud (here refl) = ≤-refl
      bud (there ())

  ¬step : ¬ (ε ⊑ᶜ[ Q ] ⟨o⟩)
  ¬step (mkᶜ cont cov bud eq) = co (m+n≡0⇒m≡0 (c o) (n≤0⇒n≡0 dur≤0))
    where
      cont≡ : cont ≡ ⟨o⟩
      cont≡ = trans (sym (∙-identityˡ cont)) eq

      dur≤0 : duration ⟨o⟩ ≤ 0
      dur≤0 = subst (λ z → duration z ≤ 0) cont≡
                    (All.lookup (toWitness bud) (here refl))

  ⊑ᶜ-needs-smyth : ¬ ({w w' : Trace} → w ⊑ᶜ[ P ] w' → w ⊑ᶜ[ Q ] w')
  ⊑ᶜ-needs-smyth f = ¬step (f step)
