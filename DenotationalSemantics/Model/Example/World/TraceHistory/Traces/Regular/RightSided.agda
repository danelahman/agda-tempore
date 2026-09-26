-------------------------------------------------------------------------
-- A trace-history Kripke frame for regular sets of timed traces as    --
-- upper bounds.                                                       --
--                                                                     --
-- Worlds are timed traces: the history observed so far. A grade `L`   --
-- reaches the histories obtained by appending a run it permits:       --
--                                                                     --
--   w ⊑ʳ[ L ] w'   iff   Σ[ cont ] w ∙ cont ≡ w'                      --
--                          and  L permits cont                        --
--                                                                     --
-- As for the finite subsets, accessibility is membership. The proofs  --
-- use the lemmas of the grade on languages, without computation on    --
-- tables.                                                             --
-------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Regular.RightSided
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Bool.Properties using (T-irrelevant)

open import Syntax.Grades.Traces.Base Op
  using (Trace; ε; _∙_; ∙-assoc; ∙-identityʳ; ∙-cancelˡ)
open import Syntax.Grades.Example.Traces.Regular.Base Op n code code-injective
  using (enc)
open import Syntax.Grades.Example.Traces.Regular.RightSided Op n code code-injective
  using (Regular; u; _·ᴿ_; _≾_; _permits_; permits-∙; ≾⇒⊆; ∈u⁺; right-sided)

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Accessibility on trace histories

infix 5 _⊑ʳ[_]_

record _⊑ʳ[_]_ (w : Trace) (L : Regular) (w' : Trace) : Set where
  constructor mkʳ
  field
    cont      : Trace                        -- continuation
    extends   : w ∙ cont ≡ w'                -- `w'` extends `w`
    permitted : L permits cont               -- a run the grade permits

open _⊑ʳ[_]_

-- reflexivity at the unit grade: the empty run

⊑ʳ-refl : ∀ {w} → w ⊑ʳ[ u ] w
⊑ʳ-refl {w} = mkʳ ε (∙-identityʳ w) ∈u⁺

-- transitivity multiplies the grades: the two continuations sequence
-- into one the product permits

⊑ʳ-trans : ∀ {L M w w' w''}
         → w ⊑ʳ[ L ] w' → w' ⊑ʳ[ M ] w'' → w ⊑ʳ[ L ·ᴿ M ] w''
⊑ʳ-trans {L} {M} {w} (mkʳ t₁ eq₁ p₁) (mkʳ t₂ eq₂ p₂) =
  mkʳ (t₁ ∙ t₂)
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
      (permits-∙ L M {t₁} {t₂} p₁ p₂)

-- covariance: a run permitted by a smaller language is permitted by a
-- larger one

⊑ʳ-mono : ∀ {L M w w'} → L ≾ M → w ⊑ʳ[ L ] w' → w ⊑ʳ[ M ] w'
⊑ʳ-mono {L} {M} r (mkʳ t eq p) = mkʳ t eq (≾⇒⊆ L M r (enc t) p)

-- proof irrelevance: the continuation is determined by left
-- cancellation, and membership is a truth value

⊑ʳ-irrelevant : ∀ {L w w'} → (p q : w ⊑ʳ[ L ] w') → p ≡ q
⊑ʳ-irrelevant {L} {w} (mkʳ t refl p) (mkʳ t' eq' p')
  with ∙-cancelˡ w eq'
... | refl with uip {p = eq'} {q = refl} | T-irrelevant p p'
... | refl | refl = refl

------------------------------------------------------------------------
-- The frame.

histories : World right-sided
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ʳ[_]_
  ; ⊑-refl        = ⊑ʳ-refl
  ; ⊑-trans       = λ {L} {M} → ⊑ʳ-trans {L} {M}
  ; ⊑-mono        = λ {L} {M} → ⊑ʳ-mono {L} {M}
  ; ⊑-irrelevant  = λ {L} → ⊑ʳ-irrelevant {L}
  }
