------------------------------------------------------------------------
-- A trace-history Kripke frame for convexly ordered sets of traces as  --
-- the resource grades.                                                 --
--                                                                    --
-- Worlds and accessibility are those of the Hoare-ordered sets of      --
-- traces: `w ⊑ʰ[ P ] w'` still asks for a continuation covered by      --
-- *some* member of `P`. Being Σ-shaped, that relation is covariant     --
-- along the Hoare lift, and the convex order is contained in it, so    --
-- `⊑-mono` is the Hoare half of the grade order. The Smyth half is     --
-- not read by the frame: it constrains which coercions are derivable,  --
-- not which worlds a grade reaches.                                    --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.SetOfTracesConvexWithTraceHistories
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.Product using (proj₁)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.SetOfTracesConvex Op _≟ₒ_ using (traces-convex)

open import DenotationalSemantics.Model.World

open import DenotationalSemantics.Model.Example.World.SetOfTracesUpToSubtraceWithTraceHistories
  Op _≟ₒ_ using (_⊑ʰ[_]_; ⊑ʰ-refl; ⊑ʰ-trans; ⊑ʰ-mono; ⊑ʰ-irrelevant)

histories : World traces-convex
histories = record
  { W             = Trace
  ; _⊑[_]_        = _⊑ʰ[_]_
  ; ⊑-refl        = ⊑ʰ-refl
  ; ⊑-trans       = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono        = λ {ρ₁} {ρ₂} rel → ⊑ʰ-mono {ρ₁} {ρ₂} (proj₁ rel)
  ; ⊑-irrelevant  = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
