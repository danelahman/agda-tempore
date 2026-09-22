------------------------------------------------------------------------
-- The coverage preorder, packaged as a `TraceOrder`.                  --
--                                                                    --
-- The same interface `Allowance.AsOrder` meets, at the order a        --
-- guarantee wants. `mono-∙` is available only with the second slack   --
-- pinned to zero -- the slack-additive form is false here, as         --
-- `Coverage.Moves` records -- but the lift is taken at slack zero     --
-- throughout, so that is exactly the instance needed. Nothing here    --
-- asks anything of `costˡᵒ`: an operation is never bought, at any     --
-- price.                                                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Traces.Coverage.AsOrder
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → ℕ) where

open import Syntax.Grades.Traces.Order Op
open import Syntax.Grades.Traces.Coverage Op costˡᵒ

open DecCoverage _≟ₒ_ using (_≼ᶜ?_)

coverageOrder : TraceOrder
coverageOrder = record
  { _≼_     = _≼ᶜ_
  ; _≼?_    = _≼ᶜ?_
  ; ≼-refl  = ≼ᶜ-refl
  ; ≼-trans = ≼ᶜ-trans
  ; ≼-nil   = nil
  ; mono-∙  = mono-∙
  ; ≼-ε-inv = ≼ᶜ-ε-inv
  }
