------------------------------------------------------------------------
-- The coverage partial order, packaged as a `TraceOrder`.            --
--                                                                    --
-- The same interface `Allowance.AsOrder` meets, at the order a       --
-- guarantee wants. `mono-∙` is available only with the second slack  --
-- pinned to zero -- the slack-additive form is false here, as        --
-- `Coverage.Moves` records -- but the lift is taken at slack zero    --
-- throughout, so that is exactly the instance needed. Nothing here   --
-- asks anything of `costˡᵒ`: an operation is never bought, at any    --
-- price.                                                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Traces.Coverage.AsOrder
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → Duration.Carrier D) where

open import Syntax.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Syntax.Grades.Traces.Order T Op
open import Syntax.Grades.Traces.Coverage T Op costˡᵒ
open import Syntax.Grades.Traces.Coverage.Antisym T Op costˡᵒ

open DecCoverage _≟ₒ_ using (_≼ᶜ?_)

coveragePartialOrder : TracePartialOrder
coveragePartialOrder = record
  { _≼_       = _≼ᶜ_
  ; _≼?_      = _≼ᶜ?_
  ; ≼-refl    = ≼ᶜ-refl
  ; ≼-trans   = λ p q → coe (+-identityʳ 0ᴰ) (≼ᶜ-trans p q)
  ; ≼-antisym = ≼ᶜ-antisym
  ; mono-∙    = mono-∙
  }

coverageOrder : TraceOrder
coverageOrder = record
  { base    = coveragePartialOrder
  ; ≼-nil   = nil
  ; ≼-ε-inv = ≼ᶜ-ε-inv
  }
