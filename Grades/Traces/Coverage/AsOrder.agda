-------------------------------------------------------------------------
-- The coverage partial order, packaged as a `TraceOrder`.             --
--                                                                     --
-- The interface `Allowance.AsOrder` meets, at the order a guarantee   --
-- wants. `mono-∙` holds only with the second slack pinned to zero     --
-- (the slack-additive form fails, as `Coverage.Moves` records),       --
-- which is the instance the lift, taken at slack zero, needs. Nothing --
-- is asked of `costˡᵒ`: an operation is never bought.                 --
-------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Coverage.AsOrder
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Grades.Traces.Order T Op
open import Grades.Traces.Coverage T Op costˡᵒ
open import Grades.Traces.Coverage.Antisym T Op costˡᵒ

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
