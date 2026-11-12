------------------------------------------------------------------------
-- Worked instances of the regular grade of upper bounds.             --
--                                                                    --
-- A grade is a non-empty regular set of runs containing every run of --
-- the computation. Weakening is inclusion; unlike in                 --
-- `Worked.Traces.FiniteRunSets.UpperBound`, the greatest grade       --
-- permits every run without absorbing products. Literals are         --
-- extended regular expressions, and an empty literal is rejected.    --
--                                                                    --
-- The product does not commute, and the unit is not least.           --
--                                                                    --
-- Every claim is established by the decision procedure of the grade. --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.Regular.UpperBound where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Op : Set where
  read send : Op

code : Op → Fin 2
code read = zero
code send = suc zero

code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
code-injective {read} {read} _ = refl
code-injective {send} {send} _ = refl

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (isYes; False; toWitnessFalse)
open import Grades.Base using (module Grade)
open import Grades.Regular.Decide 3 using (nonempty?)
open import Grades.Examples.Traces.Regular.UpperBound Op 2 code code-injective
open Grades.Base.Grade upper-bound using (_≾?_; _≃?_)
  renaming (_≾_ to _≾ᵍ_; _·_ to _·ᵍ_; 𝟏 to 𝟏ᵍ)

read·tick²≾⊤ : isYes ((operationᴿ read ·ᴿ ι 2) ≾? ⊤) ≡ true
read·tick²≾⊤ = refl

send⋠read : isYes (operationᴿ send ≾? operationᴿ read) ≡ false
send⋠read = refl

ι-2+3 : isYes ((ι 2 ·ᴿ ι 3) ≃? ι 5) ≡ true
ι-2+3 = refl

-- `⊤` is not absorbing

⊤⋠tick·⊤ : isYes (⊤ ≾? (ι 1 ·ᴿ ⊤)) ≡ false
⊤⋠tick·⊤ = refl

-- literals

distrib : isYes (⌊ (‵op read ∣ ‵op send) · delay 1 ⌋
                 ≃? ⌊ ‵op read · delay 1 ∣ ‵op send · delay 1 ⌋) ≡ true
distrib = refl

-- the runs that never send

no-send : Expr
no-send = Σ * & ~ (Σ * · ‵op send · Σ *)

reads≾no-send : isYes (⌊ (‵op read · delay 2) * ⌋ ≾? ⌊ no-send ⌋) ≡ true
reads≾no-send = refl

send⋠no-send : isYes (⌊ ‵op read · ‵op send ⌋ ≾? ⌊ no-send ⌋) ≡ false
send⋠no-send = refl

de-morgan : isYes (⌊ ~ (‵op read ∣ ‵op send) ⌋ ≃? ⌊ ~ ‵op read & ~ ‵op send ⌋) ≡ true
de-morgan = refl

-- `‵op send & ~ ‵op send` is empty, so `⌊ ‵op send & ~ ‵op send ⌋` is
-- rejected

empty : isYes (nonempty? (elab (‵op send & ~ ‵op send)) (elab-wf (‵op send & ~ ‵op send)))
      ≡ false
empty = refl

-- comparisons that fail, established by the decision

fails : (c d : Regular) {p : False (c ≾? d)} → ¬ (c ≾ᵍ d)
fails c d {p} = toWitnessFalse p

-- the product does not commute: reading and then sending is not among
-- the runs of sending and then reading

not-commutative :
  ¬ (operationᴿ read ·ᵍ operationᴿ send ≾ᵍ operationᴿ send ·ᵍ operationᴿ read)
not-commutative =
  fails (operationᴿ read ·ᵍ operationᴿ send) (operationᴿ send ·ᵍ operationᴿ read)

-- the unit is not least: the empty run is not a run of a read

unit-not-least : ¬ (𝟏ᵍ ≾ᵍ operationᴿ read)
unit-not-least = fails 𝟏ᵍ (operationᴿ read)
