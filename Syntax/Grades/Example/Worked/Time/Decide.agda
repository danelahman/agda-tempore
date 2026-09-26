------------------------------------------------------------------------
-- Discharging the numeric side conditions of the worked interval     --
-- examples.                                                          --
--                                                                    --
-- Every interval fact in the sibling modules reduces to a comparison --
-- of natural numbers: `≤!` runs `_≤?_`, and `≰!` runs it in the      --
-- other direction.                                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Time.Decide where

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (_≤?_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

≤! : {m n : ℕ} {p : True (m ≤? n)} → m ≤ n
≤! {p = p} = toWitness p

≰! : {m n : ℕ} {p : False (m ≤? n)} → ¬ (m ≤ n)
≰! {p = p} = toWitnessFalse p
