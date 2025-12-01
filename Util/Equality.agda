---------------------------------------
-- Equality related auxiliary proofs --
---------------------------------------

module Util.Equality where

open import Level renaming (zero to lzero; suc to lsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq public renaming ([_] to [|_|])
open Eq.≡-Reasoning public

open import Axiom.Extensionality.Propositional

-- Assuming function extensionality

postulate
  fun-ext  : ∀ {l₁ l₂} → Extensionality l₁ l₂
  ifun-ext : ∀ {l₁ l₂} → ExtensionalityImplicit l₁ l₂