---------------------------------------
-- Equality related auxiliary proofs --
---------------------------------------

module Util.Equality where

open import Level renaming (zero to lzero; suc to lsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq public renaming ([_] to [|_|])
open Eq.≡-Reasoning public

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs

-- Assuming function extensionality

postulate
  fun-ext  : ∀ {l₁ l₂} → Extensionality l₁ l₂
  ifun-ext : ∀ {l₁ l₂} → ExtensionalityImplicit l₁ l₂

-- UIP (provable, since the project does not use --without-K)

uip : ∀ {l} {X : Set l} {x y : X} {p q : x ≡ y} → p ≡ q
uip {p = refl} {q = refl} = refl

-- The dependent eliminator `J` of propositional equality. A definition
-- inside a record body may not case-split on `refl`, so the model records'
-- transport lemmas (e.g. `Category.substᶜ-≈`) are proved by *applying* `J`
-- at an explicit motive rather than by matching.

open import Relation.Binary.PropositionalEquality.Properties public
  using (J)
