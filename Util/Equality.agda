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

-- Congruence in three arguments; the standard library stops at `cong₂`.

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
      → (f : A → B → C → D)
      → {x x' : A} → {y y' : B} → {z z' : C}
      → x ≡ x' → y ≡ y' → z ≡ z'
      → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

-- UIP (provable, since the project does not use --without-K)

uip : ∀ {l} {X : Set l} {x y : X} {p q : x ≡ y} → p ≡ q
uip {p = refl} {q = refl} = refl

-- The dependent eliminator `J` of propositional equality. A definition
-- inside a record body may not case-split on `refl`, so the model records'
-- transport lemmas, such as `Category.substᶜ-≈`, apply `J` at an explicit
-- motive rather than match.

open import Relation.Binary.PropositionalEquality.Properties public
  using (J; dcong)
