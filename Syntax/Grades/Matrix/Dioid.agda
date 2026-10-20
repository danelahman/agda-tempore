------------------------------------------------------------------------
-- Dioids: idempotent semirings, ordered by their join.               --
--                                                                    --
-- A dioid has a join `_⊕_` with least element `𝟘` and greatest `⊤`,  --
-- and a product `_⊗_` with unit `𝟙` that is monotone, absorbs `𝟘` on --
-- both sides and distributes over `_⊕_` on both sides. The order is  --
-- a decidable, proof-irrelevant preorder, and the laws of the        --
-- product hold up to its equivalence; the inequalities of the        --
-- distributive and absorption laws that follow from monotonicity     --
-- are omitted.                                                       --
------------------------------------------------------------------------

module Syntax.Grades.Matrix.Dioid where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Irrelevant; Decidable)

open import Util.Equality

record Dioid : Set₁ where
  infix  4 _≤_ _≈_
  infixl 6 _⊕_
  infixl 7 _⊗_

  field
    Carrier : Set
    _≤_     : Rel Carrier 0ℓ
    𝟘 𝟙 ⊤   : Carrier
    _⊕_     : Carrier → Carrier → Carrier
    _⊗_     : Carrier → Carrier → Carrier

  _≈_ : Rel Carrier 0ℓ
  a ≈ b = (a ≤ b) × (b ≤ a)

  field
    -- a decidable, proof-irrelevant preorder
    ≤-refl       : Reflexive _≤_
    ≤-trans      : Transitive _≤_
    ≤-irrelevant : Irrelevant _≤_
    _≤?_         : Decidable _≤_

    -- bounded, with `_⊕_` the binary join
    𝟘-≤   : ∀ a → 𝟘 ≤ a
    ≤-⊤   : ∀ a → a ≤ ⊤
    ⊕-ubˡ : ∀ a b → a ≤ a ⊕ b
    ⊕-ubʳ : ∀ a b → b ≤ a ⊕ b
    ⊕-lub : ∀ {a b c} → a ≤ c → b ≤ c → a ⊕ b ≤ c

    -- a monoid, up to the equivalence, monotone in both arguments
    ⊗-identityˡ : ∀ a → 𝟙 ⊗ a ≈ a
    ⊗-identityʳ : ∀ a → a ⊗ 𝟙 ≈ a
    ⊗-assoc     : ∀ a b c → (a ⊗ b) ⊗ c ≈ a ⊗ (b ⊗ c)
    ⊗-mono      : ∀ {a a' b b'} → a ≤ a' → b ≤ b' → a ⊗ b ≤ a' ⊗ b'

    -- absorbing `𝟘` and distributing over `_⊕_`
    ⊗-zeroˡ    : ∀ a → 𝟘 ⊗ a ≤ 𝟘
    ⊗-zeroʳ    : ∀ a → a ⊗ 𝟘 ≤ 𝟘
    ⊗-distribˡ : ∀ a b c → a ⊗ (b ⊕ c) ≤ (a ⊗ b) ⊕ (a ⊗ c)
    ⊗-distribʳ : ∀ a b c → (b ⊕ c) ⊗ a ≤ (b ⊗ a) ⊕ (c ⊗ a)

  ≈-refl : ∀ {a} → a ≈ a
  ≈-refl = ≤-refl , ≤-refl

  ≈-sym : ∀ {a b} → a ≈ b → b ≈ a
  ≈-sym (p , q) = q , p

  ≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
  ≈-trans (p , q) (p' , q') = ≤-trans p p' , ≤-trans q' q

  ≈-reflexive : ∀ {a b} → a ≡ b → a ≈ b
  ≈-reflexive refl = ≈-refl

  ≤-reflexive : ∀ {a b} → a ≡ b → a ≤ b
  ≤-reflexive refl = ≤-refl

  ⊕-mono : ∀ {a a' b b'} → a ≤ a' → b ≤ b' → a ⊕ b ≤ a' ⊕ b'
  ⊕-mono {a' = a'} {b' = b'} p q = ⊕-lub (≤-trans p (⊕-ubˡ a' b')) (≤-trans q (⊕-ubʳ a' b'))

  ⊗-cong : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → a ⊗ b ≈ a' ⊗ b'
  ⊗-cong (p , p') (q , q') = ⊗-mono p q , ⊗-mono p' q'

  -- the join of a list

  ⨁ : List Carrier → Carrier
  ⨁ []       = 𝟘
  ⨁ (a ∷ as) = a ⊕ ⨁ as

  ⨁-ub : ∀ as {a} → a ∈ as → a ≤ ⨁ as
  ⨁-ub (b ∷ bs) (here refl) = ⊕-ubˡ b (⨁ bs)
  ⨁-ub (b ∷ bs) (there p)   = ≤-trans (⨁-ub bs p) (⊕-ubʳ b (⨁ bs))

  ⨁-lub : ∀ as {c} → (∀ {a} → a ∈ as → a ≤ c) → ⨁ as ≤ c
  ⨁-lub []       f = 𝟘-≤ _
  ⨁-lub (a ∷ as) f = ⊕-lub (f (here refl)) (⨁-lub as (λ p → f (there p)))

  -- a product with a join of a list is bounded where each term's is

  ⨁-lub-⊗ʳ : ∀ as {c t} → (∀ {a} → a ∈ as → a ⊗ c ≤ t) → ⨁ as ⊗ c ≤ t
  ⨁-lub-⊗ʳ []       {c} f = ≤-trans (⊗-zeroˡ c) (𝟘-≤ _)
  ⨁-lub-⊗ʳ (a ∷ as) {c} f =
    ≤-trans (⊗-distribʳ c a (⨁ as)) (⊕-lub (f (here refl)) (⨁-lub-⊗ʳ as (λ p → f (there p))))

  ⨁-lub-⊗ˡ : ∀ as {c t} → (∀ {a} → a ∈ as → c ⊗ a ≤ t) → c ⊗ ⨁ as ≤ t
  ⨁-lub-⊗ˡ []       {c} f = ≤-trans (⊗-zeroʳ c) (𝟘-≤ _)
  ⨁-lub-⊗ˡ (a ∷ as) {c} f =
    ≤-trans (⊗-distribˡ c a (⨁ as)) (⊕-lub (f (here refl)) (⨁-lub-⊗ˡ as (λ p → f (there p))))
