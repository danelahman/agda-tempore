------------------------------------------------------------------------
-- Equivariant dioids: dioids on which the names act.                 --
--                                                                    --
-- The transpositions `swap a b` of names act on the dioid by         --
-- automorphisms: monotone, involutive, the identity at `a = b`, and  --
-- preserving `𝟘`, `𝟙`, `_⊕_` and `_⊗_`. A permutation is a list of   --
-- transpositions, and it fixes a finite set `A` of names when none   --
-- of its transpositions touches `A`. The dioid has the joins of      --
-- orbits: for every `A` and `x`, `⟨ x ⟩ A` is the least upper bound  --
-- of the elements `π · x` for the permutations `π` fixing `A`, and   --
-- `_⊗_` distributes over it on both sides.                           --
--                                                                    --
-- A dioid whose elements name no names is equivariant with the       --
-- trivial action, its orbits being single elements (`trivial`).      --
------------------------------------------------------------------------

open import Syntax.Grades.Indexed using (Names)

module Syntax.Grades.Matrix.Nominal (𝒩 : Names) where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Syntax.Grades.Matrix.Dioid using (Dioid)

open import Util.Equality

open Names 𝒩 using (Name)

-- permutations as lists of transpositions, and those fixing a set

Perm : Set
Perm = List (Name × Name)

Fixes : List Name → Perm → Set
Fixes A = All (λ (a , b) → (a ∉ A) × (b ∉ A))

-- a permutation acting through the action of its transpositions

along : {C : Set} → (Name → Name → C → C) → Perm → C → C
along f []            x = x
along f ((a , b) ∷ π) x = f a b (along f π x)

record Equivariant (S : Dioid) : Set₁ where
  open Dioid S
  field
    act       : Name → Name → Carrier → Carrier
    act-mono  : ∀ {a b x y} → x ≤ y → act a b x ≤ act a b y
    act-inv   : ∀ a b x → act a b (act a b x) ≈ x
    act-refl  : ∀ a x → act a a x ≈ x
    act-𝟘     : ∀ a b → act a b 𝟘 ≈ 𝟘
    act-𝟙     : ∀ a b → act a b 𝟙 ≈ 𝟙
    act-⊕     : ∀ a b x y → act a b (x ⊕ y) ≈ act a b x ⊕ act a b y
    act-⊗     : ∀ a b x y → act a b (x ⊗ y) ≈ act a b x ⊗ act a b y

  -- the action of a permutation
  actᴾ : Perm → Carrier → Carrier
  actᴾ = along act

  field
    -- the joins of orbits
    ⟨_⟩_      : Carrier → List Name → Carrier
    orbit-ub  : ∀ {A x} π → Fixes A π → actᴾ π x ≤ ⟨ x ⟩ A
    orbit-lub : ∀ {A x t} → (∀ π → Fixes A π → actᴾ π x ≤ t) → ⟨ x ⟩ A ≤ t
    orbit-⊗ʳ  : ∀ {A x c t} → (∀ π → Fixes A π → actᴾ π x ⊗ c ≤ t) → (⟨ x ⟩ A) ⊗ c ≤ t
    orbit-⊗ˡ  : ∀ {A x c t} → (∀ π → Fixes A π → c ⊗ actᴾ π x ≤ t) → c ⊗ (⟨ x ⟩ A) ≤ t

  -- derived

  act-cong : ∀ {a b x y} → x ≈ y → act a b x ≈ act a b y
  act-cong (p , q) = act-mono p , act-mono q

  act-⊤ : ∀ a b → act a b ⊤ ≈ ⊤
  act-⊤ a b = ≤-⊤ _ , ≤-trans (proj₂ (act-inv a b ⊤)) (act-mono (≤-⊤ _))

  -- an element below `𝟘` stays below it
  act-≤𝟘 : ∀ {a b x} → x ≤ 𝟘 → act a b x ≤ 𝟘
  act-≤𝟘 {a} {b} p = ≤-trans (act-mono p) (proj₁ (act-𝟘 a b))

  act-≤𝟘⁻ : ∀ {a b x} → act a b x ≤ 𝟘 → x ≤ 𝟘
  act-≤𝟘⁻ {a} {b} {x} p = ≤-trans (proj₂ (act-inv a b x)) (act-≤𝟘 p)

  ⟨⟩-ub : ∀ {A} x → x ≤ ⟨ x ⟩ A
  ⟨⟩-ub x = orbit-ub [] []

------------------------------------------------------------------------
-- The trivial action

module _ (S : Dioid) where

  open Dioid S

  trivial : Equivariant S
  trivial = record
    { act       = λ _ _ x → x
    ; act-mono  = λ p → p
    ; act-inv   = λ _ _ _ → ≈-refl
    ; act-refl  = λ _ _ → ≈-refl
    ; act-𝟘     = λ _ _ → ≈-refl
    ; act-𝟙     = λ _ _ → ≈-refl
    ; act-⊕     = λ _ _ _ _ → ≈-refl
    ; act-⊗     = λ _ _ _ _ → ≈-refl
    ; ⟨_⟩_      = λ x _ → x
    ; orbit-ub  = λ π _ → ≤-reflexive (fixed π)
    ; orbit-lub = λ f → f [] []
    ; orbit-⊗ʳ  = λ f → f [] []
    ; orbit-⊗ˡ  = λ f → f [] []
    }
    where
      fixed : ∀ {x} (π : Perm) → along (λ _ _ y → y) π x ≡ x
      fixed []      = refl
      fixed (_ ∷ π) = fixed π
