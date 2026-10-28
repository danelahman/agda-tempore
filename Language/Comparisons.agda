------------------------------------------------------------------
-- Comparison relations                                         --
--                                                              --
-- The six relations of the comparison rule `cmp`: equality,    --
-- disequality and the four orderings. All are typed alike, so  --
-- one rule tagged by the relation covers them. Each relation   --
-- is read off one three-way comparison, an `Order`.            --
------------------------------------------------------------------

module Language.Comparisons where

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)

data Cmp : Set where
  eq ne lt le gt ge : Cmp

-- The outcome of a three-way comparison

data Order : Set where
  less equal greater : Order

-- Whether a relation holds of an outcome

holds : Cmp → Order → 𝔹
holds eq less    = false
holds eq equal   = true
holds eq greater = false
holds ne less    = true
holds ne equal   = false
holds ne greater = true
holds lt less    = true
holds lt equal   = false
holds lt greater = false
holds le less    = true
holds le equal   = true
holds le greater = false
holds gt less    = false
holds gt equal   = false
holds gt greater = true
holds ge less    = false
holds ge equal   = true
holds ge greater = true

-- Lexicographic combination: the first outcome decides unless it is `equal`

lexᵒ : Order → Order → Order
lexᵒ less    _ = less
lexᵒ equal   o = o
lexᵒ greater _ = greater

-- The structural orders: `false` before `true`, the usual order on
-- numerals, and the lexicographic order on lists given one on elements

compareᴮ : 𝔹 → 𝔹 → Order
compareᴮ false false = equal
compareᴮ false true  = less
compareᴮ true  false = greater
compareᴮ true  true  = equal

compareᴺ : ℕ → ℕ → Order
compareᴺ zero    zero    = equal
compareᴺ zero    (suc _) = less
compareᴺ (suc _) zero    = greater
compareᴺ (suc n) (suc m) = compareᴺ n m

compareᴸ : ∀ {X : Set} → (X → X → Order) → List X → List X → Order
compareᴸ c []       []       = equal
compareᴸ c []       (_ ∷ _)  = less
compareᴸ c (_ ∷ _)  []       = greater
compareᴸ c (x ∷ xs) (y ∷ ys) = lexᵒ (c x y) (compareᴸ c xs ys)
