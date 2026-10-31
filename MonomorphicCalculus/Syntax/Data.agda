--------------------------------------------------------------------------
-- The data of a type, and their comparison                             --
--                                                                      --
-- `⟪ A ⟫` is the set of closed canonical values of `A` read as data:   --
-- constants, booleans, numerals, pairs, injections and lists. A        --
-- subtyping acts on data by `⟪_⟫ˢ`. At an eternal type the data carry  --
-- the structural order `compareᵈ`: the base types' own, `false` before --
-- `true`, the usual order on numerals, and the lexicographic orders on --
-- pairs, injections (`inl` before `inr`) and lists. `⌈_⌉` embeds data  --
-- as values.                                                           --
--------------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Unit using (⊤; tt)

open import Language.Comparisons
open import Language.Spec

open import Util.Equality

module MonomorphicCalculus.Syntax.Data (S : LanguageSpec) where

open LanguageSpec S

open import MonomorphicCalculus.Syntax.Types     S
open import MonomorphicCalculus.Syntax.Subtyping S
open import MonomorphicCalculus.Syntax.Contexts  S using (Ctx)
open import MonomorphicCalculus.Syntax.Terms     S
  using (_⊢ᵛ⦂_; const; ⋆; true; false; zero; succ; ⦉_,_⦊; inl; inr; nil; cons)

-- The data of a type

⟪_⟫ : VType → Set
⟪ Base b    ⟫ = BaseConstants b
⟪ unit      ⟫ = ⊤
⟪ bool      ⟫ = 𝔹
⟪ nat       ⟫ = ℕ
⟪ A |×| B   ⟫ = ⟪ A ⟫ × ⟪ B ⟫
⟪ A |+| B   ⟫ = ⟪ A ⟫ ⊎ ⟪ B ⟫
⟪ list A    ⟫ = List ⟪ A ⟫
⟪ empty     ⟫ = ⊥
⟪ A ⇒ C     ⟫ = ⊤
⟪ C ⇛ D     ⟫ = ⊤
⟪ [ ρ ] A   ⟫ = ⊤

-- The action of a subtyping on data

⟪_⟫ˢ : ∀ {A A'} → A <:ᵛ A' → ⟪ A ⟫ → ⟪ A' ⟫
⟪ Baseₛ refl ⟫ˢ c       = c
⟪ unitₛ      ⟫ˢ x       = x
⟪ boolₛ      ⟫ˢ x       = x
⟪ natₛ       ⟫ˢ x       = x
⟪ p |×|ₛ q   ⟫ˢ (x , y) = ⟪ p ⟫ˢ x , ⟪ q ⟫ˢ y
⟪ p |+|ₛ q   ⟫ˢ x       = map⊎ ⟪ p ⟫ˢ ⟪ q ⟫ˢ x
⟪ listₛ p    ⟫ˢ xs      = map ⟪ p ⟫ˢ xs
⟪ emptyₛ     ⟫ˢ x       = x
⟪ p ⇒ₛ q     ⟫ˢ _       = tt
⟪ p ⇛ₛ q     ⟫ˢ _       = tt
⟪ [ q ]ₛ p   ⟫ˢ _       = tt

-- The order on data

compareᵈ : ∀ {A} → Et A → ⟪ A ⟫ → ⟪ A ⟫ → Order
compareᵈ (Baseₑ eb)      c        c'        = compareᵇ eb c c'
compareᵈ unitₑ           _        _         = equal
compareᵈ boolₑ           x        y         = compareᴮ x y
compareᵈ natₑ            n        m         = compareᴺ n m
compareᵈ (et₁ |×|ₑ et₂)  (x , y)  (x' , y') = lexᵒ (compareᵈ et₁ x x') (compareᵈ et₂ y y')
compareᵈ (et₁ |+|ₑ et₂)  (inj₁ x) (inj₁ x') = compareᵈ et₁ x x'
compareᵈ (et₁ |+|ₑ et₂)  (inj₁ _) (inj₂ _)  = less
compareᵈ (et₁ |+|ₑ et₂)  (inj₂ _) (inj₁ _)  = greater
compareᵈ (et₁ |+|ₑ et₂)  (inj₂ y) (inj₂ y') = compareᵈ et₂ y y'
compareᵈ (listₑ et)      xs       ys        = compareᴸ (compareᵈ et) xs ys
compareᵈ emptyₑ          ()       _

-- Data as values

⌈_⌉ : ∀ {Γ A} → Et A → ⟪ A ⟫ → Γ ⊢ᵛ⦂ A
⌈ Baseₑ _ ⌉        c        = const _ c
⌈ unitₑ ⌉          _        = ⋆
⌈ boolₑ ⌉          true     = true
⌈ boolₑ ⌉          false    = false
⌈ natₑ ⌉           zero     = zero
⌈ natₑ ⌉           (suc n)  = succ (⌈ natₑ ⌉ n)
⌈ et₁ |×|ₑ et₂ ⌉   (x , y)  = ⦉ ⌈ et₁ ⌉ x , ⌈ et₂ ⌉ y ⦊
⌈ et₁ |+|ₑ et₂ ⌉   (inj₁ x) = inl (⌈ et₁ ⌉ x)
⌈ et₁ |+|ₑ et₂ ⌉   (inj₂ y) = inr (⌈ et₂ ⌉ y)
⌈ listₑ et ⌉       []       = nil
⌈ listₑ et ⌉       (x ∷ xs) = cons (⌈ et ⌉ x) (⌈ listₑ et ⌉ xs)
⌈ emptyₑ ⌉         ()

-- The boolean a comparison returns

⌈_⌉ᵇ : ∀ {Γ} → 𝔹 → Γ ⊢ᵛ⦂ bool
⌈ b ⌉ᵇ = ⌈ boolₑ ⌉ b
