------------------------------------------------------------------------
-- The greatest and least value of a natural-number measure over a    --
-- finite list.                                                       --
--                                                                    --
-- Each is characterised by two facts: it bounds the value of every   --
-- member, and on a non-empty list some member attains it. The        --
-- properties used by the count maps (invariance under a change of    --
-- list with the same members, additivity over a product, and the     --
-- join over a concatenation) follow from these two.                  --
------------------------------------------------------------------------

module Syntax.Grades.Example.Counts.Extrema where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; _≤_; _⊔_; _⊓_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-antisym; ⊔-sel; ⊓-sel;
         m≤m⊔n; m≤n⊔m; m⊓n≤m; m⊓n≤n; ⊔-lub; ⊓-glb; ⊔-identityʳ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Util.Equality

------------------------------------------------------------------------
-- Non-empty lists

NonEmpty : {A : Set} → List A → Set
NonEmpty []      = ⊥
NonEmpty (_ ∷ _) = ⊤

------------------------------------------------------------------------
-- The greatest value, zero on the empty list

module _ {A : Set} (f : A → ℕ) where

  maxOf : List A → ℕ
  maxOf []       = zero
  maxOf (x ∷ xs) = f x ⊔ maxOf xs

  maxOf-mem : {t : A} {xs : List A} → t ∈ xs → f t ≤ maxOf xs
  maxOf-mem {xs = x ∷ xs} (here refl) = m≤m⊔n (f x) (maxOf xs)
  maxOf-mem {xs = x ∷ xs} (there m)   =
    ≤-trans (maxOf-mem m) (m≤n⊔m (f x) (maxOf xs))

  maxOf-attained : (xs : List A) → NonEmpty xs
                 → Σ A λ t → t ∈ xs × maxOf xs ≡ f t
  maxOf-attained (x ∷ [])     _ = x , here refl , ⊔-identityʳ (f x)
  maxOf-attained (x ∷ y ∷ ys) _
    with ⊔-sel (f x) (maxOf (y ∷ ys)) | maxOf-attained (y ∷ ys) tt
  ... | inj₁ eq | _              = x , here refl , eq
  ... | inj₂ eq | t , t∈ , eq'   = t , there t∈ , trans eq eq'

  maxOf-bound : {b : ℕ} (xs : List A) → (∀ {t} → t ∈ xs → f t ≤ b) → maxOf xs ≤ b
  maxOf-bound []       h = z≤n
  maxOf-bound (x ∷ xs) h = ⊔-lub (h (here refl)) (maxOf-bound xs (λ m → h (there m)))

  -- two lists whose members bound each other's have the same maximum

  maxOf-cover : (xs ys : List A)
              → (∀ {t} → t ∈ xs → f t ≤ maxOf ys)
              → (∀ {t} → t ∈ ys → f t ≤ maxOf xs)
              → maxOf xs ≡ maxOf ys
  maxOf-cover xs ys h k = ≤-antisym (maxOf-bound xs h) (maxOf-bound ys k)

  maxOf-same : (xs ys : List A)
             → (∀ {t} → t ∈ xs → t ∈ ys) → (∀ {t} → t ∈ ys → t ∈ xs)
             → maxOf xs ≡ maxOf ys
  maxOf-same xs ys g h =
    maxOf-cover xs ys (λ m → maxOf-mem (g m)) (λ m → maxOf-mem (h m))

  maxOf-++ : (xs ys : List A) → maxOf (xs ++ ys) ≡ maxOf xs ⊔ maxOf ys
  maxOf-++ xs ys =
    ≤-antisym
      (maxOf-bound (xs ++ ys) λ m → case (∈-++⁻ xs m))
      (⊔-lub (maxOf-bound xs (λ m → maxOf-mem (∈-++⁺ˡ m)))
             (maxOf-bound ys (λ m → maxOf-mem (∈-++⁺ʳ xs m))))
    where
      case : ∀ {t} → _ → f t ≤ maxOf xs ⊔ maxOf ys
      case (inj₁ m) = ≤-trans (maxOf-mem m) (m≤m⊔n _ _)
      case (inj₂ m) = ≤-trans (maxOf-mem m) (m≤n⊔m _ _)

------------------------------------------------------------------------
-- The least value, meaningful on a non-empty list

module _ {A : Set} (f : A → ℕ) where

  minOf : List A → ℕ
  minOf []           = zero
  minOf (x ∷ [])     = f x
  minOf (x ∷ y ∷ ys) = f x ⊓ minOf (y ∷ ys)

  minOf-mem : {t : A} {xs : List A} → t ∈ xs → minOf xs ≤ f t
  minOf-mem {xs = x ∷ []}     (here refl) = ≤-refl
  minOf-mem {xs = x ∷ y ∷ ys} (here refl) = m⊓n≤m (f x) (minOf (y ∷ ys))
  minOf-mem {xs = x ∷ y ∷ ys} (there m)   =
    ≤-trans (m⊓n≤n (f x) (minOf (y ∷ ys))) (minOf-mem m)

  minOf-attained : (xs : List A) → NonEmpty xs
                 → Σ A λ t → t ∈ xs × minOf xs ≡ f t
  minOf-attained (x ∷ [])     _ = x , here refl , refl
  minOf-attained (x ∷ y ∷ ys) _
    with ⊓-sel (f x) (minOf (y ∷ ys)) | minOf-attained (y ∷ ys) tt
  ... | inj₁ eq | _              = x , here refl , eq
  ... | inj₂ eq | t , t∈ , eq'   = t , there t∈ , trans eq eq'

  minOf-bound : {b : ℕ} (xs : List A) → NonEmpty xs
              → (∀ {t} → t ∈ xs → b ≤ f t) → b ≤ minOf xs
  minOf-bound xs ne h with minOf-attained xs ne
  ... | t , t∈ , eq = ≤-trans (h t∈) (≤-reflexive (sym eq))

  -- two non-empty lists each of whose members lies above some member of
  -- the other have the same minimum

  minOf-cover : (xs ys : List A) → NonEmpty xs → NonEmpty ys
              → (∀ {t} → t ∈ xs → minOf ys ≤ f t)
              → (∀ {t} → t ∈ ys → minOf xs ≤ f t)
              → minOf xs ≡ minOf ys
  minOf-cover xs ys nx ny h k =
    ≤-antisym (minOf-bound ys ny k) (minOf-bound xs nx h)

  minOf-same : (xs ys : List A) → NonEmpty xs → NonEmpty ys
             → (∀ {t} → t ∈ xs → t ∈ ys) → (∀ {t} → t ∈ ys → t ∈ xs)
             → minOf xs ≡ minOf ys
  minOf-same xs ys nx ny g h =
    minOf-cover xs ys nx ny (λ m → minOf-mem (g m)) (λ m → minOf-mem (h m))

  minOf-++ : (xs ys : List A) → NonEmpty xs → NonEmpty ys
           → minOf (xs ++ ys) ≡ minOf xs ⊓ minOf ys
  minOf-++ xs ys nx ny =
    ≤-antisym
      (⊓-glb (minOf-bound xs nx (λ m → minOf-mem (∈-++⁺ˡ m)))
             (minOf-bound ys ny (λ m → minOf-mem (∈-++⁺ʳ xs m))))
      (minOf-bound (xs ++ ys) (++-ne xs nx) λ m → case (∈-++⁻ xs m))
    where
      ++-ne : (xs : List A) → NonEmpty xs → NonEmpty (xs ++ ys)
      ++-ne (_ ∷ _) _ = tt

      case : ∀ {t} → _ → minOf xs ⊓ minOf ys ≤ f t
      case (inj₁ m) = ≤-trans (m⊓n≤m _ _) (minOf-mem m)
      case (inj₂ m) = ≤-trans (m⊓n≤n _ _) (minOf-mem m)
