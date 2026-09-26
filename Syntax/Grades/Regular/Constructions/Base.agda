------------------------------------------------------------------------
-- Shared lemmas for the constructions: Boolean tests, finite sets of   --
-- states as strictly increasing lists, enumerations, and tables.      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_; _≡ᵇ_; _<ᵇ_; _≤_; _<_; z≤n; s≤s)

module Syntax.Grades.Regular.Constructions.Base (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Bool.Properties using (T-≡; T-∧)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; _++_; map; foldr; length; concatMap)
open import Data.List.Properties using (length-map; length-++)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.Nat.Properties
  using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; ≮⇒≥; ≤∧≢⇒<; <-trans; ≤-refl; ≤-reflexive; +-comm;
         *-mono-≤; n<1+n; <-irrefl; ≤-trans; +-suc; +-identityʳ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import Syntax.Grades.Regular.Automaton k hiding (_∈_; _⊆_)
open import Syntax.Grades.Regular.Basics k public
  using (T-true; T-false; ≡ᵇ-refl; ≡ᵇ-true; ≡ᵇ-false; ==ⁿ-sound; ==ⁿ-refl; all-lookup; next-<; δ*-table)
open import Syntax.Grades.Regular.Operations k using (insert; fromList)

------------------------------------------------------------------------
-- Boolean tests

-- acceptance by some member

T-any⁻ : ∀ {A : Set} (f : A → Bool) xs → T (any f xs) → Any (λ x → T (f x)) xs
T-any⁻ f (x ∷ xs) t with f x in e
... | true  = here (T-true e)
... | false = there (T-any⁻ f xs t)

T-any⁺ : ∀ {A : Set} (f : A → Bool) {xs} → Any (λ x → T (f x)) xs → T (any f xs)
T-any⁺ f {x ∷ xs} (here px) with f x
... | true = tt
T-any⁺ f {x ∷ xs} (there p) with f x
... | true  = tt
... | false = T-any⁺ f p

------------------------------------------------------------------------
-- Automata whose equality test decides equality

module _ (A : Automaton) where

  open Automaton A

  lawful-exact : (≟⇒≡ : ∀ {p q} → T (p ≟ q) → p ≡ q)
                 (≟-refl′ : ∀ p → T (p ≟ p))
                 (Good : State → Set)
               → Good start
               → (∀ {p} a → Good p → Good (δ p a))
               → (enum : List State) → length enum ≤ bound
               → (∀ {p} → Good p → p ∈ enum)
               → Lawful A
  lawful-exact ≟⇒≡ ≟-refl′ Good g₀ gδ enum bnd cover = record
    { Good       = Good
    ; good-start = g₀
    ; good-δ     = gδ
    ; ≟-refl     = ≟-refl′
    ; ≟-sym      = λ {p} {q} t → subst (λ r → T (r ≟ p)) (≟⇒≡ t) (≟-refl′ p)
    ; ≟-trans    = λ {p} {q} {r} t u → subst (λ s → T (p ≟ s)) (≟⇒≡ u) t
    ; ≟-final    = λ _ _ t → cong final (≟⇒≡ t)
    ; ≟-δ        = λ {p} _ _ t a →
                     subst (λ s → T (δ p a ≟ δ s a)) (≟⇒≡ t) (≟-refl′ (δ p a))
    ; enum       = enum
    ; enum-bound = bnd
    ; enum-cover = λ g → Any.map (λ {q} p≡q → subst (λ s → T (_ ≟ s)) p≡q (≟-refl′ _))
                                 (cover g)
    }

------------------------------------------------------------------------
-- Enumerations

-- `lo , lo + 1 , … , lo + n - 1`

range : ℕ → ℕ → List ℕ
range lo zero    = []
range lo (suc n) = lo ∷ range (suc lo) n

length-range : ∀ lo n → length (range lo n) ≡ n
length-range lo zero    = refl
length-range lo (suc n) = cong suc (length-range (suc lo) n)

∈-range : ∀ lo n {x} → lo ≤ x → x < lo + n → x ∈ range lo n
∈-range lo zero    {x} lo≤x x<lo+0 =
  ⊥-elim (<-irrefl refl (≤-trans x<lo+0 (≤-trans (≤-reflexive (+-comm lo 0)) lo≤x)))
∈-range lo (suc n) {x} lo≤x x<lo+n with lo Data.Nat.Properties.≟ x
... | Relation.Nullary.yes refl = here refl
... | Relation.Nullary.no lo≢x =
  there (∈-range (suc lo) n (≤∧≢⇒< lo≤x lo≢x)
          (≤-trans x<lo+n (≤-reflexive (+-suc lo n))))

-- all pairs

pairs : {A B : Set} → List A → List B → List (A × B)
pairs xs ys = concatMap (λ x → map (x ,_) ys) xs

length-pairs : {A B : Set} (xs : List A) (ys : List B)
             → length (pairs xs ys) ≡ length xs * length ys
length-pairs []       ys = refl
length-pairs (x ∷ xs) ys =
  trans (length-++ (map (x ,_) ys))
        (cong₂ _+_ (length-map (x ,_) ys) (length-pairs xs ys))

any-pairs : {A B : Set} {P : A → Set} {Q : B → Set} {xs : List A} {ys : List B}
          → Any P xs → Any Q ys
          → Any (λ { (x , y) → P x × Q y }) (pairs xs ys)
any-pairs {xs = x ∷ xs} {ys} (here px) qy = ++⁺ˡ (go qy)
  where
  go : ∀ {ys} → Any _ ys → Any _ (map (x ,_) ys)
  go (here qy)  = here (px , qy)
  go (there qs) = there (go qs)
any-pairs {xs = x ∷ xs} {ys} (there ps) qy =
  ++⁺ʳ (map (x ,_) ys) (any-pairs ps qy)

-- all sublists

subsets : List ℕ → List (List ℕ)
subsets []       = [] ∷ []
subsets (x ∷ xs) = map (x ∷_) (subsets xs) ++ subsets xs

length-subsets : ∀ xs → length (subsets xs) ≡ 2 ^ length xs
length-subsets []       = refl
length-subsets (x ∷ xs) =
  trans (length-++ (map (x ∷_) (subsets xs)))
  (trans (cong (_+ length (subsets xs)) (length-map (x ∷_) (subsets xs)))
  (trans (cong (λ m → m + m) (length-subsets xs))
         (cong (2 ^ length xs +_) (sym (+-identityʳ _)))))

------------------------------------------------------------------------
-- Finite sets of states: strictly increasing lists

Increasing : List ℕ → Set
Increasing = AllPairs _<_

-- a strictly increasing list within `lo … lo + n - 1` is a sublist of
-- the range

∈-subsets : ∀ lo n {S} → Increasing S → All (lo ≤_) S → All (_< lo + n) S
          → S ∈ subsets (range lo n)
∈-subsets lo zero    {[]}    _ _ _ = here refl
∈-subsets lo zero    {x ∷ S} _ (lo≤x ∷ _) (x<lo+0 ∷ _) =
  ⊥-elim (<-irrefl refl (≤-trans x<lo+0 (≤-trans (≤-reflexive (+-comm lo 0)) lo≤x)))
∈-subsets lo (suc n) {[]}    _ _ _ =
  ∈-++⁺ʳ (map (lo ∷_) (subsets (range (suc lo) n))) (∈-subsets (suc lo) n [] [] [])
∈-subsets lo (suc n) {x ∷ S} (x<S ∷ incS) (lo≤x ∷ loS) (x< ∷ S<) with lo Data.Nat.Properties.≟ x
... | Relation.Nullary.yes refl =
  ∈-++⁺ˡ (∈-map⁺ (lo ∷_)
    (∈-subsets (suc lo) n incS x<S (All.map (λ lt → ≤-trans lt (≤-reflexive (+-suc lo n))) S<)))
... | Relation.Nullary.no lo≢x =
  ∈-++⁺ʳ (map (lo ∷_) (subsets (range (suc lo) n)))
    (∈-subsets (suc lo) n (x<S ∷ incS)
      (≤∧≢⇒< lo≤x lo≢x ∷ All.map (λ x<y → <-trans (≤∧≢⇒< lo≤x lo≢x) x<y) x<S)
      (All.map (λ lt → ≤-trans lt (≤-reflexive (+-suc lo n))) (x< ∷ S<)))

-- insertion

∈-insert⁻ : ∀ n S {x} → x ∈ insert n S → x ≡ n ⊎ x ∈ S
∈-insert⁻ n []       (here x≡n) = inj₁ x≡n
∈-insert⁻ n (m ∷ ms) x∈ with n ≡ᵇ m | n <ᵇ m
∈-insert⁻ n (m ∷ ms) x∈          | true  | _     = inj₂ x∈
∈-insert⁻ n (m ∷ ms) (here x≡n)  | false | true  = inj₁ x≡n
∈-insert⁻ n (m ∷ ms) (there x∈)  | false | true  = inj₂ x∈
∈-insert⁻ n (m ∷ ms) (here x≡m)  | false | false = inj₂ (here x≡m)
∈-insert⁻ n (m ∷ ms) (there x∈)  | false | false with ∈-insert⁻ n ms x∈
... | inj₁ x≡n = inj₁ x≡n
... | inj₂ x∈ms = inj₂ (there x∈ms)

∈-insert⁺ˡ : ∀ n S → n ∈ insert n S
∈-insert⁺ˡ n []       = here refl
∈-insert⁺ˡ n (m ∷ ms) with n ≡ᵇ m in e | n <ᵇ m
... | true  | _     = here (≡ᵇ-true e)
... | false | true  = here refl
... | false | false = there (∈-insert⁺ˡ n ms)

∈-insert⁺ʳ : ∀ n S {x} → x ∈ S → x ∈ insert n S
∈-insert⁺ʳ n (m ∷ ms) x∈ with n ≡ᵇ m | n <ᵇ m
∈-insert⁺ʳ n (m ∷ ms) x∈          | true  | _     = x∈
∈-insert⁺ʳ n (m ∷ ms) x∈          | false | true  = there x∈
∈-insert⁺ʳ n (m ∷ ms) (here x≡m)  | false | false = here x≡m
∈-insert⁺ʳ n (m ∷ ms) (there x∈)  | false | false = there (∈-insert⁺ʳ n ms x∈)

-- membership decides `All`

all-∈ : ∀ {P : ℕ → Set} S → (∀ {x} → x ∈ S → P x) → All P S
all-∈ []      f = []
all-∈ (x ∷ S) f = f (here refl) ∷ all-∈ S (λ x∈ → f (there x∈))

∈-all : ∀ {P : ℕ → Set} {S x} → All P S → x ∈ S → P x
∈-all (px ∷ _)  (here refl) = px
∈-all (_ ∷ pxs) (there x∈)  = ∈-all pxs x∈

insert-all : ∀ {P : ℕ → Set} n S → P n → All P S → All P (insert n S)
insert-all {P} n S pn pS = all-∈ (insert n S) λ x∈ → [ (λ { refl → pn }) , ∈-all pS ]′ (∈-insert⁻ n S x∈)
  where open import Data.Sum.Base using ([_,_]′)

insert-increasing : ∀ n S → Increasing S → Increasing (insert n S)
insert-increasing n []       [] = [] ∷ []
insert-increasing n (m ∷ ms) (m<ms ∷ inc) with n ≡ᵇ m in e₁ | n <ᵇ m in e₂
... | true  | _     = m<ms ∷ inc
... | false | true  = (n<m ∷ All.map (<-trans n<m) m<ms) ∷ m<ms ∷ inc
  where n<m = <ᵇ⇒< n _ (T-true e₂)
... | false | false = insert-all n ms m<n m<ms ∷ insert-increasing n ms inc
  where m<n = ≤∧≢⇒< (≮⇒≥ (λ n<m → T-false e₂ (Data.Nat.Properties.<⇒<ᵇ n<m)))
                    (λ m≡n → ≡ᵇ-false e₁ (sym m≡n))

-- the set of a list

∈-fromList⁻ : ∀ xs {x} → x ∈ fromList xs → x ∈ xs
∈-fromList⁻ (y ∷ ys) x∈ with ∈-insert⁻ y (fromList ys) x∈
... | inj₁ refl = here refl
... | inj₂ x∈′  = there (∈-fromList⁻ ys x∈′)

∈-fromList⁺ : ∀ xs {x} → x ∈ xs → x ∈ fromList xs
∈-fromList⁺ (y ∷ ys) (here refl) = ∈-insert⁺ˡ y (fromList ys)
∈-fromList⁺ (y ∷ ys) (there x∈)  = ∈-insert⁺ʳ y (fromList ys) (∈-fromList⁺ ys x∈)

fromList-increasing : ∀ xs → Increasing (fromList xs)
fromList-increasing []       = []
fromList-increasing (x ∷ xs) = insert-increasing x (fromList xs) (fromList-increasing xs)

fromList-all : ∀ {P : ℕ → Set} xs → All P xs → All P (fromList xs)
fromList-all xs pxs = all-∈ (fromList xs) λ x∈ → ∈-all pxs (∈-fromList⁻ xs x∈)

-- `Any` over a set and over its list

any-fromList⁻ : ∀ {P : ℕ → Set} xs → Any P (fromList xs) → Any P xs
any-fromList⁻ xs a with find a
... | x , x∈ , px = lose (∈-fromList⁻ xs x∈) px

any-fromList⁺ : ∀ {P : ℕ → Set} xs → Any P xs → Any P (fromList xs)
any-fromList⁺ xs a with find a
... | x , x∈ , px = lose (∈-fromList⁺ xs x∈) px

any-insert⁻ : ∀ {P : ℕ → Set} n S → Any P (insert n S) → P n ⊎ Any P S
any-insert⁻ n S a with find a
... | x , x∈ , px with ∈-insert⁻ n S x∈
...   | inj₁ refl = inj₁ px
...   | inj₂ x∈S  = inj₂ (lose x∈S px)

any-insert⁺ʳ : ∀ {P : ℕ → Set} n S → Any P S → Any P (insert n S)
any-insert⁺ʳ n S a with find a
... | x , x∈ , px = lose (∈-insert⁺ʳ n S x∈) px

any-insert⁺ˡ : ∀ {P : ℕ → Set} n S → P n → Any P (insert n S)
any-insert⁺ˡ n S pn = lose (∈-insert⁺ˡ n S) pn
