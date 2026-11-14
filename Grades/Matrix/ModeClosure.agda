------------------------------------------------------------------------
-- Closures of mode grades over a dioid with the trivial action.      --
--                                                                    --
-- Let the star on the entries be a Kleene star: above its argument,  --
-- closed under the product, and with a product between two stars     --
-- below the join of the products with one of them (`KleeneStars`).   --
-- Over the trivial action, the candidate `X` of `ModeGrade.Closures` --
-- at `k ≥ 4 + n` (powers up to `Aᵏ⁺¹`), `n` the number of modes the  --
-- matrix `A` names, satisfies `X · A ≾ X` (`Core.candidate-closedᴹ`, --
-- on matrices); with `k = bound = 4 + n` it is the closure of a      --
-- grade (`closure`). By the right induction law, `X · X ≾ X` follows --
-- from `X · A ≾ X`, a term of which is a walk with a star at one of  --
-- its modes. A walk of more than `k + 1` steps is below one through  --
-- the modes named, `stuck`, its two ends and two modes not named, as --
-- exchanging modes not named keeps the entries; by the pigeonhole    --
-- principle that walk has a cycle of at most `k + 1` steps,          --
-- below the star at its mode, and the product between the two stars  --
-- is below the join of two walks with one star each and fewer steps  --
-- (pumping).                                                         --
------------------------------------------------------------------------

open import Grades.Indexed using (Names)
open import Grades.Matrix.Dioid using (Dioid)
open import Grades.Matrix.Nominal using (Equivariant)

module Grades.Matrix.ModeClosure (𝒩 : Names) (S : Dioid) (Eq : Equivariant 𝒩 S) where

open Dioid S
open import Grades.Matrix.ModeGrade 𝒩 S Eq

------------------------------------------------------------------------
-- Kleene stars: a star above its argument, closed under the product,
-- and splitting a product between two stars

record KleeneStars (St : Stars) : Set where
  open Stars St
  field
    star-ext   : ∀ a → a ≤ star a
    star-idem  : ∀ a → star a ⊗ star a ≤ star a
    star-split : ∀ a b c → (star a ⊗ b) ⊗ star c ≤ (star a ⊗ b) ⊕ (b ⊗ star c)

------------------------------------------------------------------------
-- The closure, over the trivial action

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length; filter) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺)
import Data.List.Membership.DecPropositional as DecMembership
import Data.List.Membership.Propositional.Properties
open import Data.List.Properties using (++-assoc; length-++; length-map; ∷-injective; filter-notAll)
import Data.List.Relation.Unary.All.Properties as Allₚ
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)

open import Grades.Base using (Plus)
open import Grades.Matrix.Modes 𝒩
open import Grades.Matrix.Nominal 𝒩 using (Perm)
open Equivariant Eq
open import Grades.Matrix.Matrices 𝒩 S Eq

open import Util.Equality hiding (J)

private
  𝒫 : Preorder 0ℓ 0ℓ 0ℓ
  𝒫 = record
    { Carrier    = Carrier
    ; _≈_        = _≡_
    ; _≲_        = _≤_
    ; isPreorder = record { isEquivalence = isEquivalence ; reflexive = ≤-reflexive ; trans = ≤-trans } }

open import Relation.Binary.Reasoning.Preorder 𝒫

private
  assocˡ : ∀ a b c → (a ⊗ b) ⊗ c ≤ a ⊗ (b ⊗ c)
  assocˡ a b c = proj₁ (⊗-assoc a b c)

  assocʳ : ∀ a b c → a ⊗ (b ⊗ c) ≤ (a ⊗ b) ⊗ c
  assocʳ a b c = proj₂ (⊗-assoc a b c)

  monoˡ : ∀ {a a'} b → a ≤ a' → a ⊗ b ≤ a' ⊗ b
  monoˡ b p = ⊗-mono p ≤-refl

  monoʳ : ∀ a {b b'} → b ≤ b' → a ⊗ b ≤ a ⊗ b'
  monoʳ a p = ⊗-mono ≤-refl p

  -- a product between two factors distributes over a join
  distrib₂ : ∀ c₁ a b c₂ → c₁ ⊗ ((a ⊕ b) ⊗ c₂) ≤ (c₁ ⊗ (a ⊗ c₂)) ⊕ (c₁ ⊗ (b ⊗ c₂))
  distrib₂ c₁ a b c₂ = ≤-trans (monoʳ c₁ (⊗-distribʳ c₂ a b)) (⊗-distribˡ c₁ _ _)

  zero₂ : ∀ c₁ c₂ {t} → c₁ ⊗ (𝟘 ⊗ c₂) ≤ t
  zero₂ c₁ c₂ = ≤-trans (≤-trans (monoʳ c₁ (⊗-zeroˡ c₂)) (⊗-zeroʳ c₁)) (𝟘-≤ _)

  -- the names of a mode
  names : Mode → List Name
  names stuck   = []
  names ⌜ n ⌝ = n ∷ []

-- the star from closures is above its argument and closed under the
-- product

module _ (pl : (a : Carrier) → Plus _⊗_ _≤_ a) where

  private
    star = Stars.star (stars-from pl)

  stars-from-ext : ∀ a → a ≤ star a
  stars-from-ext a = ≤-trans (Plus.≾-c⁺ (pl a)) (⊕-ubʳ 𝟙 _)

  stars-from-idem : ∀ a → star a ⊗ star a ≤ star a
  stars-from-idem a =
    ≤-trans (⊗-distribʳ (𝟙 ⊕ p) 𝟙 p)
      (⊕-lub (proj₁ (⊗-identityˡ _))
             (≤-trans (⊗-distribˡ p 𝟙 p)
               (≤-trans (⊕-lub (proj₁ (⊗-identityʳ p)) (Plus.c⁺-iter (pl a))) (⊕-ubʳ 𝟙 p))))
    where p = Plus.c⁺ (pl a)

-- The joins of the powers of a matrix, and the candidate closure, on
-- matrices

module Candidates (St : Stars) where

  open StarMatrices St

  powersᴹ : Matrix → ℕ → Matrix
  powersᴹ M zero    = M
  powersᴹ M (suc j) = M ⊕ᴹ (M ⊗ᴹ powersᴹ M j)

  candidateᴹ : ℕ → Matrix → Matrix
  candidateᴹ k M = ((Iᴹ ⊕ᴹ powersᴹ M k) ⊗ᴹ starsᴹ (powersᴹ M k)) ⊗ᴹ powersᴹ M k

-- those of a grade are those of its matrix

module _ (E : ModeEntries) (St : Stars) where

  open Closures E St
  open Candidates St

  powers-mat : ∀ A j → mat (powers A j) ≡ powersᴹ (mat A) j
  powers-mat A zero    = refl
  powers-mat A (suc j) = cong (λ P → mat A ⊕ᴹ (mat A ⊗ᴹ P)) (powers-mat A j)

  candidate-mat : ∀ k A → mat (candidate k A) ≡ candidateᴹ k (mat A)
  candidate-mat k A = cong (λ P → ((Iᴹ ⊕ᴹ P) ⊗ᴹ starsᴹ P) ⊗ᴹ P) (powers-mat A k)

-- The candidate is closed under the product, for a Kleene star over the
-- trivial action

module Core (St : Stars) (K : KleeneStars St)
            (act-trivial : ∀ a b x → act a b x ≈ x) where

  open Stars St
  open KleeneStars K
  open StarMatrices St
  open Candidates St

  private
    -- under the trivial action, a permutation acts below the identity
    actᴾ-≤ : ∀ π x → actᴾ π x ≤ x
    actᴾ-≤ []            x = ≤-refl
    actᴾ-≤ ((a , b) ∷ π) x = ≤-trans (proj₁ (act-trivial a b _)) (actᴾ-≤ π x)

    ⨁₂ : ∀ {c₁ c₂ t} ts → (∀ {a} → a ∈ ts → c₁ ⊗ (a ⊗ c₂) ≤ t) → c₁ ⊗ (⨁ ts ⊗ c₂) ≤ t
    ⨁₂ {c₁} {c₂} []       f = zero₂ c₁ c₂
    ⨁₂ {c₁} {c₂} (a ∷ ts) f =
      ≤-trans (distrib₂ c₁ a (⨁ ts) c₂) (⊕-lub (f (here refl)) (⨁₂ ts (λ p → f (there p))))

    -- the entries of a product below a bound in any context
    prod-lub₂ : ∀ M N x y {c₁ c₂ t}
              → (∀ q → c₁ ⊗ ((entry M x q ⊗ entry N q y) ⊗ c₂) ≤ t)
              → c₁ ⊗ (entry (M ⊗ᴹ N) x y ⊗ c₂) ≤ t
    prod-lub₂ M N ⌜ p ⌝ y {c₁} {c₂} f =
      ≤-trans (monoʳ c₁ (monoˡ c₂ (orbit-lub (λ π _ → actᴾ-≤ π _))))
        (⨁₂ (P.terms ⌜ p ⌝ y) λ a∈ → case (∈-map⁻ (P.term ⌜ p ⌝ y) a∈))
      where
        module P = Product M N
        case : ∀ {a} → (∃ λ q → q ∈ P.candidates ⌜ p ⌝ y × a ≡ P.term ⌜ p ⌝ y q) → c₁ ⊗ (a ⊗ c₂) ≤ _
        case (q , _ , refl) = f q
    prod-lub₂ M N stuck stuck   {c₁} {c₂} f =
      ≤-trans (monoʳ c₁ (monoˡ c₂ (proj₂ (⊗-identityˡ 𝟙)))) (f stuck)
    prod-lub₂ M N stuck ⌜ _ ⌝ {c₁} {c₂} f = zero₂ c₁ c₂

    join-lub₂ : ∀ M N x y {c₁ c₂ t}
              → c₁ ⊗ (entry M x y ⊗ c₂) ≤ t → c₁ ⊗ (entry N x y ⊗ c₂) ≤ t
              → c₁ ⊗ (entry (M ⊕ᴹ N) x y ⊗ c₂) ≤ t
    join-lub₂ M N x y {c₁} {c₂} f g =
      ≤-trans (monoʳ c₁ (monoˡ c₂ (proj₁ (⊕ᴹ-entry M N x y))))
        (≤-trans (distrib₂ c₁ _ _ c₂) (⊕-lub f g))

    -- regrouping a product of four
    regroup : ∀ c₁ a b c₂ → c₁ ⊗ ((a ⊗ b) ⊗ c₂) ≤ (c₁ ⊗ a) ⊗ (b ⊗ c₂)
    regroup c₁ a b c₂ =
      ≤-trans (monoʳ c₁ (assocˡ a b c₂)) (assocʳ c₁ a (b ⊗ c₂))

    regroup⁻ : ∀ c₁ a b c₂ → (c₁ ⊗ a) ⊗ (b ⊗ c₂) ≤ c₁ ⊗ ((a ⊗ b) ⊗ c₂)
    regroup⁻ c₁ a b c₂ =
      ≤-trans (assocˡ c₁ a (b ⊗ c₂)) (monoʳ c₁ (assocʳ a b c₂))

  -- at `k` at least four more than the number of modes the matrix
  -- names: for the named modes, `stuck`, the two ends of a walk and
  -- two further modes not named

  module _ (M : Matrix) (k : ℕ) (k≥ : 4 + length (modes M) ≤ⁿ k) where

    private
      F : List Name
      F = modes M

      e : Mode → Mode → Carrier
      e = entry M

      P : ℕ → Matrix
      P j = powersᴹ M j

      B J Sᴮ X : Matrix
      B  = P k
      J  = Iᴹ ⊕ᴹ B
      Sᴮ = starsᴹ B
      X  = candidateᴹ k M

      -- the star at a mode
      s : Mode → Carrier
      s m = entry Sᴮ m m

      ------------------------------------------------------------------
      -- Walks: a start mode and the modes visited after it

      w : Mode → List Mode → Carrier
      w x []       = 𝟙
      w x (y ∷ ys) = e x y ⊗ w y ys

      end : Mode → List Mode → Mode
      end x []       = x
      end x (y ∷ ys) = end y ys

      end-++ : ∀ x ys zs → end x (ys ++ zs) ≡ end (end x ys) zs
      end-++ x []       zs = refl
      end-++ x (y ∷ ys) zs = end-++ y ys zs

      end-snoc : ∀ x ys r → end x (ys ++ r ∷ []) ≡ r
      end-snoc x ys r = end-++ x ys (r ∷ [])

      w-++ : ∀ x ys zs → w x (ys ++ zs) ≈ w x ys ⊗ w (end x ys) zs
      w-++ x []       zs = ≈-sym (⊗-identityˡ _)
      w-++ x (y ∷ ys) zs =
        ≈-trans (⊗-cong ≈-refl (w-++ y ys zs)) (≈-sym (⊗-assoc (e x y) (w y ys) _))

      w-one : ∀ x y → w x (y ∷ []) ≈ e x y
      w-one x y = ⊗-identityʳ (e x y)

      ------------------------------------------------------------------
      -- Walks below the powers and the unit joined with them

      A≤P : ∀ j → M ≤ᵖ P j
      A≤P zero    x y = ≤-refl
      A≤P (suc j) x y = ⊕ᴹ-ubˡ M _ x y

      walk-P : ∀ j x ys → 1 ≤ⁿ length ys → length ys ≤ⁿ suc j → w x ys ≤ entry (P j) x (end x ys)
      walk-P j       x (y ∷ [])      _ _ = ≤-trans (proj₁ (w-one x y)) (A≤P j x y)
      walk-P (suc j) x (y ∷ y' ∷ ys) _ (s≤s l) =
        ≤-trans (monoʳ (e x y) (walk-P j y (y' ∷ ys) (s≤s z≤n) l))
          (≤-trans (⊗ᴹ-ub M (P j) x _ y) (⊕ᴹ-ubʳ M (M ⊗ᴹ P j) x _))

      walk-J : ∀ x ys → length ys ≤ⁿ suc k → w x ys ≤ entry J x (end x ys)
      walk-J x []       _ = ≤-trans (≤-reflexive (sym (Iᴹ-diag x))) (⊕ᴹ-ubˡ Iᴹ B x x)
      walk-J x (y ∷ ys) l = ≤-trans (walk-P k x (y ∷ ys) (s≤s z≤n) l) (⊕ᴹ-ubʳ Iᴹ B x _)

      -- a term of the candidate
      corner : ∀ x m y {a b} → a ≤ entry J x m → b ≤ entry B m y → (a ⊗ s m) ⊗ b ≤ entry X x y
      corner x m y a≤ b≤ =
        ≤-trans (⊗-mono (≤-trans (monoˡ (s m) a≤) (⊗ᴹ-ub J Sᴮ x m m)) b≤)
          (⊗ᴹ-ub (J ⊗ᴹ Sᴮ) B x y m)

      ------------------------------------------------------------------
      -- The stars at the modes

      s-star : ∀ p → s ⌜ p ⌝ ≡ star (entry B ⌜ p ⌝ ⌜ p ⌝)
      s-star p with ⌜ p ⌝ ≟ᴹ ⌜ p ⌝
      ... | yes _ = refl
      ... | no ne = ⊥-elim (ne refl)

      S-off : ∀ {m' m} → ¬ m' ≡ m → entry Sᴮ m' m ≤ 𝟘
      S-off {stuck}   {stuck}   ne = ⊥-elim (ne refl)
      S-off {stuck}   {⌜ _ ⌝} ne = ≤-refl
      S-off {⌜ p ⌝} {m}       ne with m ≟ᴹ ⌜ p ⌝
      ... | yes e' = ⊥-elim (ne (sym e'))
      ... | no _   = ≤-refl

      s-unit : ∀ m → 𝟙 ≤ s m
      s-unit stuck   = ≤-refl
      s-unit ⌜ p ⌝ = ≤-trans (star-unit _) (≤-reflexive (sym (s-star p)))

      s-idem : ∀ m → s m ⊗ s m ≤ s m
      s-idem stuck   = proj₁ (⊗-identityˡ 𝟙)
      s-idem ⌜ p ⌝ rewrite s-star p = star-idem _

      s-split : ∀ m r b → (s m ⊗ b) ⊗ s r ≤ (s m ⊗ b) ⊕ (b ⊗ s r)
      s-split m stuck b = ≤-trans (proj₁ (⊗-identityʳ _)) (⊕-ubˡ _ _)
      s-split stuck ⌜ q ⌝ b = ≤-trans (monoˡ (s ⌜ q ⌝) (proj₁ (⊗-identityˡ b))) (⊕-ubʳ _ _)
      s-split ⌜ p ⌝ ⌜ q ⌝ b rewrite s-star p | s-star q = star-split _ b _

      -- a star is below the unit joined with itself followed by its argument
      s-unfold : ∀ m → s m ≤ 𝟙 ⊕ (s m ⊗ entry B m m)
      s-unfold stuck   = ⊕-ubˡ 𝟙 _
      s-unfold ⌜ p ⌝ rewrite s-star p = unfold (entry B ⌜ p ⌝ ⌜ p ⌝)
        where
          unfold : ∀ b → star b ≤ 𝟙 ⊕ (star b ⊗ b)
          unfold b = star-least {b} {star b ⊗ b}
            (≤-trans (proj₂ (⊗-identityˡ b)) (monoˡ b (star-unit b)))
            (≤-trans (assocˡ (star b) b (star b ⊗ b))
              (≤-trans (monoʳ (star b) (assocʳ b (star b) b))
                (≤-trans (monoʳ (star b) (monoˡ b (≤-trans (monoˡ (star b) (star-ext b)) (star-idem b))))
                  (≤-trans (assocʳ (star b) (star b) b) (monoˡ b (star-idem b))))))

      -- walks from `stuck` stay below the unit
      w-stuck : ∀ ys → w stuck ys ≤ 𝟙
      w-stuck []            = ≤-refl
      w-stuck (stuck ∷ ys)   = ≤-trans (proj₁ (⊗-identityˡ _)) (w-stuck ys)
      w-stuck (⌜ _ ⌝ ∷ ys) = ≤-trans (⊗-zeroˡ _) (𝟘-≤ _)

      -- a short cycle is below the star at its mode
      cycle-s : ∀ r cs → end r cs ≡ r → 1 ≤ⁿ length cs → length cs ≤ⁿ suc k → w r cs ≤ s r
      cycle-s stuck   cs _ _ _ = w-stuck cs
      cycle-s ⌜ p ⌝ cs eq l₁ l₂ =
        ≤-trans (walk-P k ⌜ p ⌝ cs l₁ l₂)
          (≤-trans (≤-reflexive (cong (entry B ⌜ p ⌝) eq))
            (≤-trans (star-ext _) (≤-reflexive (sym (s-star p)))))

      ------------------------------------------------------------------
      -- The powers and the unit joined with them below a bound, from
      -- their walks

      lub-P : ∀ j x y {c₁ c₂ t}
            → (∀ ys → end x ys ≡ y → length ys ≤ⁿ suc j → c₁ ⊗ (w x ys ⊗ c₂) ≤ t)
            → c₁ ⊗ (entry (P j) x y ⊗ c₂) ≤ t
      lub-P zero x y {c₁} {c₂} f =
        ≤-trans (monoʳ c₁ (monoˡ c₂ (proj₂ (w-one x y)))) (f (y ∷ []) refl (s≤s z≤n))
      lub-P (suc j) x y {c₁} {c₂} f =
        join-lub₂ M (M ⊗ᴹ P j) x y
          (≤-trans (monoʳ c₁ (monoˡ c₂ (proj₂ (w-one x y)))) (f (y ∷ []) refl (s≤s z≤n)))
          (prod-lub₂ M (P j) x y λ q →
            ≤-trans (regroup c₁ (e x q) _ c₂)
              (lub-P j q y λ ys eq l →
                ≤-trans (regroup⁻ c₁ (e x q) _ c₂) (f (q ∷ ys) eq (s≤s l))))

      lub-J : ∀ x y {c₁ c₂ t}
            → (∀ ys → end x ys ≡ y → length ys ≤ⁿ suc k → c₁ ⊗ (w x ys ⊗ c₂) ≤ t)
            → c₁ ⊗ (entry J x y ⊗ c₂) ≤ t
      lub-J x y {c₁} {c₂} f = join-lub₂ Iᴹ B x y unit (lub-P k x y f)
        where
          unit : c₁ ⊗ (entry Iᴹ x y ⊗ c₂) ≤ _
          unit with x ≟ᴹ y
          ... | yes refl = ≤-trans (≤-reflexive (cong (λ c → c₁ ⊗ (c ⊗ c₂)) (Iᴹ-diag x))) (f [] refl z≤n)
          ... | no ne    = ≤-trans (monoʳ c₁ (monoˡ c₂ (≤-reflexive (Iᴹ-off ne)))) (zero₂ c₁ c₂)

      ------------------------------------------------------------------
      -- Exchanging two modes not named keeps the weights of walks

      swapᴹ-fix : ∀ {a b x} → ¬ x ≡ ⌜ a ⌝ → ¬ x ≡ ⌜ b ⌝ → swapᴹ a b x ≡ x
      swapᴹ-fix {x = stuck}   _  _  = refl
      swapᴹ-fix {x = ⌜ n ⌝} na nb = cong ⌜_⌝ (swap-fix (λ e' → na (cong ⌜_⌝ e')) (λ e' → nb (cong ⌜_⌝ e')))

      w-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ x ys
             → w x ys ≤ w (swapᴹ a b x) (mapᴸ (swapᴹ a b) ys)
      w-swap a∉ b∉ x []       = ≤-refl
      w-swap {a} {b} a∉ b∉ x (y ∷ ys) =
        ⊗-mono (≤-trans (proj₂ (act-trivial a b _)) (proj₂ (entry-equivariant M a∉ b∉ x y)))
               (w-swap a∉ b∉ y ys)

      end-swap : ∀ a b x ys → end (swapᴹ a b x) (mapᴸ (swapᴹ a b) ys) ≡ swapᴹ a b (end x ys)
      end-swap a b x []       = refl
      end-swap a b x (y ∷ ys) = end-swap a b y ys

    ----------------------------------------------------------------------
    -- Folding a walk onto a finite set `L` of modes holding the modes
    -- named, `stuck`, the end `z`, and two modes `c₀` and `c₁` not
    -- named: a mode outside `L` is exchanged, with the rest of the
    -- walk, for one of `c₀` and `c₁`, which keeps the weight

    private
      module Fold (L : List Mode) (z : Mode) (c₀ c₁ : Name)
                  (stuck∈ : stuck ∈ L) (F∈ : ∀ {n} → n ∈ F → ⌜ n ⌝ ∈ L) (z∈ : z ∈ L)
                  (c₀∈ : ⌜ c₀ ⌝ ∈ L) (c₁∈ : ⌜ c₁ ⌝ ∈ L) (c₀∉ : c₀ ∉ F) (c₁∉ : c₁ ∉ F)
                  (c₀≢c₁ : ¬ c₀ ≡ c₁) (z≢c₀ : ¬ z ≡ ⌜ c₀ ⌝) (z≢c₁ : ¬ z ≡ ⌜ c₁ ⌝) where

        open DecMembership _≟ᴹ_ using () renaming (_∈?_ to _∈ᴹ?_)

        -- a mode of `L` not named, other than `y` and `z`
        pick : ∀ y → ∃ λ c → ⌜ c ⌝ ∈ L × c ∉ F × ¬ y ≡ ⌜ c ⌝ × ¬ z ≡ ⌜ c ⌝
        pick y with y ≟ᴹ ⌜ c₀ ⌝
        ... | yes refl = c₁ , c₁∈ , c₁∉ , (λ e' → c₀≢c₁ (⌜⌝-injective e')) , z≢c₁
        ... | no ne    = c₀ , c₀∈ , c₀∉ , ne , z≢c₀

        fold : ∀ n y ys → length ys ≡ n → y ∈ L → end y ys ≡ z
             → ∃ λ ys' → length ys' ≡ length ys × end y ys' ≡ z × All (_∈ L) ys' × w y ys ≤ w y ys'
        fold zero    y []        _ _  en = [] , refl , en , [] , ≤-refl
        fold (suc n) y (y' ∷ ys) l y∈ en with y' ∈ᴹ? L
        ... | yes y'∈ =
          let (zs , l' , en' , al , le) = fold n y' ys (ℕₚ.suc-injective l) y'∈ en
          in y' ∷ zs , cong suc l' , en' , y'∈ ∷ al , monoʳ (e y y') le
        fold (suc n) y (stuck ∷ ys) l y∈ en | no y'∉ = ⊥-elim (y'∉ stuck∈)
        fold (suc n) y (⌜ m ⌝ ∷ ys) l y∈ en | no y'∉ =
          let (zs , l' , en' , al , le) =
                fold n ⌜ c ⌝ ys₂ (trans (length-map σ ys) (ℕₚ.suc-injective l)) c∈ en₂
          in ⌜ c ⌝ ∷ zs , cong suc (trans l' (length-map σ ys)) , en' , c∈ ∷ al ,
             ≤-trans (w-swap m∉ c∉ y (⌜ m ⌝ ∷ ys))
               (≤-trans (≤-reflexive (cong₂ (λ y₀ m₀ → e y₀ m₀ ⊗ w m₀ ys₂) σy σm)) (monoʳ (e y ⌜ c ⌝) le))
          where
            c   = proj₁ (pick y)
            c∈  = proj₁ (proj₂ (pick y))
            c∉  = proj₁ (proj₂ (proj₂ (pick y)))
            y≢c = proj₁ (proj₂ (proj₂ (proj₂ (pick y))))
            z≢c = proj₂ (proj₂ (proj₂ (proj₂ (pick y))))
            σ   = swapᴹ m c
            ys₂ = mapᴸ σ ys
            m∉ : m ∉ F
            m∉ m∈ = y'∉ (F∈ m∈)
            σy : σ y ≡ y
            σy = swapᴹ-fix (λ { refl → y'∉ y∈ }) y≢c
            σm : σ ⌜ m ⌝ ≡ ⌜ c ⌝
            σm = cong ⌜_⌝ (swap-a m c)
            en₂ : end ⌜ c ⌝ ys₂ ≡ z
            en₂ = trans (cong (λ m₀ → end m₀ ys₂) (sym σm))
                    (trans (end-swap m c ⌜ m ⌝ ys)
                      (trans (cong σ en) (swapᴹ-fix (λ { refl → y'∉ z∈ }) z≢c)))

    ----------------------------------------------------------------------
    -- Pigeonhole: a list of elements of `L`, longer than `L`, has an
    -- element repeated at most `length L` places apart

    private
      Rep : List Mode → ℕ → Set
      Rep xs b = ∃ λ pre → ∃ λ r → ∃ λ mid → ∃ λ post →
                   (xs ≡ pre ++ r ∷ (mid ++ r ∷ post)) × length mid <ⁿ b

      -- the first occurrence of a mode
      first : ∀ y ys → All (λ z → ¬ z ≡ y) ys
                     ⊎ (∃ λ mid → ∃ λ post → (ys ≡ mid ++ y ∷ post) × All (λ z → ¬ z ≡ y) mid)
      first y []       = inj₁ []
      first y (z ∷ ys) with z ≟ᴹ y
      ... | yes refl = inj₂ ([] , ys , refl , [])
      ... | no ne with first y ys
      ...   | inj₁ al = inj₁ (ne ∷ al)
      ...   | inj₂ (mid , post , eq , al) = inj₂ (z ∷ mid , post , cong (z ∷_) eq , ne ∷ al)

      remove : Mode → List Mode → List Mode
      remove y = filter (λ z → ¬? (z ≟ᴹ y))

      remove-< : ∀ {y L} → y ∈ L → length (remove y L) <ⁿ length L
      remove-< {y} {L} y∈ = filter-notAll (λ z → ¬? (z ≟ᴹ y)) L (Any.map (λ { refl ne → ne refl }) y∈)

      remove-all : ∀ {y L} xs → All (_∈ L) xs → All (λ z → ¬ z ≡ y) xs → All (_∈ remove y L) xs
      remove-all []       []         []         = []
      remove-all (x ∷ xs) (x∈ ∷ al) (ne ∷ nes) = ∈-filter⁺ (λ z → ¬? (z ≟ᴹ _)) x∈ ne ∷ remove-all xs al nes

      rep : ∀ f L xs → length L ≤ⁿ f → All (_∈ L) xs → length L <ⁿ length xs → Rep xs (length L)
      rep f L (y ∷ ys) lf (y∈ ∷ al) lt with first y ys
      rep f L (y ∷ ys) lf (y∈ ∷ al) lt | inj₂ (mid , post , refl , nmid) with ℕₚ._<?_ (length mid) (length L)
      ... | yes short = [] , y , mid , post , refl , short
      ... | no long   = rec f lf
        where
          L' = remove y L
          rec : ∀ f → length L ≤ⁿ f → Rep (y ∷ (mid ++ y ∷ post)) (length L)
          rec zero    lf = ⊥-elim (ℕₚ.<-irrefl refl (ℕₚ.≤-trans (remove-< y∈) (ℕₚ.≤-trans lf z≤n)))
          rec (suc f) lf
            with rep f L' mid (ℕₚ.≤-pred (ℕₚ.≤-trans (remove-< y∈) lf))
                     (remove-all mid (Allₚ.++⁻ˡ mid al) nmid)
                     (ℕₚ.<-≤-trans (remove-< y∈) (ℕₚ.≮⇒≥ long))
          ... | pre , r , mid' , post' , refl , lm =
            y ∷ pre , r , mid' , post' ++ y ∷ post ,
            cong (y ∷_) (trans (++-assoc pre (r ∷ mid' ++ r ∷ post') (y ∷ post))
                          (cong (λ t → pre ++ r ∷ t) (++-assoc mid' (r ∷ post') (y ∷ post)))) ,
            ℕₚ.<-trans lm (remove-< y∈)
      rep f L (y ∷ ys) lf (y∈ ∷ al) lt | inj₁ nys = rec f lf
        where
          L' = remove y L
          rec : ∀ f → length L ≤ⁿ f → Rep (y ∷ ys) (length L)
          rec zero    lf = ⊥-elim (ℕₚ.<-irrefl refl (ℕₚ.≤-trans (remove-< y∈) (ℕₚ.≤-trans lf z≤n)))
          rec (suc f) lf
            with rep f L' ys (ℕₚ.≤-pred (ℕₚ.≤-trans (remove-< y∈) lf)) (remove-all ys al nys)
                     (ℕₚ.<-≤-trans (remove-< y∈) (ℕₚ.≤-pred lt))
          ... | pre , r , mid' , post' , eq , lm =
            y ∷ pre , r , mid' , post' , cong (y ∷_) eq , ℕₚ.<-trans lm (remove-< y∈)

    ----------------------------------------------------------------------
    -- A walk of at least `k + 1` steps is below a walk with the same
    -- ends and steps and a cycle of at most `k + 1` steps

    private
      record Cut (x : Mode) (ys : List Mode) : Set where
        field
          as cs ds : List Mode
          cyc    : end (end x as) cs ≡ end x as
          fin    : end (end x as) ds ≡ end x ys
          len    : length ys ≡ length as + (length cs + length ds)
          pos    : 1 ≤ⁿ length cs
          short  : length cs ≤ⁿ suc k
          weight : w x ys ≤ w x as ⊗ (w (end x as) cs ⊗ w (end x as) ds)

      len-snoc : ∀ (mid : List Mode) r → length (mid ++ r ∷ []) ≡ suc (length mid)
      len-snoc mid r = trans (length-++ mid) (ℕₚ.+-comm (length mid) 1)

      from-rep : ∀ x ys b → Rep (x ∷ ys) b
               → ∃ λ as → ∃ λ cs → ∃ λ ds → (ys ≡ as ++ (cs ++ ds)) × (end (end x as) cs ≡ end x as)
                                             × (1 ≤ⁿ length cs) × (length cs ≤ⁿ b)
      from-rep x ys b ([] , r , mid , post , refl , lm) =
        [] , mid ++ r ∷ [] , post , sym (++-assoc mid (r ∷ []) post) , end-snoc r mid r ,
        ℕₚ.≤-trans (s≤s z≤n) (ℕₚ.≤-reflexive (sym (len-snoc mid r))) ,
        ℕₚ.≤-trans (ℕₚ.≤-reflexive (len-snoc mid r)) lm
      from-rep x ys b (p ∷ pre , r , mid , post , refl , lm) =
        pre ++ r ∷ [] , mid ++ r ∷ [] , post ,
        sym (trans (++-assoc pre (r ∷ []) _) (cong (λ t → pre ++ r ∷ t) (++-assoc mid (r ∷ []) post))) ,
        trans (cong (λ t → end t (mid ++ r ∷ [])) ea) (trans (end-snoc r mid r) (sym ea)) ,
        ℕₚ.≤-trans (s≤s z≤n) (ℕₚ.≤-reflexive (sym (len-snoc mid r))) ,
        ℕₚ.≤-trans (ℕₚ.≤-reflexive (len-snoc mid r)) lm
        where ea = end-snoc p pre r

      -- the finite set a walk from `x` to `z` is folded onto
      module Onto (x z : Mode) where
        c₀ c₁ : Name
        c₀ = fresh (names x ++ names z ++ F)
        c₁ = fresh (c₀ ∷ names x ++ names z ++ F)

        L : List Mode
        L = stuck ∷ x ∷ z ∷ ⌜ c₀ ⌝ ∷ ⌜ c₁ ⌝ ∷ mapᴸ ⌜_⌝ F

        length-L : length L ≤ⁿ suc k
        length-L = ℕₚ.≤-trans (ℕₚ.≤-reflexive (cong (λ n → 5 + n) (length-map ⌜_⌝ F))) (s≤s k≥)

        private
          c₀∉ : c₀ ∉ names x ++ names z ++ F
          c₀∉ = fresh-∉ _

          c₁∉ : c₁ ∉ c₀ ∷ names x ++ names z ++ F
          c₁∉ = fresh-∉ _

          ∉F-lift : ∀ {c} → c ∈ F → c ∈ names x ++ names z ++ F
          ∉F-lift c∈ = Data.List.Membership.Propositional.Properties.∈-++⁺ʳ (names x)
                         (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ (names z) c∈)

          ∉z-lift : ∀ {c} → z ≡ ⌜ c ⌝ → c ∈ names z ++ F
          ∉z-lift refl = here refl

        open Fold L z c₀ c₁ (here refl) (λ n∈ → there (there (there (there (there (∈-map⁺ ⌜_⌝ n∈))))))
               (there (there (here refl))) (there (there (there (here refl))))
               (there (there (there (there (here refl)))))
               (λ c∈ → c₀∉ (∉F-lift c∈)) (λ c∈ → c₁∉ (there (∉F-lift c∈)))
               (λ e' → c₁∉ (here (sym e')))
               (λ e' → c₀∉ (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ (names x) (∉z-lift e')))
               (λ e' → c₁∉ (there (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ (names x) (∉z-lift e'))))
          public

      cut : ∀ x ys → suc k ≤ⁿ length ys → Cut x ys
      cut x ys l with Onto.fold x (end x ys) (length ys) x ys refl (there (here refl)) refl
      ... | ys' , l' , en' , al , le
        with from-rep x ys' _
               (rep (length (Onto.L x (end x ys))) (Onto.L x (end x ys)) (x ∷ ys') ℕₚ.≤-refl
                    (there (here refl) ∷ al)
                    (s≤s (ℕₚ.≤-trans (Onto.length-L x (end x ys))
                                     (ℕₚ.≤-trans l (ℕₚ.≤-reflexive (sym l'))))))
      ... | as , cs , ds , refl , cyc , p₁ , p₂ = record
        { as = as ; cs = cs ; ds = ds ; cyc = cyc
        ; fin = trans (sym (trans (end-++ x as (cs ++ ds))
                                  (trans (end-++ (end x as) cs ds) (cong (λ t → end t ds) cyc)))) en'
        ; len = trans (sym l') (trans (length-++ as) (cong (length as +_) (length-++ cs)))
        ; pos = p₁
        ; short = ℕₚ.≤-trans p₂ (Onto.length-L x (end x ys))
        ; weight = ≤-trans le
            (≤-trans (proj₁ (w-++ x as (cs ++ ds)))
              (monoʳ (w x as) (≤-trans (proj₁ (w-++ (end x as) cs ds))
                (monoʳ (w (end x as) cs) (≤-reflexive (cong (λ t → w t ds) cyc))))))
        }

    ----------------------------------------------------------------------
    -- Pumping: a walk with a star at one of its modes is below the
    -- candidate

    private
      -- lengths
      shrink : ∀ n c N → n + c ≤ⁿ suc N → 1 ≤ⁿ c → n ≤ⁿ N
      shrink n c N le c≥ =
        ℕₚ.≤-pred (ℕₚ.≤-trans (ℕₚ.≤-trans (ℕₚ.≤-reflexive (ℕₚ.+-comm 1 n)) (ℕₚ.+-monoʳ-≤ n c≥)) le)

      positive : ∀ c n → suc (suc k) ≤ⁿ c + n → c ≤ⁿ suc k → 1 ≤ⁿ n
      positive c zero    le c≤ =
        ⊥-elim (ℕₚ.<-irrefl refl (ℕₚ.≤-trans le (ℕₚ.≤-trans (ℕₚ.≤-reflexive (ℕₚ.+-identityʳ c)) c≤)))
      positive c (suc n) le c≤ = s≤s z≤n

      eq₁ : ∀ a c d v → (a + (d + v)) + c ≡ (a + (c + d)) + v
      eq₁ = solve-∀

      eq₂ : ∀ a c d v → ((a + d) + v) + c ≡ (a + (c + d)) + v
      eq₂ = solve-∀

      eq₃ : ∀ u a c d → (u + (a + d)) + c ≡ u + (a + (c + d))
      eq₃ = solve-∀

      eq₄ : ∀ u a c d → ((u + a) + d) + c ≡ u + (a + (c + d))
      eq₄ = solve-∀

      eq₅ : ∀ a c d → a + (c + d) ≡ c + (a + d)
      eq₅ = solve-∀

      -- products
      a4 : ∀ a b c d → ((a ⊗ b) ⊗ c) ⊗ d ≤ a ⊗ ((b ⊗ c) ⊗ d)
      a4 a b c d = ≤-trans (assocˡ (a ⊗ b) c d) (≤-trans (assocˡ a b (c ⊗ d)) (monoʳ a (assocʳ b c d)))

      a4⁻ : ∀ a b c d → a ⊗ ((b ⊗ c) ⊗ d) ≤ ((a ⊗ b) ⊗ c) ⊗ d
      a4⁻ a b c d = ≤-trans (monoʳ a (assocˡ b c d)) (≤-trans (assocʳ a b (c ⊗ d)) (assocʳ (a ⊗ b) c d))

      b4 : ∀ p q a c d → (p ⊗ q) ⊗ (a ⊗ (c ⊗ d)) ≤ p ⊗ (((q ⊗ a) ⊗ c) ⊗ d)
      b4 p q a c d =
        ≤-trans (assocˡ p q _) (monoʳ p (≤-trans (assocʳ q a (c ⊗ d)) (assocʳ (q ⊗ a) c d)))

      -- a walk with a star at the end of `us`
      One : Mode → List Mode → List Mode → Carrier
      One x us vs = (w x us ⊗ s (end x us)) ⊗ w (end x us) vs

      shape : ∀ {a a' m m'} vs → a ≤ a' → m ≡ m' → (a ⊗ s m) ⊗ w m vs ≤ (a' ⊗ s m') ⊗ w m' vs
      shape vs le refl = monoˡ _ (monoˡ _ le)

      Hyp : Mode → ℕ → Set
      Hyp x N = ∀ us vs y → length us + length vs ≤ⁿ N → 1 ≤ⁿ length us + length vs
              → end (end x us) vs ≡ y → One x us vs ≤ entry X x y

      -- a cycle in the walk before the star
      left : ∀ x N → Hyp x N → ∀ us vs y → length us + length vs ≤ⁿ suc N
           → suc (suc k) ≤ⁿ length us → end (end x us) vs ≡ y → One x us vs ≤ entry X x y
      left x N ih us vs y lN lu ey =
        ≤-trans (monoˡ wv (monoˡ (s m) (≤-trans weight (monoʳ wa (monoˡ wd (cycle-s r cs cyc pos short))))))
          (≤-trans (a4 wa (s r ⊗ wd) (s m) wv)
            (≤-trans (monoʳ wa (monoˡ wv (s-split r m wd)))
              (≤-trans (distrib₂ wa _ _ wv) (⊕-lub T₁ T₂))))
        where
          open Cut (cut x us (ℕₚ.≤-trans (ℕₚ.n≤1+n _) lu))
          m  = end x us
          r  = end x as
          wa = w x as
          wd = w r ds
          wv = w m vs
          a = length as ; c = length cs ; d = length ds ; v = length vs
          lN' : (a + (c + d)) + v ≤ⁿ suc N
          lN' = subst (λ n → n + v ≤ⁿ suc N) len lN
          ad : 1 ≤ⁿ a + d
          ad = positive c (a + d) (subst (suc (suc k) ≤ⁿ_) (trans len (eq₅ a c d)) lu) short
          T₁ : wa ⊗ ((s r ⊗ wd) ⊗ wv) ≤ entry X x y
          T₁ = ≤-trans (regroup wa (s r) wd wv)
                 (≤-trans (monoʳ (wa ⊗ s r)
                            (≤-trans (monoʳ wd (≤-reflexive (cong (λ t → w t vs) (sym fin))))
                                     (proj₂ (w-++ r ds vs))))
                   (ih as (ds ++ vs) y
                      (subst (_≤ⁿ N) (cong (a +_) (sym (length-++ ds)))
                             (shrink _ c N (subst (_≤ⁿ suc N) (sym (eq₁ a c d v)) lN') pos))
                      (subst (1 ≤ⁿ_) (cong (a +_) (sym (length-++ ds)))
                             (ℕₚ.≤-trans ad (ℕₚ.+-monoʳ-≤ a (ℕₚ.m≤m+n d v))))
                      (trans (end-++ r ds vs) (trans (cong (λ t → end t vs) fin) ey))))
          T₂ : wa ⊗ ((wd ⊗ s m) ⊗ wv) ≤ entry X x y
          T₂ = ≤-trans (a4⁻ wa wd (s m) wv)
                 (≤-trans (shape vs (proj₂ (w-++ x as ds)) (sym (trans (end-++ x as ds) fin)))
                   (ih (as ++ ds) vs y
                      (subst (λ n → n + v ≤ⁿ N) (sym (length-++ as))
                             (shrink _ c N (subst (_≤ⁿ suc N) (sym (eq₂ a c d v)) lN') pos))
                      (subst (λ n → 1 ≤ⁿ n + v) (sym (length-++ as)) (ℕₚ.≤-trans ad (ℕₚ.m≤m+n _ v)))
                      (trans (cong (λ t → end t vs) (trans (end-++ x as ds) fin)) ey)))

      -- a cycle in the walk after the star
      right : ∀ x N → Hyp x N → ∀ us vs y → length us + length vs ≤ⁿ suc N
            → suc (suc k) ≤ⁿ length vs → end (end x us) vs ≡ y → One x us vs ≤ entry X x y
      right x N ih us vs y lN lv ey =
        ≤-trans (monoʳ (wu ⊗ s m) (≤-trans weight (monoʳ wa (monoˡ wd (cycle-s r cs cyc pos short)))))
          (≤-trans (b4 wu (s m) wa (s r) wd)
            (≤-trans (monoʳ wu (monoˡ wd (s-split m r wa)))
              (≤-trans (distrib₂ wu _ _ wd) (⊕-lub T₁ T₂))))
        where
          m  = end x us
          open Cut (cut m vs (ℕₚ.≤-trans (ℕₚ.n≤1+n _) lv))
          r  = end m as
          wu = w x us
          wa = w m as
          wd = w r ds
          u = length us ; a = length as ; c = length cs ; d = length ds
          lN' : u + (a + (c + d)) ≤ⁿ suc N
          lN' = subst (λ n → u + n ≤ⁿ suc N) len lN
          ad : 1 ≤ⁿ a + d
          ad = positive c (a + d) (subst (suc (suc k) ≤ⁿ_) (trans len (eq₅ a c d)) lv) short
          T₁ : wu ⊗ ((s m ⊗ wa) ⊗ wd) ≤ entry X x y
          T₁ = ≤-trans (regroup wu (s m) wa wd)
                 (≤-trans (monoʳ (wu ⊗ s m) (proj₂ (w-++ m as ds)))
                   (ih us (as ++ ds) y
                      (subst (λ n → u + n ≤ⁿ N) (sym (length-++ as))
                             (shrink _ c N (subst (_≤ⁿ suc N) (sym (eq₃ u a c d)) lN') pos))
                      (subst (λ n → 1 ≤ⁿ u + n) (sym (length-++ as)) (ℕₚ.≤-trans ad (ℕₚ.m≤n+m _ u)))
                      (trans (end-++ m as ds) (trans fin ey))))
          T₂ : wu ⊗ ((wa ⊗ s r) ⊗ wd) ≤ entry X x y
          T₂ = ≤-trans (a4⁻ wu wa (s r) wd)
                 (≤-trans (shape ds (proj₂ (w-++ x us as)) (sym (end-++ x us as)))
                   (ih (us ++ as) ds y
                      (subst (λ n → n + d ≤ⁿ N) (sym (length-++ us))
                             (shrink _ c N (subst (_≤ⁿ suc N) (sym (eq₄ u a c d)) lN') pos))
                      (subst (λ n → 1 ≤ⁿ n + d) (sym (length-++ us))
                             (ℕₚ.≤-trans ad (ℕₚ.≤-trans (ℕₚ.m≤n+m (a + d) u) (ℕₚ.≤-reflexive (sym (ℕₚ.+-assoc u a d))))))
                      (trans (cong (λ t → end t ds) (end-++ x us as)) (trans fin ey))))

      pump : ∀ x N → Hyp x N
      pump x zero    us vs y lN p ey = ⊥-elim (ℕₚ.<-irrefl refl (ℕₚ.≤-trans p lN))
      pump x (suc N) us vs y lN p ey with suc k ℕₚ.<? length us
      ... | yes lu = left x N (pump x N) us vs y lN lu ey
      ... | no lu  = short-us vs lN p ey
        where
          lu' : length us ≤ⁿ suc k
          lu' = ℕₚ.≮⇒≥ lu

          short-us : ∀ vs {y} → length us + length vs ≤ⁿ suc N → 1 ≤ⁿ length us + length vs
                   → end (end x us) vs ≡ y → One x us vs ≤ entry X x y
          -- a star at the end: the walk, or the star followed by its argument
          short-us [] lN p refl =
            ≤-trans (proj₁ (⊗-identityʳ _))
              (≤-trans (monoʳ wu (s-unfold m))
                (≤-trans (⊗-distribˡ wu 𝟙 _) (⊕-lub U₁ U₂)))
            where
              m  = end x us
              wu = w x us
              U₁ : wu ⊗ 𝟙 ≤ entry X x m
              U₁ = ≤-trans (proj₁ (⊗-identityʳ wu))
                     (≤-trans (proj₂ (⊗-identityˡ wu))
                       (≤-trans (monoˡ wu (≤-trans (s-unit x) (proj₂ (⊗-identityˡ (s x)))))
                         (corner x x m (walk-J x [] z≤n)
                           (walk-P k x us (subst (1 ≤ⁿ_) (ℕₚ.+-identityʳ _) p) lu'))))
              U₂ : wu ⊗ (s m ⊗ entry B m m) ≤ entry X x m
              U₂ = ≤-trans (assocʳ wu (s m) _) (corner x m m (walk-J x us lu') ≤-refl)
          short-us (v ∷ vs) lN p ey with suc k ℕₚ.<? length (v ∷ vs)
          ... | yes lv = right x N (pump x N) us (v ∷ vs) _ lN lv ey
          ... | no lv  =
            ≤-trans (corner x (end x us) _ (walk-J x us lu') (walk-P k (end x us) (v ∷ vs) (s≤s z≤n) (ℕₚ.≮⇒≥ lv)))
              (≤-reflexive (cong (entry X x) ey))

    ----------------------------------------------------------------------
    -- The candidate followed by the grade is below the candidate, so
    -- that the candidate is closed under the product

    private
      pump′ : ∀ x us m vs y → end x us ≡ m → end m vs ≡ y → length us ≤ⁿ suc k → length vs ≤ⁿ suc (suc k)
            → 1 ≤ⁿ length vs → (w x us ⊗ s m) ⊗ w m vs ≤ entry X x y
      pump′ x us m vs y refl ey lu lv pv =
        pump x (suc k + suc (suc k)) us vs y (ℕₚ.+-mono-≤ lu lv) (ℕₚ.≤-trans pv (ℕₚ.m≤n+m _ _)) ey

      X·A : ∀ x y → entry (X ⊗ᴹ M) x y ≤ entry X x y
      X·A x y = ⊗ᴹ-lub X M x y λ q →
        ≤-trans (proj₂ (⊗-identityˡ _))
          (prod-lub₂ (J ⊗ᴹ Sᴮ) B x q λ m →
            ≤-trans (monoʳ 𝟙 (assocˡ _ _ _))
              (prod-lub₂ J Sᴮ x m λ m' → diag m' m q))
        where
          diag : ∀ m' m q → 𝟙 ⊗ ((entry J x m' ⊗ entry Sᴮ m' m) ⊗ (entry B m q ⊗ e q y)) ≤ entry X x y
          diag m' m q with m' ≟ᴹ m
          ... | no ne =
            ≤-trans (monoʳ 𝟙 (monoˡ _ (≤-trans (monoʳ _ (S-off ne)) (⊗-zeroʳ _))))
              (zero₂ 𝟙 _)
          ... | yes refl =
            ≤-trans (monoʳ 𝟙 (assocˡ (entry J x m) (s m) _))
              (lub-J x m λ us eu lu →
                ≤-trans (≤-trans (proj₁ (⊗-identityˡ _)) (assocʳ (w x us) (s m) _))
                  (lub-P k m q λ vs ev lv →
                    ≤-trans (monoʳ (w x us ⊗ s m)
                              (≤-trans (monoʳ (w m vs) (≤-trans (proj₂ (w-one q y))
                                                         (≤-reflexive (cong (λ t → w t (y ∷ [])) (sym ev)))))
                                       (proj₂ (w-++ m vs (y ∷ [])))))
                      (pump′ x us m (vs ++ y ∷ []) y eu (end-snoc m vs y) lu
                         (ℕₚ.≤-trans (ℕₚ.≤-reflexive (len-snoc vs y)) (s≤s lv))
                         (ℕₚ.≤-trans (s≤s z≤n) (ℕₚ.≤-reflexive (sym (len-snoc vs y)))))))

    candidate-closedᴹ : X ⊗ᴹ M ≤ᵖ X
    candidate-closedᴹ = X·A

------------------------------------------------------------------------
-- The closures of mode grades

module _ (E : ModeEntries) (St : Stars) (K : KleeneStars St)
         (act-trivial : ∀ a b x → act a b x ≈ x) where

  open Closures E St
  open Core St K act-trivial

  module _ (A : ModeMatrix E) where

    -- the index of the candidate: four more than the modes `A` names
    bound : ℕ
    bound = 4 + length (modes (mat A))

    candidate-iter : _≾ᵐ_ E (_·ᵐ_ E (candidate bound A) (candidate bound A)) (candidate bound A)
    candidate-iter =
      pointwise⇒≤ᴹ (candidate-indʳ bound A
        (subst (λ X → X ⊗ᴹ mat A ≤ᵖ X) (sym (candidate-mat E St bound A))
               (candidate-closedᴹ (mat A) bound ℕₚ.≤-refl)))
      where open Candidates St

    -- the closure of a grade

    closure : Plus (_·ᵐ_ E) (_≾ᵐ_ E) A
    closure = candidate-plus bound A candidate-iter
