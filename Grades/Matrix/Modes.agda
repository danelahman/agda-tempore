------------------------------------------------------------------------
-- Modes, and the exchange of two of them.                            --
--                                                                    --
-- The modes are the names of an infinite set together with the       --
-- absorbing mode `stuck`. `swap a b` exchanges the names `a` and `b` --
-- and fixes every other mode; for `a` and `b` outside a finite set   --
-- `F` of names it fixes `F`, and it is an involution. The            --
-- representatives of the pairs of modes over `F` are the pairs of    --
-- names in `F`, `stuck`, and two fresh names `o` and `o'`; every     --
-- pair not leaving `stuck` is carried to one of them by at most two  --
-- swaps of names outside `F` (`via-representatives`).                --
------------------------------------------------------------------------

open import Grades.Indexed using (Names)

module Grades.Matrix.Modes (𝒩 : Names) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
import Data.List.Membership.DecPropositional as DecMembership
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

open Names 𝒩 public using (Name; _≟ᴺ_; fresh; fresh-∉)
open DecMembership _≟ᴺ_ public using (_∈?_)

data Mode : Set where
  stuck : Mode
  ⌜_⌝   : Name → Mode

⌜⌝-injective : ∀ {a b} → ⌜ a ⌝ ≡ ⌜ b ⌝ → a ≡ b
⌜⌝-injective refl = refl

------------------------------------------------------------------------
-- Exchanging two names

swap : Name → Name → Name → Name
swap a b n with n ≟ᴺ a
... | yes _ = b
... | no _ with n ≟ᴺ b
...   | yes _ = a
...   | no _  = n

swap-a : ∀ a b → swap a b a ≡ b
swap-a a b with a ≟ᴺ a
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)

swap-b : ∀ a b → swap a b b ≡ a
swap-b a b with b ≟ᴺ a
... | yes e = e
... | no _ with b ≟ᴺ b
...   | yes _ = refl
...   | no ¬e = ⊥-elim (¬e refl)

swap-fix : ∀ {a b n} → ¬ n ≡ a → ¬ n ≡ b → swap a b n ≡ n
swap-fix {a} {b} {n} na nb with n ≟ᴺ a
... | yes e = ⊥-elim (na e)
... | no _ with n ≟ᴺ b
...   | yes e = ⊥-elim (nb e)
...   | no _  = refl

swap-inv : ∀ a b n → swap a b (swap a b n) ≡ n
swap-inv a b n with n ≟ᴺ a
... | yes refl = swap-b n b
... | no na with n ≟ᴺ b
...   | yes refl = swap-a a n
...   | no nb = swap-fix na nb

swap-injective : ∀ {a b n m} → swap a b n ≡ swap a b m → n ≡ m
swap-injective {a} {b} {n} {m} e =
  trans (sym (swap-inv a b n)) (trans (cong (swap a b) e) (swap-inv a b m))

-- names of a set the swap of two names outside it fixes

swap-∈ : ∀ {F a b n} → a ∉ F → b ∉ F → n ∈ F → swap a b n ≡ n
swap-∈ a∉ b∉ n∈ = swap-fix (λ { refl → a∉ n∈ }) (λ { refl → b∉ n∈ })

-- and it keeps the names outside it outside

swap-∉ : ∀ {F a b n} → a ∉ F → b ∉ F → n ∉ F → swap a b n ∉ F
swap-∉ {F} {a} {b} {n} a∉ b∉ n∉ with n ≟ᴺ a
... | yes _ = b∉
... | no _ with n ≟ᴺ b
...   | yes _ = a∉
...   | no _  = n∉

swap-∈⁻ : ∀ {F a b n} → a ∉ F → b ∉ F → swap a b n ∈ F → n ∈ F
swap-∈⁻ {F} {a} {b} {n} a∉ b∉ s∈ with n ∈? F
... | yes n∈ = n∈
... | no n∉  = ⊥-elim (swap-∉ a∉ b∉ n∉ s∈)

swapᴹ : Name → Name → Mode → Mode
swapᴹ a b stuck   = stuck
swapᴹ a b ⌜ n ⌝ = ⌜ swap a b n ⌝

swapᴹ-inv : ∀ a b x → swapᴹ a b (swapᴹ a b x) ≡ x
swapᴹ-inv a b stuck   = refl
swapᴹ-inv a b ⌜ n ⌝ = cong ⌜_⌝ (swap-inv a b n)

------------------------------------------------------------------------
-- Representatives over a finite set of names

module Representatives (F : List Name) where

  o o' : Name
  o  = fresh F
  o' = fresh (o ∷ F)

  o∉ : o ∉ F
  o∉ = fresh-∉ F

  o'∉ : o' ∉ F
  o'∉ p = fresh-∉ (o ∷ F) (there p)

  o≢o' : ¬ o ≡ o'
  o≢o' e = fresh-∉ (o ∷ F) (here (sym e))

  -- a property of pairs of modes, kept by the swaps of names outside
  -- `F`, holds of every pair not leaving `stuck` once it holds of the
  -- representatives

  via-representatives :
      (P : Mode → Mode → Set)
    → (∀ {a b x y} → a ∉ F → b ∉ F → P x y → P (swapᴹ a b x) (swapᴹ a b y))
    → (∀ {p q} → p ∈ F → q ∈ F → P ⌜ p ⌝ ⌜ q ⌝)
    → (∀ {p} → p ∈ F → P ⌜ p ⌝ ⌜ o ⌝)
    → (∀ {q} → q ∈ F → P ⌜ o ⌝ ⌜ q ⌝)
    → P ⌜ o ⌝ ⌜ o ⌝
    → P ⌜ o ⌝ ⌜ o' ⌝
    → (∀ {p} → p ∈ F → P ⌜ p ⌝ stuck)
    → P ⌜ o ⌝ stuck
    → ∀ p y → P ⌜ p ⌝ y
  via-representatives P sw yy yo oy oo oo' ys os p stuck with p ∈? F
  ... | yes p∈ = ys p∈
  ... | no p∉  = subst (λ n → P ⌜ n ⌝ stuck) (swap-a o p) (sw o∉ p∉ os)
  via-representatives P sw yy yo oy oo oo' ys os p ⌜ q ⌝ with p ∈? F | q ∈? F
  ... | yes p∈ | yes q∈ = yy p∈ q∈
  ... | yes p∈ | no q∉ =
    subst₂ (λ m n → P ⌜ m ⌝ ⌜ n ⌝) (swap-∈ o∉ q∉ p∈) (swap-a o q) (sw o∉ q∉ (yo p∈))
  ... | no p∉ | yes q∈ =
    subst₂ (λ m n → P ⌜ m ⌝ ⌜ n ⌝) (swap-a o p) (swap-∈ o∉ p∉ q∈) (sw o∉ p∉ (oy q∈))
  ... | no p∉ | no q∉ with p ≟ᴺ q
  ...   | yes refl = subst₂ (λ m n → P ⌜ m ⌝ ⌜ n ⌝) (swap-a o p) (swap-a o p) (sw o∉ p∉ oo)
  ...   | no p≢q =
    -- carry `(o , o')` to `(o , q')` and then to `(p , q)`, where
    -- `q' = swap o p q`, so that `swap o p q' = q`
    subst₂ (λ m n → P ⌜ m ⌝ ⌜ n ⌝) (swap-a o p) (swap-inv o p q)
      (sw o∉ p∉ (subst₂ (λ m n → P ⌜ m ⌝ ⌜ n ⌝) o-fixed (swap-a o' q')
                   (sw o'∉ q'∉ oo')))
    where
      q' = swap o p q
      q'∉ : q' ∉ F
      q'∉ = swap-∉ o∉ p∉ q∉
      q'≢o : ¬ q' ≡ o
      q'≢o e = p≢q (sym (trans (sym (swap-inv o p q)) (trans (cong (swap o p) e) (swap-a o p))))
      o-fixed : swap o' q' o ≡ o
      o-fixed = swap-fix (λ e → o≢o' e) (λ e → q'≢o (sym e))
