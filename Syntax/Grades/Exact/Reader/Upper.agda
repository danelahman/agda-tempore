------------------------------------------------------------------------
-- The upper reader: weights and bounds are upper ends.               --
--                                                                    --
-- A chain fits when the sum of the weights poured into it lies below --
-- the sum of the bounds of its stretches. Read on the pieces of an   --
-- exact run against closed bounds, an accepting run of the reader    --
-- builds a word of the bound that the run fits: every stretch of a   --
-- chain but the last is filled to its bound, the last takes the rest.--
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Exact.Reader.Upper
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; foldr; [_])
open import Data.List.Properties using (map-++)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Solver T using (solve; _⊜_; _⊕_)
open import Syntax.Durations.Intervals T
  using (Cut; Hi; fin; ∞; _⊑_; _⊑ʰ_; _⊑ʰ?_; ⁺; ⁻; 0⁺; _+ʰ_; ⊑⇒≤; ≤⇒⁺⊑⁺)
  renaming (_∣_ to _∣ᶜ_)

open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Pour T Op n code code-injective
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader T Op n code code-injective running

------------------------------------------------------------------------
-- Weights, bounds and the comparison

Pc Ph : Set
Pc = Piece Carrier
Ph = Piece Hi

sumʰ : List Hi → Hi
sumʰ = foldr _+ʰ_ (fin 0⁺)

Fitsᵁ : List Ph → List Hi → Set
Fitsᵁ pre cs = sumʰ (map proj₂ pre) ⊑ʰ sumʰ cs

Fitsᵁ? : ∀ pre cs → Dec (Fitsᵁ pre cs)
Fitsᵁ? pre cs = sumʰ (map proj₂ pre) ⊑ʰ? sumʰ cs

open Upper proj₁ Fitsᵁ public
open Upper.Decide proj₁ Fitsᵁ Fitsᵁ? public

-- the closed reading of a length

cl : Carrier → Hi
cl c = fin (c ∣ᶜ ⁺)

toHi : Pc → Ph
toHi (k , τ) = k , cl τ

clo : Letter Carrier → Letter Hi
clo = mapˡ cl
  where
    mapˡ : (Carrier → Hi) → Letter Carrier → Letter Hi
    mapˡ f (op o)   = op o
    mapˡ f (st S c) = st S (f c)

sum-cl : ∀ xs → sumʰ (map cl xs) ≡ cl (sumᴰ xs)
sum-cl []       = refl
sum-cl (x ∷ xs) rewrite sum-cl xs = refl

wts-toHi : ∀ ps → map proj₂ (map toHi ps) ≡ map cl (amts ps)
wts-toHi []       = refl
wts-toHi (p ∷ ps) = cong (_ ∷_) (wts-toHi ps)

sum-toHi : ∀ ps → sumʰ (map proj₂ (map toHi ps)) ≡ cl (sumᴰ (amts ps))
sum-toHi ps = trans (cong sumʰ (wts-toHi ps)) (sum-cl (amts ps))

private
  cl-⊑ : ∀ {a b} → cl a ⊑ʰ cl b → a ≤ᴰ b
  cl-⊑ = ⊑⇒≤

  ⊑-cl : ∀ {a b} → a ≤ᴰ b → cl a ⊑ʰ cl b
  ⊑-cl = ≤⇒⁺⊑⁺

fits⇒ : ∀ pre cs → Fitsᵁ (map toHi pre) (map cl cs) → sumᴰ (amts pre) ≤ᴰ sumᴰ cs
fits⇒ pre cs f =
  cl-⊑ (subst₂ _⊑ʰ_ (trans (cong sumʰ (wts-toHi pre)) (sum-cl (amts pre))) (sum-cl cs) f)

⇒fits : ∀ pre cs → sumᴰ (amts pre) ≤ᴰ sumᴰ cs → Fitsᵁ (map toHi pre) (map cl cs)
⇒fits pre cs r =
  subst₂ _⊑ʰ_ (sym (trans (cong sumʰ (wts-toHi pre)) (sum-cl (amts pre)))) (sym (sum-cl cs)) (⊑-cl r)

sumᴰ-∷ʳ : ∀ xs x → sumᴰ (xs ∷ʳ x) ≡ sumᴰ xs +ᴰ x
sumᴰ-∷ʳ []       x = trans (+ᴰ-identityʳ x) (sym (+ᴰ-identityˡ x))
sumᴰ-∷ʳ (y ∷ xs) x = trans (cong (y +ᴰ_) (sumᴰ-∷ʳ xs x)) (sym (+ᴰ-assoc y (sumᴰ xs) x))

map-∷ʳ : ∀ {A B : Set} (f : A → B) xs x → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
map-∷ʳ f xs x = map-++ f xs [ x ]

------------------------------------------------------------------------
-- Walking into a stretch of a given length

private
  variable
    a b q s : Carrier

  ≮⇒≥ : ¬ (a <ᴰ b) → b ≤ᴰ a
  ≮⇒≥ {a} {b} ¬p with b ≤ᴰ? a
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

data SView (S : OpSet) (s : Carrier) : Word → Set where
  vzero : s ≡ 0ᴰ → SView S s []
  vpos  : (e : D⁺) → ∣ e ∣⁺ ≡ s → SView S s (st e S ∷ [])

sview : ∀ S s → SView S s (stretch S s)
sview S s = case (0ᴰ <ᴰ? s)
  where
    case : (c : Dec (0ᴰ <ᴰ s)) → SView S s (stretch-of S s c)
    case (yes p) = vpos (pos⁺ s p) refl
    case (no ¬p) = vzero (≮0⇒≡0 ¬p)

private
  ≤0 : a ≤ᴰ 0ᴰ → a ≡ 0ᴰ
  ≤0 = ≤0⇒≡0

-- the stretch is done: the walk goes on past it

walk-past : ∀ {x y S} s → Pour x 0ᴰ y 0ᴰ → Pour x 0ᴰ (stretch S s ++ y) s
walk-past {x} {y} {S} s w = go (sview S s)
  where
    go : ∀ {z} → SView S s z → Pour x 0ᴰ (z ++ y) s
    go (vzero e)  = subst (Pour x 0ᴰ y) (sym e) w
    go (vpos e e′) = subst (Pour x 0ᴰ (st e S ∷ y)) e′ (nexty w)

-- an item poured to its end into the stretch

walk-pour : ∀ {i x y S ox oy} s q → Adm i S → ox +ᴰ q ≡ len i → oy +ᴰ q ≤ᴰ s
          → Pour x 0ᴰ (stretch S s ++ y) (oy +ᴰ q) → Pour (i ∷ x) ox (stretch S s ++ y) oy
walk-pour {i} {x} {y} {S} {ox} {oy} s q ad e r w = go (sview S s) w
  where
    go : ∀ {z} → SView S s z → Pour x 0ᴰ (z ++ y) (oy +ᴰ q) → Pour (i ∷ x) ox (z ++ y) oy
    go (vzero e₀) w′ =
      subst (λ u → Pour (i ∷ x) u y oy) (sym oxl)
        (nextx (subst (Pour x 0ᴰ y) (trans (cong (oy +ᴰ_) q0) (+ᴰ-identityʳ oy)) w′))
      where
        q0 : q ≡ 0ᴰ
        q0 = ≤0 (≤ᴰ-trans (≤ᴰ-+ˡ q oy) (subst (oy +ᴰ q ≤ᴰ_) e₀ r))
        oxl : ox ≡ len i
        oxl = trans (sym (+ᴰ-identityʳ ox)) (trans (cong (ox +ᴰ_) (sym q0)) e)
    go (vpos f ef) w′ =
      pour q ad (≤ᴰ-reflexive e) (subst (oy +ᴰ q ≤ᴰ_) (sym ef) r)
        (subst (λ u → Pour (i ∷ x) u (st f S ∷ y) (oy +ᴰ q)) (sym e) (nextx w′))

-- an item poured into the stretch until the stretch is full

walk-fill : ∀ {i x y S ox oy} s q → Adm i S → oy +ᴰ q ≡ s → ox +ᴰ q ≤ᴰ len i
          → Pour (i ∷ x) (ox +ᴰ q) y 0ᴰ → Pour (i ∷ x) ox (stretch S s ++ y) oy
walk-fill {i} {x} {y} {S} {ox} {oy} s q ad e r w = go (sview S s)
  where
    go : ∀ {z} → SView S s z → Pour (i ∷ x) ox (z ++ y) oy
    go (vzero e₀) =
      subst (Pour (i ∷ x) ox y) oy0
        (subst (λ u → Pour (i ∷ x) u y 0ᴰ) (trans (cong (ox +ᴰ_) q0) (+ᴰ-identityʳ ox)) w)
      where
        q0 : q ≡ 0ᴰ
        q0 = ≤0 (≤ᴰ-trans (≤ᴰ-+ˡ q oy) (≤ᴰ-reflexive (trans e e₀)))
        oy0 : 0ᴰ ≡ oy
        oy0 = sym (≤0 (≤ᴰ-trans (≤ᴰ-+ oy q) (≤ᴰ-reflexive (trans e e₀))))
    go (vpos f ef) =
      pour q ad r (≤ᴰ-reflexive (trans e (sym ef)))
        (subst (Pour (i ∷ x) (ox +ᴰ q) (st f S ∷ y)) (trans ef (sym e)) (nexty w))
