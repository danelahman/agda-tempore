------------------------------------------------------------------------
-- The lower reader: weights and bounds are lower ends.               --
--                                                                    --
-- A chain's bounds are met when the sum of its stretches' lower ends --
-- lies below the sum of the weights poured into it. Read on the      --
-- pieces of an exact run against closed bounds, an accepting run of  --
-- the reader builds a word of the bound that the run fits: every     --
-- stretch of a chain but the last takes exactly its bound, the last  --
-- takes the rest.                                                    --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Exact.Reader.Lower
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; foldr; [_])
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Cut; _⊑_; _⊑?_; ⁺; ⁻; 0⁻; _+ˡ_; ⊑⇒≤; ≤⇒⁻⊑⁻)
  renaming (_∣_ to _∣ᶜ_)

open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader T Op n code code-injective running

------------------------------------------------------------------------
-- Weights, bounds and the comparison

Pl : Set
Pl = Piece Cut

sumˡ : List Cut → Cut
sumˡ = foldr _+ˡ_ 0⁻

Fitsᴸ : List Pl → List Cut → Set
Fitsᴸ pre cs = sumˡ cs ⊑ sumˡ (map proj₂ pre)

Fitsᴸ? : ∀ pre cs → Dec (Fitsᴸ pre cs)
Fitsᴸ? pre cs = sumˡ cs ⊑? sumˡ (map proj₂ pre)

open Lower proj₁ Fitsᴸ public
open Lower.Decide proj₁ Fitsᴸ Fitsᴸ? public

-- the closed reading of a length, as a lower end

cl⁻ : Carrier → Cut
cl⁻ c = c ∣ᶜ ⁻

toLo : Piece Carrier → Pl
toLo (k , τ) = k , cl⁻ τ

clo⁻ : Letter Carrier → Letter Cut
clo⁻ (op o)   = op o
clo⁻ (st S c) = st S (cl⁻ c)

sum-cl⁻ : ∀ xs → sumˡ (map cl⁻ xs) ≡ cl⁻ (sumᴰ xs)
sum-cl⁻ []       = refl
sum-cl⁻ (x ∷ xs) rewrite sum-cl⁻ xs = refl

wts-toLo : ∀ ps → map proj₂ (map toLo ps) ≡ map cl⁻ (amts ps)
wts-toLo []       = refl
wts-toLo (p ∷ ps) = cong (_ ∷_) (wts-toLo ps)

sum-toLo : ∀ ps → sumˡ (map proj₂ (map toLo ps)) ≡ cl⁻ (sumᴰ (amts ps))
sum-toLo ps = trans (cong sumˡ (wts-toLo ps)) (sum-cl⁻ (amts ps))

fitsᴸ⇒ : ∀ pre cs → Fitsᴸ (map toLo pre) (map cl⁻ cs) → sumᴰ cs ≤ᴰ sumᴰ (amts pre)
fitsᴸ⇒ pre cs f = ⊑⇒≤ (subst₂ _⊑_ (sum-cl⁻ cs) (sum-toLo pre) f)

⇒fitsᴸ : ∀ pre cs → sumᴰ cs ≤ᴰ sumᴰ (amts pre) → Fitsᴸ (map toLo pre) (map cl⁻ cs)
⇒fitsᴸ pre cs r = subst₂ _⊑_ (sym (sum-cl⁻ cs)) (sym (sum-toLo pre)) (≤⇒⁻⊑⁻ r)
