------------------------------------------------------------------------
-- Durations on a grid: the multiples of a unit.                      --
--                                                                    --
-- `k × δ` is `k` copies of the unit `δ`. For a positive unit, the    --
-- multiples are an ordered-monoid embedding of ℕ: they add as their  --
-- counts do and compare as their counts do. A time domain is         --
-- commensurable when every finite list of durations lies on the grid --
-- of one positive unit, and Archimedean when every duration lies     --
-- below some multiple of every positive unit; the first gives the    --
-- second.                                                            --
--                                                                    --
-- Cuts and upper ends of whole steps (`Intervals ℕᵀ`) scale to those --
-- of the time domain, point by point; the scaling preserves sums and --
-- preserves and reflects the order, so a comparison of sums of grid  --
-- values is decided on their counts.                                 --
------------------------------------------------------------------------

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Exact.Grid {D : Duration} (T : TimeDomain D) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)
open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
import Syntax.Durations.Intervals ℕᵀ as N
import Syntax.Durations.Monus ℕᵀ as NM

------------------------------------------------------------------------
-- Multiples of a unit

infixr 7 _×ᴰ_

_×ᴰ_ : ℕ → Carrier → Carrier
zero  ×ᴰ δ = 0ᴰ
suc k ×ᴰ δ = δ +ᴰ k ×ᴰ δ

×-+ : ∀ m n δ → (m ℕ.+ n) ×ᴰ δ ≡ m ×ᴰ δ +ᴰ n ×ᴰ δ
×-+ zero    n δ = sym (+ᴰ-identityˡ (n ×ᴰ δ))
×-+ (suc m) n δ = trans (cong (δ +ᴰ_) (×-+ m n δ)) (sym (+ᴰ-assoc δ (m ×ᴰ δ) (n ×ᴰ δ)))

×-mono : ∀ {m n} δ → m ℕ.≤ n → m ×ᴰ δ ≤ᴰ n ×ᴰ δ
×-mono {n = n} δ z≤n     = 0ᴰ-least (n ×ᴰ δ)
×-mono δ (s≤s r) = +ᴰ-monoʳ-≤ δ (×-mono δ r)

module _ {δ : Carrier} (δ-pos : 0ᴰ <ᴰ δ) where

  ×-reflect : ∀ {m n} → m ×ᴰ δ ≤ᴰ n ×ᴰ δ → m ℕ.≤ n
  ×-reflect {zero}  {n}     _ = z≤n
  ×-reflect {suc m} {zero}  r = ⊥-elim (δ-pos (≤ᴰ-trans (≤ᴰ-+ δ (m ×ᴰ δ)) r))
  ×-reflect {suc m} {suc n} r = s≤s (×-reflect (+ᴰ-cancelˡ-≤ δ r))

  ×-injective : ∀ {m n} → m ×ᴰ δ ≡ n ×ᴰ δ → m ≡ n
  ×-injective e = ℕ.≤-antisym (×-reflect (≤ᴰ-reflexive e)) (×-reflect (≤ᴰ-reflexive (sym e)))

  ×-<-reflect : ∀ {m n} → m ×ᴰ δ <ᴰ n ×ᴰ δ → m ℕ.< n
  ×-<-reflect {m} {n} r with m ℕ.<? n
  ... | yes p = p
  ... | no ¬p = ⊥-elim (r (×-mono δ (ℕ.≮⇒≥ ¬p)))

  ×-<-mono : ∀ {m n} → m ℕ.< n → m ×ᴰ δ <ᴰ n ×ᴰ δ
  ×-<-mono r s = ℕ.<⇒≱ r (×-reflect s)

------------------------------------------------------------------------
-- Grids, commensurability, and the Archimedean property

-- `q` is a multiple of `δ`

Grid : Carrier → Carrier → Set
Grid δ q = Σ[ k ∈ ℕ ] k ×ᴰ δ ≡ q

-- a positive unit with a count for itself and for each listed duration

record Unit (xs : List Carrier) : Set where
  field
    δ       : Carrier
    δ-pos   : 0ᴰ <ᴰ δ
    count   : Carrier → ℕ
    count-δ : count δ ≡ 1
    counts  : ∀ {q} → q ∈ xs → count q ×ᴰ δ ≡ q

Commensurable : Set
Commensurable = (xs : List Carrier) → Unit xs

Archimedean : Set
Archimedean = ∀ δ q → 0ᴰ <ᴰ δ → Σ[ m ∈ ℕ ] q ≤ᴰ m ×ᴰ δ

-- the counts of a unit and a duration bound the second by a multiple
-- of the first

commensurable⇒archimedean : Commensurable → Archimedean
commensurable⇒archimedean com δ q δ-pos = go (count δ) refl
  where
    open Unit (com (δ ∷ q ∷ [])) renaming (δ to u; δ-pos to u-pos)
    eδ : count δ ×ᴰ u ≡ δ
    eδ = counts (here refl)
    eq : count q ×ᴰ u ≡ q
    eq = counts (there (here refl))
    ×-assoc : ∀ a b → (a ℕ.* b) ×ᴰ u ≡ a ×ᴰ (b ×ᴰ u)
    ×-assoc zero    b = refl
    ×-assoc (suc a) b = trans (×-+ b (a ℕ.* b) u) (cong (b ×ᴰ u +ᴰ_) (×-assoc a b))
    go : ∀ c → count δ ≡ c → Σ[ m ∈ ℕ ] q ≤ᴰ m ×ᴰ δ
    go zero    c = ⊥-elim (δ-pos (≤ᴰ-reflexive (trans (sym eδ) (cong (_×ᴰ u) c))))
    go (suc c) e = count q ,
      ≤ᴰ-trans (≤ᴰ-reflexive (sym eq))
        (≤ᴰ-trans (×-mono u (ℕ.m≤m*n (count q) (suc c)))
          (≤ᴰ-reflexive (trans (×-assoc (count q) (suc c))
            (cong (count q ×ᴰ_) (trans (cong (_×ᴰ u) (sym e)) eδ)))))

------------------------------------------------------------------------
-- Scaling cuts and upper ends of whole steps

module Scale {δ : Carrier} (δ-pos : 0ᴰ <ᴰ δ) where

  scˢ : N.Side → Side
  scˢ N.⁻ = ⁻
  scˢ N.⁺ = ⁺

  scᶜ : N.Cut → Cut
  scᶜ (k N.∣ s) = (k ×ᴰ δ) ∣ scˢ s

  scʰ : N.Hi → Hi
  scʰ (N.fin c) = fin (scᶜ c)
  scʰ N.∞       = ∞

  -- sides

  scˢ-∧ : ∀ s t → scˢ (s N.∧ˢ t) ≡ scˢ s ∧ˢ scˢ t
  scˢ-∧ N.⁻ _ = refl
  scˢ-∧ N.⁺ t = refl

  scˢ-∨ : ∀ s t → scˢ (s N.∨ˢ t) ≡ scˢ s ∨ˢ scˢ t
  scˢ-∨ N.⁻ _ = refl
  scˢ-∨ N.⁺ t = refl

  scˢ-≤ : ∀ {s t} → s N.≤ˢ t → scˢ s ≤ˢ scˢ t
  scˢ-≤ N.⁻≤  = ⁻≤
  scˢ-≤ N.⁺≤⁺ = ⁺≤⁺

  scˢ-≤⁻ : ∀ {s t} → scˢ s ≤ˢ scˢ t → s N.≤ˢ t
  scˢ-≤⁻ {N.⁻} {_}   _   = N.⁻≤
  scˢ-≤⁻ {N.⁺} {N.⁺} _   = N.⁺≤⁺
  scˢ-≤⁻ {N.⁺} {N.⁻} ()

  -- sums

  scᶜ-+ˡ : ∀ c c′ → scᶜ (c N.+ˡ c′) ≡ scᶜ c +ˡ scᶜ c′
  scᶜ-+ˡ (k N.∣ s) (l N.∣ t) = cong₂ _∣_ (×-+ k l δ) (scˢ-∨ s t)

  scʰ-+ʰ : ∀ h h′ → scʰ (h N.+ʰ h′) ≡ scʰ h +ʰ scʰ h′
  scʰ-+ʰ (N.fin (k N.∣ s)) (N.fin (l N.∣ t)) = cong fin (cong₂ _∣_ (×-+ k l δ) (scˢ-∧ s t))
  scʰ-+ʰ (N.fin _) N.∞ = refl
  scʰ-+ʰ N.∞ _ = refl

  scᶜ-0⁻ : scᶜ N.0⁻ ≡ 0⁻
  scᶜ-0⁻ = refl

  scʰ-0⁺ : scʰ (N.fin N.0⁺) ≡ fin 0⁺
  scʰ-0⁺ = refl

  -- the order, preserved and reflected

  scᶜ-⊑ : ∀ {c c′} → c N.⊑ c′ → scᶜ c ⊑ scᶜ c′
  scᶜ-⊑ (N.by-pt r)     = by-pt (×-<-mono δ-pos (ℕ.≰⇒> r))
  scᶜ-⊑ (N.by-side e r) = by-side (cong (_×ᴰ δ) e) (scˢ-≤ r)

  scᶜ-⊑⁻ : ∀ {c c′} → scᶜ c ⊑ scᶜ c′ → c N.⊑ c′
  scᶜ-⊑⁻ {k N.∣ s} {l N.∣ t} (by-pt r) =
    N.by-pt (ℕ.<⇒≱ (×-<-reflect δ-pos r))
  scᶜ-⊑⁻ {k N.∣ s} {l N.∣ t} (by-side e r) =
    N.by-side (×-injective δ-pos e) (scˢ-≤⁻ r)

  scʰ-⊑ : ∀ {h h′} → h N.⊑ʰ h′ → scʰ h ⊑ʰ scʰ h′
  scʰ-⊑ {N.fin _} {N.fin _} r = scᶜ-⊑ r
  scʰ-⊑ {N.fin _} {N.∞}     _ = tt
  scʰ-⊑ {N.∞}     {N.∞}     _ = tt

  scʰ-⊑⁻ : ∀ {h h′} → scʰ h ⊑ʰ scʰ h′ → h N.⊑ʰ h′
  scʰ-⊑⁻ {N.fin _} {N.fin _} r = scᶜ-⊑⁻ r
  scʰ-⊑⁻ {N.fin _} {N.∞}     _ = tt
  scʰ-⊑⁻ {N.∞}     {N.∞}     _ = tt
  scʰ-⊑⁻ {N.∞}     {N.fin _} ()

  scᶜ-⇔ : ∀ c c′ → (c N.⊑ c′) ⇔ (scᶜ c ⊑ scᶜ c′)
  scᶜ-⇔ c c′ = mk⇔ scᶜ-⊑ scᶜ-⊑⁻

  scʰ-⇔ : ∀ h h′ → (h N.⊑ʰ h′) ⇔ (scʰ h ⊑ʰ scʰ h′)
  scʰ-⇔ h h′ = mk⇔ scʰ-⊑ scʰ-⊑⁻

  -- sums of lists

  sumʰ : List Hi → Hi
  sumʰ = foldr _+ʰ_ (fin 0⁺)

  sumˡ : List Cut → Cut
  sumˡ = foldr _+ˡ_ 0⁻

  scʰ-sum : ∀ hs → scʰ (foldr N._+ʰ_ (N.fin N.0⁺) hs) ≡ sumʰ (map scʰ hs)
  scʰ-sum []       = refl
  scʰ-sum (h ∷ hs) = trans (scʰ-+ʰ h _) (cong (scʰ h +ʰ_) (scʰ-sum hs))

  scᶜ-sum : ∀ cs → scᶜ (foldr N._+ˡ_ N.0⁻ cs) ≡ sumˡ (map scᶜ cs)
  scᶜ-sum []       = refl
  scᶜ-sum (c ∷ cs) = trans (scᶜ-+ˡ c _) (cong (scᶜ c +ˡ_) (scᶜ-sum cs))
