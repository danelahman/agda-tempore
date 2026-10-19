------------------------------------------------------------------------
-- A lower run on smaller weights gives one on larger weights.        --
--                                                                    --
-- The larger reading follows the smaller one move for move, except   --
-- where the smaller reading overflows a piece into the next stretch  --
-- while the larger one has already met the bounds of its chain:      --
-- there the larger reading closes its chain before the piece and     --
-- starts afresh at that next stretch. Afterwards the smaller chain   --
-- holds a prefix of pieces and bounds that the larger one has        --
-- dropped; since those pieces did not meet those bounds, whatever    --
-- meets the whole of the smaller chain meets what the larger one     --
-- keeps of it.                                                       --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Exact.Reader.Lower.Mimic
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; [_])
open import Data.List.Properties using (++-assoc; map-++; ++-identityʳ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (_≤ˢ_; ≤ˢ-⁺; Cut; ⁺; ⁻; 0⁻; _+ˡ_; ⊑⇒≤; by-pt; by-side; ⁻≤; ⁺≤⁺; _∨ˢ_; ⊏-cases;
         +ˡ-monoˡ; +ˡ-monoʳ; +ˡ-identityˡ; +ˡ-identityʳ; +ˡ-assoc; +ˡ-inflate)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-refl to ⊑ᶜ-refl; ⊑-trans to ⊑ᶜ-trans)
open import Syntax.Durations.Intervals.Dense T using (⊑⁻⇒<)

open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower T Op n code code-injective running

------------------------------------------------------------------------
-- Sums of lower ends

sumL : List Pl → Cut
sumL pre = sumˡ (map proj₂ pre)

sumˡ-++ : ∀ xs ys → sumˡ (xs ++ ys) ≡ sumˡ xs +ˡ sumˡ ys
sumˡ-++ []       ys = sym (+ˡ-identityˡ (sumˡ ys))
sumˡ-++ (x ∷ xs) ys = trans (cong (x +ˡ_) (sumˡ-++ xs ys)) (sym (+ˡ-assoc x (sumˡ xs) (sumˡ ys)))

sumL-++ : ∀ xs ys → sumL (xs ++ ys) ≡ sumL xs +ˡ sumL ys
sumL-++ xs ys = trans (cong sumˡ (map-++ proj₂ xs ys)) (sumˡ-++ (map proj₂ xs) (map proj₂ ys))

sumL-∷ʳ : ∀ xs x → sumL (xs ∷ʳ x) ≡ sumL xs +ˡ proj₂ x
sumL-∷ʳ xs x = trans (sumL-++ xs [ x ]) (cong (sumL xs +ˡ_) (+ˡ-identityʳ (proj₂ x)))

-- what bounds not met by a sum leave of larger bounds met by a larger sum

subtractˡ : ∀ {a b c d} → ¬ (c ⊑ᶜ a) → c +ˡ d ⊑ᶜ a +ˡ b → d ⊑ᶜ b
subtractˡ {a ∣ᶜ sa} {b ∣ᶜ sb} {c ∣ᶜ sc} {d ∣ᶜ sd} ¬ca t with ⊏-cases ¬ca
... | inj₁ a<c = by-pt d<b
  where
    d<b : d <ᴰ b
    d<b le = +ᴰ-monoˡ-< b a<c (≤ᴰ-trans (+ᴰ-monoʳ-≤ c le) (⊑⇒≤ t))
... | inj₂ (e , refl , refl) = go sb t
  where
    go : ∀ sb → ((c +ᴰ d) ∣ᶜ (⁺ ∨ˢ sd)) ⊑ᶜ ((a +ᴰ b) ∣ᶜ (⁻ ∨ˢ sb)) → (d ∣ᶜ sd) ⊑ᶜ (b ∣ᶜ sb)
    go ⁻ r = by-pt (λ le → ⊑⁻⇒< r refl (subst (λ u → a +ᴰ b ≤ᴰ u +ᴰ d) e (+ᴰ-monoʳ-≤ a le)))
    go ⁺ r = le⇒ (+ᴰ-cancelˡ-≤ a (subst (λ u → u +ᴰ d ≤ᴰ a +ᴰ b) (sym e) (⊑⇒≤ r)))
      where
        le⇒ : d ≤ᴰ b → (d ∣ᶜ sd) ⊑ᶜ (b ∣ᶜ ⁺)
        le⇒ le with compare d b
        ... | tri< x = by-pt x
        ... | tri> x = ⊥-elim (x le)
        ... | tri≈ x = by-side x (to⁺ sd)
          where
            to⁺ : ∀ s → s ≤ˢ ⁺
            to⁺ _ = ≤ˢ-⁺

------------------------------------------------------------------------
-- The two readings side by side

-- pieces with the same kinds, the weights no smaller

data Ge* : List Pl → List Pl → Set where
  []  : Ge* [] []
  _∷_ : ∀ {p q ps qs} → proj₁ q ≡ proj₁ p × proj₂ p ⊑ᶜ proj₂ q → Ge* ps qs → Ge* (p ∷ ps) (q ∷ qs)

Gap : List Pl → List Cut → Set
Gap A cs₀ = (A ≡ [] × cs₀ ≡ []) ⊎ ¬ Fitsᴸ A cs₀

record Drop (preW : List Pl) (csW : List Cut) (preQ : List Pl) (csQ : List Cut) : Set where
  field
    A B  : List Pl
    cs₀  : List Cut
    eW   : preW ≡ A ++ B
    eC   : csW ≡ cs₀ ++ csQ
    gap  : Gap A cs₀
    ge   : sumL B ⊑ᶜ sumL preQ

-- the larger reading is mid-piece only when the smaller one is, and
-- then its chain is short of its bounds

data Flags (preQ : List Pl) (csQ : List Cut) : Bool → Bool → Set where
  fresh : ∀ {mW} → Flags preQ csQ mW false
  mid   : ¬ Fitsᴸ preQ csQ → Flags preQ csQ true true

private
  open Drop

  transfer : ∀ {preW csW preQ csQ} → Drop preW csW preQ csQ
           → Fitsᴸ preW csW → Fitsᴸ preQ csQ
  transfer {preW} {csW} {preQ} {csQ} d f = ⊑ᶜ-trans kept (ge d)
    where
      whole : sumˡ (cs₀ d) +ˡ sumˡ csQ ⊑ᶜ sumL (A d) +ˡ sumL (B d)
      whole = subst₂ _⊑ᶜ_ (trans (cong sumˡ (eC d)) (sumˡ-++ (cs₀ d) csQ))
                          (trans (cong sumL (eW d)) (sumL-++ (A d) (B d))) f
      kept : sumˡ csQ ⊑ᶜ sumL (B d)
      kept with gap d
      ... | inj₁ (eA , eC₀) =
        subst₂ _⊑ᶜ_ (trans (cong (λ z → sumˡ z +ˡ sumˡ csQ) eC₀) (+ˡ-identityˡ _))
                    (trans (cong (λ z → sumL z +ˡ sumL (B d)) eA) (+ˡ-identityˡ _)) whole
      ... | inj₂ ¬g = subtractˡ ¬g whole

  d-pour : ∀ {preW csW preQ csQ p q} → Drop preW csW preQ csQ → proj₂ p ⊑ᶜ proj₂ q
         → Drop (preW ∷ʳ p) csW (preQ ∷ʳ q) csQ
  d-pour {preW} {csW} {preQ} {csQ} {p} {q} d w = record
    { A = A d ; B = B d ∷ʳ p ; cs₀ = cs₀ d
    ; eW = trans (cong (_∷ʳ p) (eW d)) (++-assoc (A d) (B d) [ p ])
    ; eC = eC d ; gap = gap d
    ; ge = subst₂ _⊑ᶜ_ (sym (sumL-∷ʳ (B d) p)) (sym (sumL-∷ʳ preQ q))
             (⊑ᶜ-trans (+ˡ-monoˡ (proj₂ p) (ge d)) (+ˡ-monoʳ (sumL preQ) w)) }

  d-more : ∀ {preW csW preQ csQ} c → Drop preW csW preQ csQ → Drop preW (csW ∷ʳ c) preQ (csQ ∷ʳ c)
  d-more c d = record
    { A = A d ; B = B d ; cs₀ = cs₀ d ; eW = eW d
    ; eC = trans (cong (_∷ʳ c) (eC d)) (++-assoc (cs₀ d) _ [ c ]) ; gap = gap d ; ge = ge d }

  d-start : ∀ c → Drop [] (c ∷ []) [] (c ∷ [])
  d-start c = record { A = [] ; B = [] ; cs₀ = [] ; eW = refl ; eC = refl ; gap = inj₁ (refl , refl) ; ge = ⊑ᶜ-refl }

  d-early : ∀ {preW csW} c → ¬ Fitsᴸ preW csW → Drop preW (csW ∷ʳ c) [] (c ∷ [])
  d-early {preW} {csW} c ¬f = record
    { A = preW ; B = [] ; cs₀ = csW ; eW = sym (++-identityʳ _) ; eC = refl
    ; gap = inj₂ ¬f ; ge = ⊑ᶜ-refl }

  still-short : ∀ {pre cs c} → ¬ Fitsᴸ pre cs → ¬ Fitsᴸ pre (cs ∷ʳ c)
  still-short {pre} {cs} {c} ¬f f =
    ¬f (⊑ᶜ-trans (+ˡ-inflate (sumˡ cs) c) (subst (_⊑ᶜ _) (sumˡ-∷ʳ′ cs c) f))
    where
      sumˡ-∷ʳ′ : ∀ cs c → sumˡ (cs ∷ʳ c) ≡ sumˡ cs +ˡ c
      sumˡ-∷ʳ′ cs c = trans (sumˡ-++ cs [ c ]) (cong (sumˡ cs +ˡ_) (+ˡ-identityʳ c))


mutual

  mimicᴸ : ∀ {ps qs v} → Ge* ps qs → RunL ps v → RunL qs v
  mimicᴸ []              done        = done
  mimicᴸ ((ek , _) ∷ ge) (match k r) = match (trans ek k) (mimicᴸ ge r)
  mimicᴸ ge              (start h)   = start (mC (d-start _) fresh ge h)

  mC : ∀ {S preW csW preQ csQ mW mQ ps qs v} → Drop preW csW preQ csQ → Flags preQ csQ mW mQ → Ge* ps qs
     → ChL S preW csW mW ps v → ChL S preQ csQ mQ qs v
  mC {S} d fl ((ek , w) ∷ ge) (pour ad h) =
    pour (subst (λ k → AdmK k S) (sym ek) ad) (mC (d-pour d w) fresh ge h)
  mC {S} {preQ = preQ} {csQ} {qs = q ∷ qs} d fl ((ek , w) ∷ ge) (over {c = c} ad ¬f g h)
    with Fitsᴸ? preQ csQ
  ... | yes fq = early fl
    where
      early : ∀ {mQ} → Flags preQ csQ _ mQ → ChL S preQ csQ mQ (q ∷ qs) _
      early fresh     = close fq (start (mC (d-early c ¬f) fresh ((ek , w) ∷ ge) h))
      early (mid ¬fq) = ⊥-elim (¬fq fq)
  ... | no ¬fq =
    over (subst (λ k → AdmK k S) (sym ek) ad) ¬fq (transfer (d-pour d w) g)
      (mC (d-more c d) (mid (still-short {preQ} {csQ} {c} ¬fq)) ((ek , w) ∷ ge) h)
  mC d fresh ge (close f r) = close (transfer d f) (mimicᴸ ge r)
