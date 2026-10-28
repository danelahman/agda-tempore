------------------------------------------------------------------------
-- An upper run on larger weights gives one on smaller weights.       --
--                                                                    --
-- The smaller reading follows the larger one move for move, except   --
-- where the larger reading overflows a piece that the smaller one    --
-- can still pour whole. There the smaller reading pours it, closes   --
-- its chain, and starts afresh at the stretch the larger one         --
-- overflows into, one piece ahead. Afterwards the larger chain holds --
-- a prefix of pieces and bounds that the smaller one has dropped;    --
-- since those pieces did not fit those bounds, whatever fits the     --
-- whole of the larger chain fits what the smaller one keeps of it.   --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Reader.Upper.Mimic
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; [_])
open import Data.List.Properties using (++-assoc; map-++)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; Hi; fin; ∞; _⊑_; _⊑ʰ_; ⁺; ⁻; 0⁺; _+ʰ_; ⊑⇒≤; by-pt; by-side; ⊑ʰ-trans; ⊑ʰ-∞;
         +ʰ-mono; +ʰ-identityˡ; +ʰ-identityʳ; +ʰ-assoc; ⊑ʰ-refl; _≤ˢ_; ⁻≤; ⁺≤⁺; _∧ˢ_;
         ⊏-cases; ≤⇒⁻⊑⁻; ⊑-trans)
  renaming (_∣_ to _∣ᶜ_)

open import Grades.Durations.Intervals.Dense T using (⊑⁻⇒<)
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Reader.Upper T Op n code code-injective running

------------------------------------------------------------------------
-- Sums of upper ends

sumW : List Ph → Hi
sumW pre = sumʰ (map proj₂ pre)

sumʰ-++ : ∀ xs ys → sumʰ (xs ++ ys) ≡ sumʰ xs +ʰ sumʰ ys
sumʰ-++ []       ys = sym (+ʰ-identityˡ (sumʰ ys))
sumʰ-++ (x ∷ xs) ys = trans (cong (x +ʰ_) (sumʰ-++ xs ys)) (sym (+ʰ-assoc x (sumʰ xs) (sumʰ ys)))

sumW-++ : ∀ xs ys → sumW (xs ++ ys) ≡ sumW xs +ʰ sumW ys
sumW-++ xs ys = trans (cong sumʰ (map-++ proj₂ xs ys)) (sumʰ-++ (map proj₂ xs) (map proj₂ ys))

-- what a sum that does not fit leaves of a larger sum that does

subtract : ∀ {a b c d} → ¬ (a ⊑ʰ c) → a +ʰ b ⊑ʰ c +ʰ d → b ⊑ʰ d
subtract {b = b} {d = ∞} _ _ = ⊑ʰ-∞ b
subtract {a = a} {c = ∞} ¬ac _ = ⊥-elim (¬ac (⊑ʰ-∞ a))
subtract {∞} {b} {fin c} {fin d} _ ()
subtract {fin a} {∞} {fin c} {fin d} _ ()
subtract {fin (a ∣ᶜ sa)} {fin (b ∣ᶜ sb)} {fin (c ∣ᶜ sc)} {fin (d ∣ᶜ sd)} ¬ac t with ⊏-cases ¬ac
... | inj₁ c<a = ≤⇒⊑ (λ db → +ᴰ-mono-< c<a db (⊑⇒≤ t))
  where
    +ᴰ-mono-< : c <ᴰ a → d <ᴰ b → c +ᴰ d <ᴰ a +ᴰ b
    +ᴰ-mono-< p q = <-trans (+ᴰ-monoˡ-< d p) (+ᴰ-monoʳ-< a q)
    -- strictly below or equal points: the cut of `b` lies below that of `d`
    ≤⇒⊑ : ¬ (d <ᴰ b) → (b ∣ᶜ sb) ⊑ (d ∣ᶜ sd)
    ≤⇒⊑ ¬db with compare b d
    ... | tri< x = by-pt x
    ... | tri> x = ⊥-elim (¬db x)
    ... | tri≈ e =
      ⊥-elim (subst (λ z → c +ᴰ z <ᴰ a +ᴰ b) e (+ᴰ-monoˡ-< b c<a) (⊑⇒≤ t))
... | inj₂ (e , refl , refl) = go sb t
  where
    go : ∀ sb → ((a +ᴰ b) ∣ᶜ (⁺ ∧ˢ sb)) ⊑ ((c +ᴰ d) ∣ᶜ ⁻) → (b ∣ᶜ sb) ⊑ (d ∣ᶜ sd)
    go ⁺ r = by-pt (λ z → ⊑⁻⇒< r refl (subst (λ u → u +ᴰ d ≤ᴰ a +ᴰ b) (sym e) (+ᴰ-monoʳ-≤ a z)))
    go ⁻ r = ⊑-trans (≤⇒⁻⊑⁻ (+ᴰ-cancelˡ-≤ a (subst (λ u → a +ᴰ b ≤ᴰ u +ᴰ d) e (⊑⇒≤ r))))
                     (by-side refl ⁻≤)

sumW-∷ʳ : ∀ xs x → sumW (xs ∷ʳ x) ≡ sumW xs +ʰ proj₂ x
sumW-∷ʳ xs x = trans (sumW-++ xs [ x ]) (cong (sumW xs +ʰ_) (+ʰ-identityʳ (proj₂ x)))

------------------------------------------------------------------------
-- The two readings side by side

-- pieces with the same kinds, the weights no larger

data Le* : List Ph → List Ph → Set where
  []  : Le* [] []
  _∷_ : ∀ {p q ps qs} → proj₁ q ≡ proj₁ p × proj₂ q ⊑ʰ proj₂ p → Le* ps qs → Le* (p ∷ ps) (q ∷ qs)

-- the larger chain is a dropped part `A`, against bounds `cs₀`, and a
-- kept part `B`, against the smaller chain's bounds

Gap : List Ph → List Hi → Set
Gap A cs₀ = (A ≡ [] × cs₀ ≡ []) ⊎ ¬ Fitsᵁ A cs₀

record Drop (preW : List Ph) (csW : List Hi) (preQ : List Ph) (csQ : List Hi) : Set where
  field
    A B  : List Ph
    cs₀  : List Hi
    eW   : preW ≡ A ++ B
    eC   : csW ≡ cs₀ ++ csQ
    gap  : Gap A cs₀
    le   : sumW preQ ⊑ʰ sumW B

private
  open Drop

  transfer : ∀ {preW csW preQ csQ p q} → Drop preW csW preQ csQ
           → proj₂ q ⊑ʰ proj₂ p → Fitsᵁ (preW ∷ʳ p) csW → Fitsᵁ (preQ ∷ʳ q) csQ
  transfer {preW} {csW} {preQ} {csQ} {p} {q} d w f =
    subst (_⊑ʰ sumʰ csQ) (sym (sumW-∷ʳ preQ q))
      (⊑ʰ-trans (+ʰ-mono (le d) w) (subst (_⊑ʰ sumʰ csQ) (sumW-∷ʳ (B d) p) kept))
    where
      whole : sumW (A d) +ʰ sumW (B d ∷ʳ p) ⊑ʰ sumʰ (cs₀ d) +ʰ sumʰ csQ
      whole = subst₂ _⊑ʰ_
                (trans (cong sumW (trans (cong (_∷ʳ p) (eW d)) (++-assoc (A d) (B d) [ p ])))
                       (sumW-++ (A d) (B d ∷ʳ p)))
                (trans (cong sumʰ (eC d)) (sumʰ-++ (cs₀ d) csQ))
                f
      kept : sumW (B d ∷ʳ p) ⊑ʰ sumʰ csQ
      kept with gap d
      ... | inj₁ (eA , eC₀) =
        subst₂ _⊑ʰ_ (trans (cong (λ z → sumW z +ʰ sumW (B d ∷ʳ p)) eA) (+ʰ-identityˡ _))
                    (trans (cong (λ z → sumʰ z +ʰ sumʰ csQ) eC₀) (+ʰ-identityˡ _)) whole
      ... | inj₂ ¬g = subtract ¬g whole

  d-pour : ∀ {preW csW preQ csQ p q} → Drop preW csW preQ csQ → proj₂ q ⊑ʰ proj₂ p
         → Drop (preW ∷ʳ p) csW (preQ ∷ʳ q) csQ
  d-pour {preW} {csW} {preQ} {csQ} {p} {q} d w = record
    { A = A d ; B = B d ∷ʳ p ; cs₀ = cs₀ d
    ; eW = trans (cong (_∷ʳ p) (eW d)) (++-assoc (A d) (B d) [ p ])
    ; eC = eC d ; gap = gap d
    ; le = subst₂ _⊑ʰ_ (sym (sumW-∷ʳ preQ q)) (sym (sumW-∷ʳ (B d) p)) (+ʰ-mono (le d) w) }

  d-more : ∀ {preW csW preQ csQ} c → Drop preW csW preQ csQ → Drop preW (csW ∷ʳ c) preQ (csQ ∷ʳ c)
  d-more c d = record
    { A = A d ; B = B d ; cs₀ = cs₀ d ; eW = eW d
    ; eC = trans (cong (_∷ʳ c) (eC d)) (++-assoc (cs₀ d) _ [ c ]) ; gap = gap d ; le = le d }

  d-start : ∀ c → Drop [] (c ∷ []) [] (c ∷ [])
  d-start c = record { A = [] ; B = [] ; cs₀ = [] ; eW = refl ; eC = refl ; gap = inj₁ (refl , refl) ; le = ⊑ʰ-refl }

  d-ahead : ∀ {preW cs₀ p} c → ¬ Fitsᵁ (preW ∷ʳ p) cs₀ → Drop (preW ∷ʳ p) (cs₀ ∷ʳ c) [] (c ∷ [])
  d-ahead {preW} {cs₀} {p} c ¬f = record
    { A = preW ∷ʳ p ; B = [] ; cs₀ = cs₀ ; eW = sym (++-identityʳ _) ; eC = refl
    ; gap = inj₂ ¬f ; le = ⊑ʰ-refl }
    where open import Data.List.Properties using (++-identityʳ)

mutual

  mimic : ∀ {ps qs v} → Le* ps qs → RunU ps v → RunU qs v
  mimic []                done        = done
  mimic ((ek , _) ∷ le)   (match k r) = match (trans ek k) (mimic le r)
  mimic le                (start h)   = start (mC (d-start _) le h)

  mC : ∀ {S preW csW preQ csQ m ps qs v} → Drop preW csW preQ csQ → Le* ps qs
     → ChU S preW csW m ps v → ChU S preQ csQ m qs v
  mC {S} d ((ek , w) ∷ le) (pour ad f h) =
    pour (subst (λ k → AdmK k S) (sym ek) ad) (transfer d w f) (mC (d-pour d w) le h)
  mC {S} {preQ = preQ} {csQ} {qs = q ∷ qs} d ((ek , w) ∷ le) (over ad ¬f o)
    with Fitsᵁ? (preQ ∷ʳ q) csQ
  ... | yes g = pour (subst (λ k → AdmK k S) (sym ek) ad) g (close (mOa ¬f le o))
  ... | no ¬g = over (subst (λ k → AdmK k S) (sym ek) ad) ¬g (mOv d (ek , w) le o)
  mC d le (close r) = close (mimic le r)

  mOv : ∀ {preW csW preQ csQ p q ps qs v} → Drop preW csW preQ csQ
      → proj₁ q ≡ proj₁ p × proj₂ q ⊑ʰ proj₂ p → Le* ps qs
      → OverU preW csW p ps v → OverU preQ csQ q qs v
  mOv d lp le (enter {c = c} h) = enter (mC (d-more c d) (lp ∷ le) h)
  mOv d lp le (pass o)          = pass (mOv d lp le o)

  mOa : ∀ {preW csW p ps qs v} → ¬ Fitsᵁ (preW ∷ʳ p) csW → Le* ps qs
      → OverU preW csW p ps v → RunU qs v
  mOa ¬f le (enter h) = start (mA ¬f le h)
  mOa ¬f le (pass o)  = start (close (mOa ¬f le o))

  mA : ∀ {S preW cs₀ c p ps qs v} → ¬ Fitsᵁ (preW ∷ʳ p) cs₀ → Le* ps qs
     → ChU S preW (cs₀ ∷ʳ c) true (p ∷ ps) v → ChU S [] (c ∷ []) false qs v
  mA {c = c} ¬f le (pour ad f h)    = mC (d-ahead c ¬f) le h
  mA         ¬f le (over ad ¬f′ o)  = close (mOa ¬f′ le o)
