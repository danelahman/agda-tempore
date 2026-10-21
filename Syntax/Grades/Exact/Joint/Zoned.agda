------------------------------------------------------------------------
-- The joint walk on zones.                                           --
--                                                                    --
-- The walk of `Exact.Joint` with the time the piece in progress has  --
-- run replaced by a zone of such times: a walk on zones from a zone  --
-- `I` is a walk from some time in `I`. Where a piece of the lower    --
-- word ends inside a piece of the upper, the upper's zone grows by   --
-- the lengths the lower letter admits (`⊕ᶻ`); where the upper piece  --
-- ends, the lower one has run for the times `C ⊖ᶻ I`, `C` the        --
-- lengths the upper letter admits; where both end, the two must      --
-- meet (`∩ᶻ`). A zone is then normalised for the letter in progress, --
-- keeping the walks it admits:                                       --
--                                                                    --
--   a letter with a finite upper end: times past it are dropped,     --
--     the piece having to end within it;                             --
--   an upper stretch without end: every time is alike, so the zone   --
--     is every positive time;                                        --
--   a lower stretch with lower end `c`: times past `c` are alike, so --
--     the zone's lower end is lowered to `c` and its upper end       --
--     raised to `∞` once it is past `c`.                             --
--                                                                    --
-- Normalised zones have ends bounded by the letters' ends, so        --
-- finitely many occur (`Joint.Decide`). In a dense time domain the   --
-- walks on zones are exactly the walks (`zoned⇔walk`).               --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Joint.Zoned
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
open import Syntax.Durations.Intervals.Dense T using (_∈ⁱ_)

open import Syntax.Grades.Exact.Expression T Op n code code-injective running
  using (Instance; upper; lower; End; _∈ᵉ_)
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
  using (Letter; op; st; Word′)
open import Syntax.Grades.Exact.Joint T Op n code code-injective running
open import Syntax.Grades.Exact.Joint.Zone T

open Exactᶻ dense κ κ-pos

open RunningTimes.RunningTimes running using (rt; rt-pos)

------------------------------------------------------------------------
-- The positive lengths a letter admits

Aᴸ : Letter Cut → Zone
Aᴸ (op o)   = ⟨ lo (rt o) , hi (rt o) ⟩ᶻ
Aᴸ (st S c) = ⟨ 0⁺ ⊔ᶜ c , ∞ ⟩ᶻ

Aᵁ : Letter Hi → Zone
Aᵁ (op o)   = ⟨ lo (rt o) , hi (rt o) ⟩ᶻ
Aᵁ (st S h) = ⟨ 0⁺ , h ⟩ᶻ

Aᴸ-sound : ∀ ℓ {t} → t ∈ᶻ Aᴸ ℓ → 0ᴰ <ᴰ t × Adm {lower} ℓ t
Aᴸ-sound (op o)   m       = rt-pos o m , m
Aᴸ-sound (st S c) (r , _) with lo-read (⊑-trans (⊔ᶜ-ubˡ 0⁺ c) r)
... | lo⁺ p = p , ⊑-trans (⊔ᶜ-ubʳ 0⁺ c) r

Aᴸ-complete : ∀ ℓ {t} → 0ᴰ <ᴰ t → Adm {lower} ℓ t → t ∈ᶻ Aᴸ ℓ
Aᴸ-complete (op o)   _ m = m
Aᴸ-complete (st S c) p a = ⊔ᶜ-lub (lo-write (lo⁺ p)) a , tt

Aᵁ-sound : ∀ m {t} → t ∈ᶻ Aᵁ m → 0ᴰ <ᴰ t × Adm {upper} m t
Aᵁ-sound (op o)   m        = rt-pos o m , m
Aᵁ-sound (st S h) (r , r′) with lo-read r
... | lo⁺ p = p , r′

Aᵁ-complete : ∀ m {t} → 0ᴰ <ᴰ t → Adm {upper} m t → t ∈ᶻ Aᵁ m
Aᵁ-complete (op o)   _ m = m
Aᵁ-complete (st S h) p a = lo-write (lo⁺ p) , a

------------------------------------------------------------------------
-- What a walk sees of the time its piece in progress has run

private
  +pos : ∀ {e t} → 0ᴰ <ᴰ t → 0ᴰ <ᴰ e +ᴰ t
  +pos {e} {t} p = <-≤-trans p (≤ᴰ-+ˡ t e)

  assoc-adm : ∀ {s} (ℓ : Letter (End s)) {e t u} → Adm ℓ ((e +ᴰ t) +ᴰ u) → Adm ℓ (e +ᴰ (t +ᴰ u))
  assoc-adm ℓ {e} {t} {u} = subst (Adm ℓ) (+ᴰ-assoc e t u)

  assoc-adm⁻ : ∀ {s} (ℓ : Letter (End s)) {e t u} → Adm ℓ (e +ᴰ (t +ᴰ u)) → Adm ℓ ((e +ᴰ t) +ᴰ u)
  assoc-adm⁻ ℓ {e} {t} {u} = subst (Adm ℓ) (sym (+ᴰ-assoc e t u))

-- the piece in progress ends later, at a length its letter admits

pendingᵁ : ∀ {v w m e} → Walk v w (inU m e) → Σ[ s ∈ Carrier ] 0ᴰ <ᴰ s × Adm m (e +ᴰ s)
pendingᵁ (skipL _ _ j) = pendingᵁ j
pendingᵁ {m = m} (firstL {t = t} _ pt _ j) with pendingᵁ j
... | s , ps , a = t +ᴰ s , +pos ps , assoc-adm m a
pendingᵁ (lateU {t = t} _ pt a _)   = t , pt , a
pendingᵁ (bothU {t = t} _ pt _ b _) = t , pt , b

pendingᴸ : ∀ {v w ℓ e} → Walk v w (inL ℓ e) → Σ[ s ∈ Carrier ] 0ᴰ <ᴰ s × Adm ℓ (e +ᴰ s)
pendingᴸ (skipU _ _ j) = pendingᴸ j
pendingᴸ {ℓ = ℓ} (firstU {t = t} _ pt _ j) with pendingᴸ j
... | s , ps , a = t +ᴰ s , +pos ps , assoc-adm ℓ a
pendingᴸ (lateL {t = t} _ pt a _)   = t , pt , a
pendingᴸ (bothL {t = t} _ pt a _ _) = t , pt , a

-- and the time it has run is seen only through the lengths its letter
-- admits after more time

relabelᵁ : ∀ {v w m e e₂} → (∀ s → Adm m (e +ᴰ s) → Adm m (e₂ +ᴰ s))
         → Walk v w (inU m e) → Walk v w (inU m e₂)
relabelᵁ h (skipL φ a j)              = skipL inU a (relabelᵁ h j)
relabelᵁ {m = m} h (firstL {t = t} mt pt a j) =
  firstL mt pt a (relabelᵁ (λ u x → assoc-adm⁻ m (h (t +ᴰ u) (assoc-adm m x))) j)
relabelᵁ h (lateU {t = t} mt pt a j)   = lateU mt pt (h t a) j
relabelᵁ h (bothU {t = t} mt pt a b j) = bothU mt pt a (h t b) j

relabelᴸ : ∀ {v w ℓ e e₂} → (∀ s → Adm ℓ (e +ᴰ s) → Adm ℓ (e₂ +ᴰ s))
         → Walk v w (inL ℓ e) → Walk v w (inL ℓ e₂)
relabelᴸ h (skipU φ a j)              = skipU inL a (relabelᴸ h j)
relabelᴸ {ℓ = ℓ} h (firstU {t = t} mt pt a j) =
  firstU mt pt a (relabelᴸ (λ u x → assoc-adm⁻ ℓ (h (t +ᴰ u) (assoc-adm ℓ x))) j)
relabelᴸ h (lateL {t = t} mt pt a j)   = lateL mt pt (h t a) j
relabelᴸ h (bothL {t = t} mt pt a b j) = bothL mt pt (h t a) b j

------------------------------------------------------------------------
-- Normalising a zone for the letter in progress

normᵁ : Letter Hi → Zone → Zone
normᵁ (op o)         I = I ∩ᶻ ⟨ 0⁻ , hi (rt o) ⟩ᶻ
normᵁ (st S (fin c)) I = I ∩ᶻ ⟨ 0⁻ , fin c ⟩ᶻ
normᵁ (st S ∞)       I = ⟨ 0⁺ , ∞ ⟩ᶻ

normᴸ : Letter Cut → Zone → Zone
normᴸ (op o)   I = I ∩ᶻ ⟨ 0⁻ , hi (rt o) ⟩ᶻ
normᴸ (st S c) I = ⟨ loᶻ I ⊓ᶜ c , raise c (hiᶻ I) ⟩ᶻ

private
  -- below an upper end that a later time is below
  below-hi : ∀ {e s h} → fin ((e +ᴰ s) ∣ ⁺) ⊑ʰ h → fin (e ∣ ⁺) ⊑ʰ h
  below-hi {e} {s} {h} r = ⊑ʰ-trans {fin (e ∣ ⁺)} {fin ((e +ᴰ s) ∣ ⁺)} {h} (≤⇒⁺⊑⁺ (≤ᴰ-+ e s)) r

  -- a lower end below a time stays below every later one
  above-lo : ∀ {c e s} → c ⊑ (e ∣ ⁻) → c ⊑ ((e +ᴰ s) ∣ ⁻)
  above-lo {c} {e} {s} r = ⊑-trans r (≤⇒⁻⊑⁻ (≤ᴰ-+ e s))

  -- a cut strictly below `x ∣ ⁺` is below `x ∣ ⁻`
  ⊏⁺⇒⊑⁻ : ∀ {h x} → h ⊏ (x ∣ ⁺) → h ⊑ (x ∣ ⁻)
  ⊏⁺⇒⊑⁻ {p ∣ s} r with ⊏-cases r
  ... | inj₁ a              = by-pt a
  ... | inj₂ (e , refl , _) = by-side e ⁻≤

  ⊓ʰ-∞ : ∀ h → h ⊓ʰ ∞ ≡ h
  ⊓ʰ-∞ (fin _) = refl
  ⊓ʰ-∞ ∞       = refl

normᵁ-complete : ∀ m {v w e I} → Walk v w (inU m e) → 0ᴰ <ᴰ e → e ∈ᶻ I → e ∈ᶻ normᵁ m I
normᵁ-complete (op o) j pe m with pendingᵁ j
... | s , _ , a = ∩ᶻ-sound m (0⁻-least _ , below-hi (proj₂ a))
normᵁ-complete (st S (fin c)) j pe m with pendingᵁ j
... | s , _ , a = ∩ᶻ-sound m (0⁻-least _ , below-hi {h = fin c} a)
normᵁ-complete (st S ∞) j pe m = lo-write (lo⁺ pe) , tt

normᴸ-complete : ∀ ℓ {v w e I} → Walk v w (inL ℓ e) → 0ᴰ <ᴰ e → e ∈ᶻ I → e ∈ᶻ normᴸ ℓ I
normᴸ-complete (op o) j pe m with pendingᴸ j
... | s , _ , a = ∩ᶻ-sound m (0⁻-least _ , below-hi (proj₂ a))
normᴸ-complete (st S c) {I = I} j pe (r , r′) = ⊑-trans (⊓ᶜ-lbˡ (loᶻ I) c) r , up (c ◁? hiᶻ I)
  where
    up : Dec (c ◁ hiᶻ I) → fin (_ ∣ ⁺) ⊑ʰ raise c (hiᶻ I)
    up d with c ◁? hiᶻ I
    ... | yes _ = tt
    ... | no _  = r′

normᵁ-sound : ∀ m {v w e₂ I} → Inh I → e₂ ∈ᶻ normᵁ m I → Walk v w (inU m e₂)
            → Σ[ e ∈ Carrier ] e ∈ᶻ I × Walk v w (inU m e)
normᵁ-sound (op o)         iI m j = _ , proj₁ (∩ᶻ-elim m) , j
normᵁ-sound (st S (fin c)) iI m j = _ , proj₁ (∩ᶻ-elim m) , j
normᵁ-sound (st S ∞)       iI m j with inhabited iI
... | e , e∈ = e , e∈ , relabelᵁ (λ _ _ → tt) j

private
  ⊔-◁′ : ∀ {a b h} → a ◁ h → b ◁ h → a ⊔ᶜ b ◁ h
  ⊔-◁′ {a} {b} {h} u v with ⊔ᶜ-sel a b
  ... | inj₁ e = subst (_◁ h) (sym e) u
  ... | inj₂ e = subst (_◁ h) (sym e) v

  -- outside a zone, a time of its normalisation for a lower stretch
  -- with lower end `c` is past `c`, and some time of the zone is too
  past : ∀ {e₂} c l h → l ◁ h → (l ⊓ᶜ c) ⊑ (e₂ ∣ ⁻) → fin (e₂ ∣ ⁺) ⊑ʰ raise c h
       → ¬ (e₂ ∈ᶻ ⟨ l , h ⟩ᶻ) → c ⊑ (e₂ ∣ ⁻) × Inh (⟨ l , h ⟩ᶻ ∩ᶻ ⟨ c , ∞ ⟩ᶻ)
  past {e₂} c l h iI r r′ ¬m with c ◁? h
  ... | yes c◁ with l ⊑? (e₂ ∣ ⁻)
  ...   | no ¬l = low ¬l , subst (l ⊔ᶜ c ◁_) (sym (⊓ʰ-∞ h)) (⊔-◁′ iI c◁)
    where
      low : ¬ (l ⊑ (e₂ ∣ ⁻)) → c ⊑ (e₂ ∣ ⁻)
      low ¬l with ⊓ᶜ-sel l c
      ... | inj₁ e = ⊥-elim (¬l (subst (_⊑ (e₂ ∣ ⁻)) e r))
      ... | inj₂ e = subst (_⊑ (e₂ ∣ ⁻)) e r
  past {e₂} c l ∞ iI r r′ ¬m | yes c◁ | yes ll = ⊥-elim (¬m (ll , tt))
  past {e₂} c l (fin h) iI r r′ ¬m | yes c◁ | yes ll with (e₂ ∣ ⁺) ⊑? h
  ... | yes u = ⊥-elim (¬m (ll , u))
  ... | no ¬u = ⊑-trans (⊏⇒⊑ c◁) (⊏⁺⇒⊑⁻ ¬u) , ⊔-◁′ {l} {c} {fin h} iI c◁
  past {e₂} c l h iI r r′ ¬m | no ¬c◁ with l ⊑? (e₂ ∣ ⁻)
  ... | yes ll = ⊥-elim (¬m (ll , r′))
  ... | no ¬l with ⊓ᶜ-sel l c
  ...   | inj₁ e = ⊥-elim (¬l (subst (_⊑ (e₂ ∣ ⁻)) e r))
  ...   | inj₂ e = ⊥-elim (¬c◁ (∈⇒Inh {e₂} {⟨ c , h ⟩ᶻ} (subst (_⊑ (e₂ ∣ ⁻)) e r , r′)))

normᴸ-sound : ∀ ℓ {v w e₂ I} → Inh I → e₂ ∈ᶻ normᴸ ℓ I → Walk v w (inL ℓ e₂)
            → Σ[ e ∈ Carrier ] e ∈ᶻ I × Walk v w (inL ℓ e)
normᴸ-sound (op o) iI m j = _ , proj₁ (∩ᶻ-elim m) , j
normᴸ-sound (st S c) {e₂ = e₂} {I} iI (r , r′) j with e₂ ∈ᶻ? I
... | yes m = e₂ , m , j
... | no ¬m with past c (loᶻ I) (hiᶻ I) iI r r′ ¬m
...   | c⊑e₂ , inh with inhabited inh
...     | e , e∈ = e , proj₁ (∩ᶻ-elim e∈) ,
          relabelᴸ (λ s _ → above-lo {s = s} (proj₁ (proj₂ (∩ᶻ-elim {Z = I} e∈)))) j

------------------------------------------------------------------------
-- The walk on zones

data ZPhase : Set where
  zsync : ZPhase
  zinL  : Letter Cut → Zone → ZPhase
  zinU  : Letter Hi → Zone → ZPhase

data ZAtL : ZPhase → Set where
  zsync : ZAtL zsync
  zinU  : ∀ {m I} → ZAtL (zinU m I)

data ZAtU : ZPhase → Set where
  zsync : ZAtU zsync
  zinL  : ∀ {ℓ I} → ZAtU (zinL ℓ I)

data ZWalk : Word′ lower → Word′ upper → ZPhase → Set where
  zdone  : ZWalk [] [] zsync
  zskipL : ∀ {S c v w φ} → ZAtL φ → 0ᴰ ∈ᵉ c → ZWalk v w φ → ZWalk (st S c ∷ v) w φ
  zskipU : ∀ {S h v w φ} → ZAtU φ → 0ᴰ ∈ᵉ h → ZWalk v w φ → ZWalk v (st S h ∷ w) φ
  zopop  : ∀ {o v w} → Inh (Aᴸ (op o)) → ZWalk v w zsync → ZWalk (op o ∷ v) (op o ∷ w) zsync
  zsyncL : ∀ {ℓ m v w} → Meets ℓ m → Inh (Aᴸ ℓ) → Inh (normᵁ m (Aᴸ ℓ))
         → ZWalk v w (zinU m (normᵁ m (Aᴸ ℓ))) → ZWalk (ℓ ∷ v) (m ∷ w) zsync
  zsyncU : ∀ {ℓ m v w} → Meets ℓ m → Inh (Aᵁ m) → Inh (normᴸ ℓ (Aᵁ m))
         → ZWalk v w (zinL ℓ (normᴸ ℓ (Aᵁ m))) → ZWalk (ℓ ∷ v) (m ∷ w) zsync
  zsyncB : ∀ {ℓ m v w} → Meets ℓ m → Inh (Aᴸ ℓ ∩ᶻ Aᵁ m)
         → ZWalk v w zsync → ZWalk (ℓ ∷ v) (m ∷ w) zsync
  zfirstL : ∀ {ℓ m I v w} → Meets ℓ m → Inh (Aᴸ ℓ) → Inh (normᵁ m (I ⊕ᶻ Aᴸ ℓ))
          → ZWalk v w (zinU m (normᵁ m (I ⊕ᶻ Aᴸ ℓ))) → ZWalk (ℓ ∷ v) w (zinU m I)
  zlateU  : ∀ {ℓ m I v w} → Meets ℓ m → Inh (Aᵁ m) → Inh (Aᵁ m ⊖ᶻ I) → Inh (normᴸ ℓ (Aᵁ m ⊖ᶻ I))
          → ZWalk v w (zinL ℓ (normᴸ ℓ (Aᵁ m ⊖ᶻ I))) → ZWalk (ℓ ∷ v) w (zinU m I)
  zbothU  : ∀ {ℓ m I v w} → Meets ℓ m → Inh (Aᴸ ℓ) → Inh ((I ⊕ᶻ Aᴸ ℓ) ∩ᶻ Aᵁ m)
          → ZWalk v w zsync → ZWalk (ℓ ∷ v) w (zinU m I)
  zfirstU : ∀ {ℓ m I v w} → Meets ℓ m → Inh (Aᵁ m) → Inh (normᴸ ℓ (I ⊕ᶻ Aᵁ m))
          → ZWalk v w (zinL ℓ (normᴸ ℓ (I ⊕ᶻ Aᵁ m))) → ZWalk v (m ∷ w) (zinL ℓ I)
  zlateL  : ∀ {ℓ m I v w} → Meets ℓ m → Inh (Aᴸ ℓ) → Inh (Aᴸ ℓ ⊖ᶻ I) → Inh (normᵁ m (Aᴸ ℓ ⊖ᶻ I))
          → ZWalk v w (zinU m (normᵁ m (Aᴸ ℓ ⊖ᶻ I))) → ZWalk v (m ∷ w) (zinL ℓ I)
  zbothL  : ∀ {ℓ m I v w} → Meets ℓ m → Inh (Aᵁ m) → Inh ((I ⊕ᶻ Aᵁ m) ∩ᶻ Aᴸ ℓ)
          → ZWalk v w zsync → ZWalk v (m ∷ w) (zinL ℓ I)

------------------------------------------------------------------------
-- A walk on zones gives a walk

mutual

  zsound : ∀ {v w} → ZWalk v w zsync → Walk v w sync
  zsound zdone            = done
  zsound (zskipL _ a z)   = skipL sync a (zsound z)
  zsound (zskipU _ a z)   = skipU sync a (zsound z)
  zsound (zopop {o} i z) with inhabited i
  ... | t , t∈ = opop (proj₂ (Aᴸ-sound (op o) t∈)) (zsound z)
  zsound (zsyncL {ℓ} {m} mt iA iN z) with zsoundᵁ z iN
  ... | e₂ , e₂∈ , j with normᵁ-sound m iA e₂∈ j
  ...   | t , t∈ , j′ = syncL mt (proj₁ (Aᴸ-sound ℓ t∈)) (proj₂ (Aᴸ-sound ℓ t∈)) j′
  zsound (zsyncU {ℓ} {m} mt iA iN z) with zsoundᴸ z iN
  ... | e₂ , e₂∈ , j with normᴸ-sound ℓ iA e₂∈ j
  ...   | t , t∈ , j′ = syncU mt (proj₁ (Aᵁ-sound m t∈)) (proj₂ (Aᵁ-sound m t∈)) j′
  zsound (zsyncB {ℓ} {m} mt i z) with inhabited i
  ... | t , t∈ with ∩ᶻ-elim {Z = Aᴸ ℓ} t∈
  ...   | tℓ , tm = syncB mt (proj₁ (Aᴸ-sound ℓ tℓ)) (proj₂ (Aᴸ-sound ℓ tℓ)) (proj₂ (Aᵁ-sound m tm))
                      (zsound z)

  zsoundᵁ : ∀ {v w m I} → ZWalk v w (zinU m I) → Inh I → Σ[ e ∈ Carrier ] e ∈ᶻ I × Walk v w (inU m e)
  zsoundᵁ (zskipL _ a z) iI with zsoundᵁ z iI
  ... | e , e∈ , j = e , e∈ , skipL inU a j
  zsoundᵁ {I = I} (zfirstL {ℓ} {m} mt iA iN z) iI with zsoundᵁ z iN
  ... | e₂ , e₂∈ , j with normᵁ-sound m (+-◁ {loᶻ I} {loᶻ (Aᴸ ℓ)} {hiᶻ I} {hiᶻ (Aᴸ ℓ)} iI iA) e₂∈ j
  ...   | s , s∈ , j′ with ⊕ᶻ-complete {Z = I} {W = Aᴸ ℓ} iI iA s∈
  ...     | e , t , e∈ , t∈ , refl =
    e , e∈ , firstL mt (proj₁ (Aᴸ-sound ℓ t∈)) (proj₂ (Aᴸ-sound ℓ t∈)) j′
  zsoundᵁ {I = I} (zlateU {ℓ} {m} mt iA iD iN z) iI with zsoundᴸ z iN
  ... | t₂ , t₂∈ , j with normᴸ-sound ℓ iD t₂∈ j
  ...   | t , t∈ , j′ with ⊖ᶻ-complete {t} {Aᵁ m} {I} iA iI t∈
  ...     | e , e∈ , et∈ =
    e , e∈ , lateU mt (⊖ᶻ-pos {t} {Aᵁ m} {I} t∈) (proj₂ (Aᵁ-sound m et∈)) j′
  zsoundᵁ {I = I} (zbothU {ℓ} {m} mt iA iX z) iI with inhabited iX
  ... | s , s∈ with ∩ᶻ-elim {Z = I ⊕ᶻ Aᴸ ℓ} s∈
  ...   | s₁ , s₂ with ⊕ᶻ-complete {Z = I} {W = Aᴸ ℓ} iI iA s₁
  ...     | e , t , e∈ , t∈ , refl =
    e , e∈ , bothU mt (proj₁ (Aᴸ-sound ℓ t∈)) (proj₂ (Aᴸ-sound ℓ t∈)) (proj₂ (Aᵁ-sound m s₂)) (zsound z)

  zsoundᴸ : ∀ {v w ℓ I} → ZWalk v w (zinL ℓ I) → Inh I → Σ[ e ∈ Carrier ] e ∈ᶻ I × Walk v w (inL ℓ e)
  zsoundᴸ (zskipU _ a z) iI with zsoundᴸ z iI
  ... | e , e∈ , j = e , e∈ , skipU inL a j
  zsoundᴸ {I = I} (zfirstU {ℓ} {m} mt iA iN z) iI with zsoundᴸ z iN
  ... | e₂ , e₂∈ , j with normᴸ-sound ℓ (+-◁ {loᶻ I} {loᶻ (Aᵁ m)} {hiᶻ I} {hiᶻ (Aᵁ m)} iI iA) e₂∈ j
  ...   | s , s∈ , j′ with ⊕ᶻ-complete {Z = I} {W = Aᵁ m} iI iA s∈
  ...     | e , t , e∈ , t∈ , refl =
    e , e∈ , firstU mt (proj₁ (Aᵁ-sound m t∈)) (proj₂ (Aᵁ-sound m t∈)) j′
  zsoundᴸ {I = I} (zlateL {ℓ} {m} mt iA iD iN z) iI with zsoundᵁ z iN
  ... | t₂ , t₂∈ , j with normᵁ-sound m iD t₂∈ j
  ...   | t , t∈ , j′ with ⊖ᶻ-complete {t} {Aᴸ ℓ} {I} iA iI t∈
  ...     | e , e∈ , et∈ =
    e , e∈ , lateL mt (⊖ᶻ-pos {t} {Aᴸ ℓ} {I} t∈) (proj₂ (Aᴸ-sound ℓ et∈)) j′
  zsoundᴸ {I = I} (zbothL {ℓ} {m} mt iA iX z) iI with inhabited iX
  ... | s , s∈ with ∩ᶻ-elim {Z = I ⊕ᶻ Aᵁ m} s∈
  ...   | s₁ , s₂ with ⊕ᶻ-complete {Z = I} {W = Aᵁ m} iI iA s₁
  ...     | e , t , e∈ , t∈ , refl =
    e , e∈ , bothL mt (proj₁ (Aᵁ-sound m t∈)) (proj₂ (Aᴸ-sound ℓ s₂)) (proj₂ (Aᵁ-sound m t∈)) (zsound z)

------------------------------------------------------------------------
-- A walk gives a walk on zones

mutual

  zcomplete : ∀ {v w} → Walk v w sync → ZWalk v w zsync
  zcomplete done            = zdone
  zcomplete (skipL _ a j)   = zskipL zsync a (zcomplete j)
  zcomplete (skipU _ a j)   = zskipU zsync a (zcomplete j)
  zcomplete (opop {o} a j)  = zopop (∈⇒Inh (Aᴸ-complete (op o) (rt-pos o a) a)) (zcomplete j)
  zcomplete (syncL {ℓ} {m} {t} mt pt a j) =
    zsyncL mt (∈⇒Inh t∈) (∈⇒Inh t∈′) (zcompleteᵁ j pt t∈′)
    where
      t∈  = Aᴸ-complete ℓ pt a
      t∈′ = normᵁ-complete m j pt t∈
  zcomplete (syncU {ℓ} {m} {t} mt pt a j) =
    zsyncU mt (∈⇒Inh t∈) (∈⇒Inh t∈′) (zcompleteᴸ j pt t∈′)
    where
      t∈  = Aᵁ-complete m pt a
      t∈′ = normᴸ-complete ℓ j pt t∈
  zcomplete (syncB {ℓ} {m} {t} mt pt a b j) =
    zsyncB mt (∈⇒Inh {t} {Aᴸ ℓ ∩ᶻ Aᵁ m} (∩ᶻ-sound (Aᴸ-complete ℓ pt a) (Aᵁ-complete m pt b))) (zcomplete j)

  zcompleteᵁ : ∀ {v w m e I} → Walk v w (inU m e) → 0ᴰ <ᴰ e → e ∈ᶻ I → ZWalk v w (zinU m I)
  zcompleteᵁ (skipL _ a j) pe e∈ = zskipL zinU a (zcompleteᵁ j pe e∈)
  zcompleteᵁ {m = m} {e} {I} (firstL {ℓ} {t = t} mt pt a j) pe e∈ =
    zfirstL mt (∈⇒Inh t∈) (∈⇒Inh s∈′) (zcompleteᵁ j (+pos pt) s∈′)
    where
      t∈  = Aᴸ-complete ℓ pt a
      s∈′ = normᵁ-complete m j (+pos pt) (⊕ᶻ-sound {Z = I} {W = Aᴸ ℓ} e∈ t∈)
  zcompleteᵁ {m = m} {e} {I} (lateU {ℓ} {t = t} mt pt a j) pe e∈ =
    zlateU mt (∈⇒Inh et∈) (∈⇒Inh t∈) (∈⇒Inh t∈′) (zcompleteᴸ j pt t∈′)
    where
      et∈ = Aᵁ-complete m (+pos pt) a
      t∈  = ⊖ᶻ-sound {C = Aᵁ m} {I} e∈ et∈ pt
      t∈′ = normᴸ-complete ℓ j pt t∈
  zcompleteᵁ {m = m} {e} {I} (bothU {ℓ} {t = t} mt pt a b j) pe e∈ =
    zbothU mt (∈⇒Inh t∈)
      (∈⇒Inh {e +ᴰ t} {(I ⊕ᶻ Aᴸ ℓ) ∩ᶻ Aᵁ m} (∩ᶻ-sound (⊕ᶻ-sound {Z = I} {W = Aᴸ ℓ} e∈ t∈) (Aᵁ-complete m (+pos pt) b)))
      (zcomplete j)
    where
      t∈ = Aᴸ-complete ℓ pt a

  zcompleteᴸ : ∀ {v w ℓ e I} → Walk v w (inL ℓ e) → 0ᴰ <ᴰ e → e ∈ᶻ I → ZWalk v w (zinL ℓ I)
  zcompleteᴸ (skipU _ a j) pe e∈ = zskipU zinL a (zcompleteᴸ j pe e∈)
  zcompleteᴸ {ℓ = ℓ} {e} {I} (firstU {m = m} {t = t} mt pt a j) pe e∈ =
    zfirstU mt (∈⇒Inh t∈) (∈⇒Inh s∈′) (zcompleteᴸ j (+pos pt) s∈′)
    where
      t∈  = Aᵁ-complete m pt a
      s∈′ = normᴸ-complete ℓ j (+pos pt) (⊕ᶻ-sound {Z = I} {W = Aᵁ m} e∈ t∈)
  zcompleteᴸ {ℓ = ℓ} {e} {I} (lateL {m = m} {t = t} mt pt a j) pe e∈ =
    zlateL mt (∈⇒Inh et∈) (∈⇒Inh t∈) (∈⇒Inh t∈′) (zcompleteᵁ j pt t∈′)
    where
      et∈ = Aᴸ-complete ℓ (+pos pt) a
      t∈  = ⊖ᶻ-sound {C = Aᴸ ℓ} {I} e∈ et∈ pt
      t∈′ = normᵁ-complete m j pt t∈
  zcompleteᴸ {ℓ = ℓ} {e} {I} (bothL {m = m} {t = t} mt pt a b j) pe e∈ =
    zbothL mt (∈⇒Inh t∈)
      (∈⇒Inh {e +ᴰ t} {(I ⊕ᶻ Aᵁ m) ∩ᶻ Aᴸ ℓ} (∩ᶻ-sound (⊕ᶻ-sound {Z = I} {W = Aᵁ m} e∈ t∈) (Aᴸ-complete ℓ (+pos pt) a)))
      (zcomplete j)
    where
      t∈ = Aᵁ-complete m pt b

zoned⇔walk : ∀ {v w} → ZWalk v w zsync ⇔ Walk v w sync
zoned⇔walk = mk⇔ zsound zcomplete
