------------------------------------------------------------------------
-- The duration hull of an expression: the least interval holding the --
-- durations of the exact words it denotes.                           --
--                                                                    --
-- `hull e` is computed by recursion on `e`: the empty word is the    --
-- point zero, an operation set the hull of its running times, a      --
-- stretch the lengths its end admits, union the hull of the union,   --
-- concatenation the sum of intervals, iteration the closure joined   --
-- with zero. `nothing` stands for the empty set of durations.        --
--                                                                    --
-- In any time domain the hull is sound: every word of `e` lasts a    --
-- duration it admits (`hull-sound`). In a dense one, for an          --
-- expression without iteration, it is the least such interval        --
-- (`hull-least`): every duration it admits lies between two          --
-- durations of words of `e` (`hull-reach`); with iteration it is     --
-- the least too once the domain is Archimedean, a word of positive   --
-- duration repeated outlasting every duration (`Iterated`). Fitting  --
-- preserves durations, so where the hull is least it is monotone in  --
-- the order on sets of words (`hull-mono`, `hull-mono*`).            --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Durations
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List.Base using (List; []; _∷_; _++_; allFin)
open import Data.Nat.Base using (zero; suc)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (fromWitness)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T renaming (_∣_ to _∣ᶜ_)
open import Grades.Durations.Intervals.Dense T
  using (_∈ⁱ_; ⊆ⁱ-sound; ⊕-sound; ⁺⋢⁻; pointⁱ-∈; module Exact)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective using (⊑-dur)
open import Grades.Exact.Lift T Op n code code-injective using (Lang; _≾_)
open import Grades.Exact.Expression T Op n code code-injective running

open RunningTimes.RunningTimes running using (rt; rt-pos)
open import Grades.Exact.Grid T using (Archimedean; _×ᴰ_)

------------------------------------------------------------------------
-- Possibly empty intervals

Hull : Set
Hull = Maybe Interval

infix 4 _∈ʰ_
infixl 6 _∪ʰ_
infixl 7 _⊕ʰ_

_∈ʰ_ : Carrier → Hull → Set
t ∈ʰ nothing = ⊥
t ∈ʰ just i  = t ∈ⁱ i

_∪ʰ_ : Hull → Hull → Hull
nothing ∪ʰ m       = m
just i  ∪ʰ nothing = just i
just i  ∪ʰ just j  = just (i ∪ⁱ j)

_⊕ʰ_ : Hull → Hull → Hull
just i ⊕ʰ just j = just (i ⊕ j)
_      ⊕ʰ _      = nothing

starʰ : Hull → Hull
starʰ nothing  = just 0ⁱ
starʰ (just i) = just (0ⁱ ∪ⁱ i⁺ i)

------------------------------------------------------------------------
-- The hull

-- the lengths an upper end admits, from zero

upperʰ : (h : Hi) → Dec (0⁻ ◁ h) → Hull
upperʰ h (yes p) = just (⟪ 0⁻ , h ⟫ {fromWitness p})
upperʰ h (no _)  = nothing

strʰ : (s : Instance) → End s → Hull
strʰ upper h = upperʰ h (0⁻ ◁? h)
strʰ lower c = just ⟪ c , ∞ ⟫

-- the running times of an operation of a set

guardʰ : ∀ {P : Set} → Dec P → Interval → Hull
guardʰ (yes _) i = just i
guardʰ (no _)  _ = nothing

opʰ : OpSet → Fin n → Hull
opʰ A c = guardʰ (c ∈? A) (rt (name c))

⋃ʰ : List (Fin n) → (Fin n → Hull) → Hull
⋃ʰ []       f = nothing
⋃ʰ (c ∷ cs) f = f c ∪ʰ ⋃ʰ cs f

hull : ∀ {s} → Expr s → Hull
hull ε             = just 0ⁱ
hull (ops A)       = ⋃ʰ (allFin n) (opʰ A)
hull {s} (str S e) = strʰ s e
hull (e ∣ f)       = hull e ∪ʰ hull f
hull (e · f)       = hull e ⊕ʰ hull f
hull (e *)         = starʰ (hull e)

------------------------------------------------------------------------
-- Soundness

private
  ∪ʰ-ubˡ : ∀ m m′ {t} → t ∈ʰ m → t ∈ʰ m ∪ʰ m′
  ∪ʰ-ubˡ (just i) nothing  t∈ = t∈
  ∪ʰ-ubˡ (just i) (just j) t∈ = ⊆ⁱ-sound {i} {i ∪ⁱ j} (∪ⁱ-ubˡ i j) t∈

  ∪ʰ-ubʳ : ∀ m m′ {t} → t ∈ʰ m′ → t ∈ʰ m ∪ʰ m′
  ∪ʰ-ubʳ nothing  m′       t∈ = t∈
  ∪ʰ-ubʳ (just i) (just j) t∈ = ⊆ⁱ-sound {j} {i ∪ⁱ j} (∪ⁱ-ubʳ i j) t∈

  ⊕ʰ-sound : ∀ m m′ {a b} → a ∈ʰ m → b ∈ʰ m′ → a +ᴰ b ∈ʰ m ⊕ʰ m′
  ⊕ʰ-sound (just i) (just j) a∈ b∈ = ⊕-sound {i} {j} a∈ b∈

  0∈0ⁱ : 0ᴰ ∈ⁱ 0ⁱ
  0∈0ⁱ = ⊑-refl , ⊑-refl

  -- a cut above `t ∣ ⁺` is above `0 ∣ ⁻`
  upper-inhabited : ∀ h {t} → fin (t ∣ᶜ ⁺) ⊑ʰ h → 0⁻ ◁ h
  upper-inhabited (fin c) {t} r q = ⁺⋢⁻ (⊑-trans r (⊑-trans q (0⁻-least (t ∣ᶜ ⁻))))
  upper-inhabited ∞       r = tt

  str-sound : ∀ {s} S (e : End s) {x} → strᴸ S e x → dur x ∈ʰ strʰ s e
  str-sound {upper} S h {x} (τ , r , refl) = case (0⁻ ◁? h)
    where
      case : (d : Dec (0⁻ ◁ h)) → dur (stretch S τ) ∈ʰ upperʰ h d
      case (yes _) rewrite dur-stretch S τ = 0⁻-least _ , r
      case (no ¬p) = ¬p (upper-inhabited h r)
  str-sound {lower} S c (τ , r , refl) rewrite dur-stretch S τ = r , tt

  -- `name` inverts `code`
  name-code : ∀ o → name (code o) ≡ o
  name-code o = code-injective (code-name (code o))

  ⋃ʰ-complete : ∀ cs f {c t} → c ∈ˡ cs → t ∈ʰ f c → t ∈ʰ ⋃ʰ cs f
  ⋃ʰ-complete (c ∷ cs) f (here refl) t∈ = ∪ʰ-ubˡ (f c) (⋃ʰ cs f) t∈
  ⋃ʰ-complete (d ∷ cs) f (there c∈)  t∈ = ∪ʰ-ubʳ (f d) (⋃ʰ cs f) (⋃ʰ-complete cs f c∈ t∈)

  dur-op : ∀ o d → dur (op o d ∷ []) ≡ ∣ d ∣⁺
  dur-op o d = +ᴰ-identityʳ ∣ d ∣⁺

  ops-sound : ∀ A {x} → opsᴸ A x → dur x ∈ʰ ⋃ʰ (allFin n) (opʰ A)
  ops-sound A (o , d , c∈ , t∈ , refl) =
    ⋃ʰ-complete (allFin n) (opʰ A) (∈-allFin (code o)) (case (code o ∈? A))
    where
      case : (q : Dec (code o ∈ A)) → dur (op o d ∷ []) ∈ʰ guardʰ q (rt (name (code o)))
      case (yes _) rewrite dur-op o d | name-code o = t∈
      case (no ¬q) = ¬q c∈

  -- the closure absorbs a summand of the hull
  ⊆-star : ∀ i → i ⊕ (0ⁱ ∪ⁱ i⁺ i) ⊆ⁱ 0ⁱ ∪ⁱ i⁺ i
  ⊆-star i =
    ⊆ⁱ-trans {i ⊕ (0ⁱ ∪ⁱ i⁺ i)} {(i ⊕ 0ⁱ) ∪ⁱ (i ⊕ i⁺ i)} {0ⁱ ∪ⁱ i⁺ i}
      (⊕-distribˡ-∪ⁱ i 0ⁱ (i⁺ i))
      (∪ⁱ-lub {i ⊕ 0ⁱ} {i ⊕ i⁺ i} {0ⁱ ∪ⁱ i⁺ i} (subst (_⊆ⁱ 0ⁱ ∪ⁱ i⁺ i) (sym (⊕-identityʳ i))
                (⊆ⁱ-trans {i} {i⁺ i} {0ⁱ ∪ⁱ i⁺ i} (⊑-refl , ⊑ʰ-plusʰ (hi i)) (∪ⁱ-ubʳ 0ⁱ (i⁺ i))))
              (⊆ⁱ-trans {i ⊕ i⁺ i} {i⁺ i} {0ⁱ ∪ⁱ i⁺ i}
                 (+ˡ-inflate (lo i) (lo i) ,
                  ⊑ʰ-trans {hi i +ʰ plusʰ (hi i)}
                    (+ʰ-monoˡ (plusʰ (hi i)) (⊑ʰ-plusʰ (hi i)))
                    (plusʰ-iter {hi i} (◁⇒0⁺⊑ʰ {lo i} {hi i} (lo◁hi i))))
                 (∪ⁱ-ubʳ 0ⁱ (i⁺ i))))

hull-sound : ∀ {s} (e : Expr s) {x} → ⟦ e ⟧ x → dur x ∈ʰ hull e
hull-sound ε         refl = 0∈0ⁱ
hull-sound (ops A)   x∈   = ops-sound A x∈
hull-sound (str S e) x∈   = str-sound S e x∈
hull-sound (e ∣ f)   (inj₁ x∈) = ∪ʰ-ubˡ (hull e) (hull f) (hull-sound e x∈)
hull-sound (e ∣ f)   (inj₂ x∈) = ∪ʰ-ubʳ (hull e) (hull f) (hull-sound f x∈)
hull-sound (e · f)   (x , y , refl , x∈ , y∈) rewrite dur-++ x y =
  ⊕ʰ-sound (hull e) (hull f) (hull-sound e x∈) (hull-sound f y∈)
hull-sound (e *)     x∈ = star (hull e) refl x∈
  where
    star : ∀ m → hull e ≡ m → ∀ {y} → Star ⟦ e ⟧ y → dur y ∈ʰ starʰ m
    star nothing  _  stop = 0∈0ⁱ
    star (just i) _  stop = ∪ʰ-ubˡ (just 0ⁱ) (just (i⁺ i)) 0∈0ⁱ
    star m        eq (more {x} {y} x∈ ys) with subst (dur x ∈ʰ_) eq (hull-sound e x∈)
    star (just i) eq (more {x} {y} x∈ ys) | x∈′ rewrite dur-++ x y =
      ⊆ⁱ-sound {i ⊕ (0ⁱ ∪ⁱ i⁺ i)} {0ⁱ ∪ⁱ i⁺ i} (⊆-star i)
        (⊕-sound {i} {0ⁱ ∪ⁱ i⁺ i} x∈′ (star (just i) eq ys))

-- an expression with a word has an interval as its hull

theʰ : (m : Hull) {t : Carrier} → t ∈ʰ m → Interval
theʰ (just i) _ = i

theʰ-≡ : (m : Hull) {t : Carrier} (p : t ∈ʰ m) → m ≡ just (theʰ m p)
theʰ-≡ (just i) _ = refl

hullOf : ∀ {s} (e : Expr s) → ∃ ⟦ e ⟧ → Interval
hullOf e (x , x∈) = theʰ (hull e) (hull-sound e x∈)

hullOf-≡ : ∀ {s} (e : Expr s) (w : ∃ ⟦ e ⟧) → hull e ≡ just (hullOf e w)
hullOf-≡ e (x , x∈) = theʰ-≡ (hull e) (hull-sound e x∈)

------------------------------------------------------------------------
-- The durations of a set of words

Durs : Lang → Carrier → Set
Durs X t = Σ[ x ∈ Word ] X x × dur x ≡ t

-- an expression without iteration

NoStar : ∀ {s} → Expr s → Set
NoStar ε         = ⊤
NoStar (ops _)   = ⊤
NoStar (str _ _) = ⊤
NoStar (e ∣ f)   = NoStar e × NoStar f
NoStar (e · f)   = NoStar e × NoStar f
NoStar (e *)     = ⊥

-- a duration between two that an interval admits is admitted

between-∈ : ∀ {i a b t} → a ∈ⁱ i → b ∈ⁱ i → a ≤ᴰ t → t ≤ᴰ b → t ∈ⁱ i
between-∈ {i} {a} {b} {t} (ra , _) (_ , rb) a≤t t≤b =
  ⊑-trans ra (≤⇒⁻⊑⁻ a≤t) , ⊑ʰ-trans {fin (t ∣ᶜ ⁺)} {fin (b ∣ᶜ ⁺)} {hi i} (≤⇒⁺⊑⁺ t≤b) rb

------------------------------------------------------------------------
-- In a dense time domain the hull is the least interval

module Least (dense : Dense T) (κ : Carrier) (κ-pos : 0ᴰ <ᴰ κ) where

  open Exact dense κ κ-pos using (inhabited; ⊆ⁱ-complete; ⊕-complete)

  -- every duration above a lower end is above a duration of `P`, and
  -- every duration below an upper end below one

  LoReach : (Carrier → Set) → Cut → Set
  LoReach P c = ∀ {t} → c ⊑ (t ∣ᶜ ⁻) → Σ[ a ∈ Carrier ] P a × a ≤ᴰ t

  HiReach : (Carrier → Set) → Hi → Set
  HiReach P h = ∀ {t} → fin (t ∣ᶜ ⁺) ⊑ʰ h → Σ[ b ∈ Carrier ] P b × t ≤ᴰ b

  Reaches : (Carrier → Set) → Hull → Set
  Reaches P nothing  = ⊤
  Reaches P (just i) = LoReach P (lo i) × HiReach P (hi i)

  private
    reach-mono : ∀ {P Q : Carrier → Set} m → (∀ {t} → P t → Q t) → Reaches P m → Reaches Q m
    reach-mono nothing  f _       = tt
    reach-mono (just i) f (l , h) =
      (λ r → let (a , pa , le) = l r in a , f pa , le) ,
      (λ r → let (b , pb , le) = h r in b , f pb , le)

    -- an interval reaches what it admits
    interval-reach : ∀ i → Reaches (_∈ⁱ i) (just i)
    interval-reach i = lo-part , hi-part
      where
        lo-part : LoReach (_∈ⁱ i) (lo i)
        lo-part {t} r with fin (t ∣ᶜ ⁺) ⊑ʰ? hi i
        ... | yes q = t , (r , q) , ≤ᴰ-refl
        ... | no ¬q with hi i | inhabited i
        ...   | ∞     | _ = ⊥-elim (¬q tt)
        ...   | fin c | s , s∈ =
          s , s∈ , ⊑⇒≤ (⊑-trans {s ∣ᶜ ⁺} {c} {t ∣ᶜ ⁺} (proj₂ s∈) (⊏⇒⊑ ¬q))
        hi-part : HiReach (_∈ⁱ i) (hi i)
        hi-part {t} r with lo i ⊑? (t ∣ᶜ ⁻)
        ... | yes q = t , (q , r) , ≤ᴰ-refl
        ... | no ¬q with inhabited i
        ...   | s , s∈ = s , s∈ , ⊑⇒≤ (⊑-trans (⊏⇒⊑ ¬q) (proj₁ s∈))

    ∪ʰ-reach : ∀ {P Q : Carrier → Set} m m′ → Reaches P m → Reaches Q m′
             → Reaches (λ t → P t ⊎ Q t) (m ∪ʰ m′)
    ∪ʰ-reach nothing  m′       _ q = reach-mono m′ inj₂ q
    ∪ʰ-reach (just i) nothing  p _ = reach-mono (just i) inj₁ p
    ∪ʰ-reach (just i) (just j) (pl , ph) (ql , qh) = lo-part , hi-part
      where
        lo-part : LoReach _ (lo i ⊓ᶜ lo j)
        lo-part {t} r with ⊓ᶜ-sel (lo i) (lo j)
        ... | inj₁ e = let (a , pa , le) = pl (subst (_⊑ (t ∣ᶜ ⁻)) e r) in a , inj₁ pa , le
        ... | inj₂ e = let (a , qa , le) = ql (subst (_⊑ (t ∣ᶜ ⁻)) e r) in a , inj₂ qa , le
        hi-part : HiReach _ (hi i ⊔ʰ hi j)
        hi-part {t} r with ⊔ʰ-sel (hi i) (hi j)
        ... | inj₁ e = let (b , pb , le) = ph (subst (fin (t ∣ᶜ ⁺) ⊑ʰ_) e r) in b , inj₁ pb , le
        ... | inj₂ e = let (b , qb , le) = qh (subst (fin (t ∣ᶜ ⁺) ⊑ʰ_) e r) in b , inj₂ qb , le

  -- the sums of durations of two sets

  _⊞_ : (Carrier → Set) → (Carrier → Set) → Carrier → Set
  (P ⊞ Q) t = Σ[ a ∈ Carrier ] Σ[ b ∈ Carrier ] P a × Q b × a +ᴰ b ≡ t

  private
    0⁻◁ : ∀ i → 0⁻ ◁ hi i
    0⁻◁ i = ⊑-◁-trans {0⁻} {lo i} {hi i} (0⁻-least (lo i)) (lo◁hi i)

    ⊕ʰ-reach : ∀ {P Q : Carrier → Set} m m′ → Reaches P m → Reaches Q m′
             → Reaches (P ⊞ Q) (m ⊕ʰ m′)
    ⊕ʰ-reach nothing  _        _ _ = tt
    ⊕ʰ-reach (just i) nothing  _ _ = tt
    ⊕ʰ-reach (just i) (just j) (pl , ph) (ql , qh) = lo-part , hi-part
      where
        lo-part : LoReach _ (lo i +ˡ lo j)
        lo-part {t} r
          with ⊕-complete {⟪ lo i , ∞ ⟫} {⟪ lo j , ∞ ⟫} {t} (r , tt)
        ... | x , y , x∈ , y∈ , e
          with pl (proj₁ x∈) | ql (proj₁ y∈)
        ...   | a , pa , a≤ | b , qb , b≤ =
          a +ᴰ b , (a , b , pa , qb , refl) ,
          subst (a +ᴰ b ≤ᴰ_) e (+ᴰ-mono-≤ a≤ b≤)
        hi-part : HiReach _ (hi i +ʰ hi j)
        hi-part {t} r
          with ⊕-complete {⟪ 0⁻ , hi i ⟫ {fromWitness (0⁻◁ i)}}
                          {⟪ 0⁻ , hi j ⟫ {fromWitness (0⁻◁ j)}} {t}
                 (subst (_⊑ (t ∣ᶜ ⁻)) (sym (+ˡ-identityˡ 0⁻)) (0⁻-least _) , r)
        ... | x , y , x∈ , y∈ , e
          with ph (proj₂ x∈) | qh (proj₂ y∈)
        ...   | a , pa , x≤ | b , qb , y≤ =
          a +ᴰ b , (a , b , pa , qb , refl) ,
          subst (_≤ᴰ a +ᴰ b) e (+ᴰ-mono-≤ x≤ y≤)

    ⋃ʰ-reach : ∀ {P : Carrier → Set} cs (f : Fin n → Hull)
             → (∀ c → Reaches P (f c)) → Reaches P (⋃ʰ cs f)
    ⋃ʰ-reach []       f g = tt
    ⋃ʰ-reach (c ∷ cs) f g =
      reach-mono (f c ∪ʰ ⋃ʰ cs f) (λ { (inj₁ p) → p ; (inj₂ p) → p })
        (∪ʰ-reach (f c) (⋃ʰ cs f) (g c) (⋃ʰ-reach cs f g))

    op-reach : ∀ A c → Reaches (Durs ⟦ ops {upper} A ⟧) (opʰ A c)
    op-reach A c with c ∈? A
    ... | no _   = tt
    ... | yes c∈ = reach-mono (just (rt (name c))) word (interval-reach (rt (name c)))
      where
        word : ∀ {t} → t ∈ⁱ rt (name c) → Durs ⟦ ops {upper} A ⟧ t
        word {t} t∈ =
          op (name c) d ∷ [] ,
          (name c , d , subst (_∈ A) (sym (code-name c)) c∈ , t∈ , refl) ,
          dur-op (name c) d
          where
            d : D⁺
            d = pos⁺ t (rt-pos (name c) t∈)

    -- the operation sets mean the same in both instances
    ops-reach : ∀ {s} A → Reaches (Durs ⟦ ops {s} A ⟧) (⋃ʰ (allFin n) (opʰ A))
    ops-reach {upper} A = ⋃ʰ-reach (allFin n) (opʰ A) (op-reach A)
    ops-reach {lower} A = ⋃ʰ-reach (allFin n) (opʰ A) (op-reach A)

    str-reach : ∀ {s} S (e : End s) → Reaches (Durs ⟦ str S e ⟧) (strʰ s e)
    str-reach {upper} S h = case (0⁻ ◁? h)
      where
        case : (d : Dec (0⁻ ◁ h)) → Reaches (Durs ⟦ str S h ⟧) (upperʰ h d)
        case (yes p) =
          reach-mono (just (⟪ 0⁻ , h ⟫ {fromWitness p}))
            (λ {t} t∈ → stretch S t , (t , proj₂ t∈ , refl) , dur-stretch S t)
            (interval-reach (⟪ 0⁻ , h ⟫ {fromWitness p}))
        case (no _) = tt
    str-reach {lower} S c =
      reach-mono (just ⟪ c , ∞ ⟫)
        (λ {t} t∈ → stretch S t , (t , proj₁ t∈ , refl) , dur-stretch S t)
        (interval-reach ⟪ c , ∞ ⟫)

  hull-reach : ∀ {s} (e : Expr s) → NoStar e → Reaches (Durs ⟦ e ⟧) (hull e)
  hull-reach ε _ =
    reach-mono (just 0ⁱ) (λ {t} t∈ → [] , refl , sym (pointⁱ-∈ t∈)) (interval-reach 0ⁱ)
  hull-reach {s} (ops A) _ = ops-reach {s} A
  hull-reach (str S e) _ = str-reach S e
  hull-reach (e ∣ f) (ne , nf) =
    reach-mono (hull e ∪ʰ hull f)
      (λ { (inj₁ (x , x∈ , d)) → x , inj₁ x∈ , d ; (inj₂ (x , x∈ , d)) → x , inj₂ x∈ , d })
      (∪ʰ-reach (hull e) (hull f) (hull-reach e ne) (hull-reach f nf))
  hull-reach (e · f) (ne , nf) =
    reach-mono (hull e ⊕ʰ hull f)
      (λ { (a , b , (x , x∈ , refl) , (y , y∈ , refl) , refl) →
             x ++ y , (x , y , refl , x∈ , y∈) , dur-++ x y })
      (⊕ʰ-reach (hull e) (hull f) (hull-reach e ne) (hull-reach f nf))

  -- the hull lies within every interval admitting the durations, once
  -- it reaches them

  reach-least : ∀ {s} (e : Expr s) → Reaches (Durs ⟦ e ⟧) (hull e) → ∀ {i} → hull e ≡ just i
              → (j : Interval) → (∀ {x} → ⟦ e ⟧ x → dur x ∈ⁱ j) → i ⊆ⁱ j
  reach-least e r {i} eq j f = ⊆ⁱ-complete {i} {j} λ {t} t∈ → go (hull e) eq r t∈
    where
      go : ∀ m → m ≡ just i → Reaches (Durs ⟦ e ⟧) m → ∀ {t} → t ∈ⁱ i → t ∈ⁱ j
      go (just .i) refl (l , h) {t} t∈ with l (proj₁ t∈) | h (proj₂ t∈)
      ... | a , (x , x∈ , refl) , a≤ | b , (y , y∈ , refl) , ≤b =
        between-∈ {j} (f x∈) (f y∈) a≤ ≤b

  hull-least : ∀ {s} (e : Expr s) → NoStar e → ∀ {i} → hull e ≡ just i
             → (j : Interval) → (∀ {x} → ⟦ e ⟧ x → dur x ∈ⁱ j) → i ⊆ⁱ j
  hull-least e ne = reach-least e (hull-reach e ne)

  -- the hull is monotone in the order on sets of words, once it
  -- reaches the durations of the lesser set

  reach-mono-hull : ∀ {s s′} (e : Expr s) (f : Expr s′) → Reaches (Durs ⟦ e ⟧) (hull e)
                  → ⟦ e ⟧ ≾ ⟦ f ⟧ → ∀ {i j} → hull e ≡ just i → hull f ≡ just j → i ⊆ⁱ j
  reach-mono-hull e f r le {i} {j} eqe eqf = reach-least e r eqe j into
    where
      into : ∀ {x} → ⟦ e ⟧ x → dur x ∈ⁱ j
      into {x} x∈ with le x x∈
      ... | y , y∈ , x⊑y =
        subst (_∈ⁱ j) (sym (⊑-dur x⊑y)) (subst (dur y ∈ʰ_) eqf (hull-sound f y∈))

  hull-mono : ∀ {s s′} (e : Expr s) (f : Expr s′) → NoStar e
            → ⟦ e ⟧ ≾ ⟦ f ⟧ → ∀ {i j} → hull e ≡ just i → hull f ≡ just j → i ⊆ⁱ j
  hull-mono e f ne = reach-mono-hull e f (hull-reach e ne)

  --------------------------------------------------------------------
  -- With iteration, in an Archimedean time domain: a word of positive
  -- duration, repeated, outlasts every duration

  module Iterated (archimedean : Archimedean) where

    private
      copies : ℕ → Word → Word
      copies zero    y = []
      copies (suc k) y = y ++ copies k y

      copies-∈ : ∀ {X : Lang} {y} k → X y → Star X (copies k y)
      copies-∈ zero    _  = stop
      copies-∈ (suc k) y∈ = more y∈ (copies-∈ k y∈)

      copies-dur : ∀ k y → dur (copies k y) ≡ k ×ᴰ dur y
      copies-dur zero    y = refl
      copies-dur (suc k) y = trans (dur-++ y (copies k y)) (cong (dur y +ᴰ_) (copies-dur k y))

      -- a positive length reached below a positive upper end
      positive : ∀ h → ¬ (h ⊑ʰ fin 0⁺) → Σ[ t ∈ Carrier ] 0ᴰ <ᴰ t × fin (t ∣ᶜ ⁺) ⊑ʰ h
      positive ∞ _ = κ , κ-pos , tt
      positive (fin (p ∣ᶜ s)) ¬h with dense {0ᴰ} {p} p-pos
        where
          p-pos : ¬ (p ≤ᴰ 0ᴰ)
          p-pos p≤0 = ¬h (subst (λ z → (z ∣ᶜ s) ⊑ 0⁺) (sym (≤0⇒≡0 p≤0)) (by-side refl ≤ˢ-⁺))
      ... | t , t-pos , t<p = t , t-pos , by-pt t<p

      star-reach : ∀ {X : Lang} m → Reaches (Durs X) m → Reaches (Durs (Star X)) (starʰ m)
      star-reach {X} nothing _ =
        reach-mono (just 0ⁱ) (λ {t} t∈ → [] , stop , sym (pointⁱ-∈ t∈)) (interval-reach 0ⁱ)
      star-reach {X} (just i) (_ , hr) = lo-part , hi-part
        where
          lo-part : LoReach (Durs (Star X)) (lo (0ⁱ ∪ⁱ i⁺ i))
          lo-part {t} _ = 0ᴰ , ([] , stop , refl) , 0ᴰ-least t
          unbounded : ¬ (hi i ⊑ʰ fin 0⁺) → ∀ t → Σ[ b ∈ Carrier ] Durs (Star X) b × t ≤ᴰ b
          unbounded ¬h t with positive (hi i) ¬h
          ... | t₀ , t₀-pos , r with hr r
          ...   | b , (y , y∈ , refl) , t₀≤b with archimedean (dur y) t (<-≤-trans t₀-pos t₀≤b)
          ...     | k , t≤ = k ×ᴰ dur y , (copies k y , copies-∈ k y∈ , copies-dur k y) , t≤
          hi-part : HiReach (Durs (Star X)) (hi (0ⁱ ∪ⁱ i⁺ i))
          hi-part {t} r with ⊔ʰ-sel (fin 0⁺) (plusʰ (hi i))
          ... | inj₁ e = 0ᴰ , ([] , stop , refl) , ⊑⇒≤ (subst (fin (t ∣ᶜ ⁺) ⊑ʰ_) e r)
          ... | inj₂ e with hi i in ehi
          ...   | ∞ = unbounded (λ q → subst (_⊑ʰ fin 0⁺) ehi q) t
          ...   | fin c with c ⊑? 0⁺
          ...     | no ¬q = unbounded (λ q → ¬q (subst (_⊑ʰ fin 0⁺) ehi q)) t
          ...     | yes _ with hr {t} (subst (fin (t ∣ᶜ ⁺) ⊑ʰ_) e r)
          ...       | b , (y , y∈ , refl) , t≤ = dur y , (y ++ [] , more y∈ stop , dur-++-[] y) , t≤
            where
              dur-++-[] : ∀ y → dur (y ++ []) ≡ dur y
              dur-++-[] y = trans (dur-++ y []) (+ᴰ-identityʳ (dur y))

    -- the hull reaches the durations of every expression

    hull-reach* : ∀ {s} (e : Expr s) → Reaches (Durs ⟦ e ⟧) (hull e)
    hull-reach* ε =
      reach-mono (just 0ⁱ) (λ {t} t∈ → [] , refl , sym (pointⁱ-∈ t∈)) (interval-reach 0ⁱ)
    hull-reach* {s} (ops A) = ops-reach {s} A
    hull-reach* (str S e) = str-reach S e
    hull-reach* (e ∣ f) =
      reach-mono (hull e ∪ʰ hull f)
        (λ { (inj₁ (x , x∈ , d)) → x , inj₁ x∈ , d ; (inj₂ (x , x∈ , d)) → x , inj₂ x∈ , d })
        (∪ʰ-reach (hull e) (hull f) (hull-reach* e) (hull-reach* f))
    hull-reach* (e · f) =
      reach-mono (hull e ⊕ʰ hull f)
        (λ { (a , b , (x , x∈ , refl) , (y , y∈ , refl) , refl) →
               x ++ y , (x , y , refl , x∈ , y∈) , dur-++ x y })
        (⊕ʰ-reach (hull e) (hull f) (hull-reach* e) (hull-reach* f))
    hull-reach* (e *) = star-reach (hull e) (hull-reach* e)

    hull-least* : ∀ {s} (e : Expr s) → ∀ {i} → hull e ≡ just i
                → (j : Interval) → (∀ {x} → ⟦ e ⟧ x → dur x ∈ⁱ j) → i ⊆ⁱ j
    hull-least* e = reach-least e (hull-reach* e)

    hull-mono* : ∀ {s s′} (e : Expr s) (f : Expr s′)
               → ⟦ e ⟧ ≾ ⟦ f ⟧ → ∀ {i j} → hull e ≡ just i → hull f ≡ just j → i ⊆ⁱ j
    hull-mono* e f = reach-mono-hull e f (hull-reach* e)
