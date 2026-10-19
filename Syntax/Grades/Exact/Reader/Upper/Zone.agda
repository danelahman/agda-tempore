------------------------------------------------------------------------
-- Exact runs near the extremal one read as it does.                  --
--                                                                    --
-- Each piece of a word ranges over an interval, its box: a stretch   --
-- over lengths above zero within its end, an operation over its      --
-- running times. The upper reader reads a piece at the upper end of  --
-- its box. For finitely many comparisons against given bounds there  --
-- is a choice of a length in every box such that every comparison    --
-- the extremal reading fails, the exact reading fails too: each      --
-- failing comparison asks for some length large enough, density      --
-- supplies one inside the box, and the largest of them serves all.   --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Reader.Upper.Zone
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; foldr; [_]; zipWith; concatMap)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Cut; Hi; fin; ∞; _⊑_; _⊏_; _⊑ʰ_; _⊑ʰ?_; ⁺; ⁻; 0⁺; 0⁻; _+ʰ_; ⊑⇒≤; ≤⇒⁺⊑⁺;
         by-pt; by-side; ⊑ʰ-trans; ⊑ʰ-∞; +ʰ-mono; +ʰ-monoˡ; +ʰ-monoʳ; +ʰ-assoc; +ʰ-identityʳ;
         Interval; lo; hi; lo◁hi; _◁_; _⊔ᶜ_; ⊔ᶜ-ubˡ; ⊔ᶜ-ubʳ; ⊏-cases; ⊏-by-pt; 0⁻-least;
         ⊑-⊏-trans; ⊑-trans; ⊑-refl; ≤⇒⁻⊑⁻; ⁻≤; 0⁻⊏⇒0⁺⊑; +ʰ-identityˡ)
  renaming (_∣_ to _∣ᶜ_)
open import Syntax.Durations.Intervals.Dense T using (_∈ⁱ_; ⊔-◁; ⊑⁻⇒<; module Exact)
open Exact dense κ κ-pos using (between; inhabited)

open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Upper T Op n code code-injective running

private
  π₁ = proj₁
  π₂ = proj₂

  variable
    a b c : Carrier

  ≮⇒≥ : ¬ (a <ᴰ b) → b ≤ᴰ a
  ≮⇒≥ {a} {b} ¬p with b ≤ᴰ? a
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

  -- a closed end past the point of a bound is not below it
  past : ∀ {c t p u} → c <ᴰ p → ¬ (fin (p ∣ᶜ u) ⊑ʰ fin (c ∣ᶜ t))
  past r s = r (⊑⇒≤ s)

  -- below the upper end of an interval, closed: its point is admitted
  closed-end : ∀ {l w} → l ◁ fin (w ∣ᶜ ⁺) → l ⊑ (w ∣ᶜ ⁻)
  closed-end r with ⊏-cases r
  ... | inj₁ a             = by-pt a
  ... | inj₂ (e , refl , _) = by-side e ⁻≤

  -- an open upper end above a lower one is above zero
  open-pos : ∀ {l w} → l ◁ fin (w ∣ᶜ ⁻) → 0ᴰ <ᴰ w
  open-pos {l} r = ⊑⁻⇒< (⊑-trans (0⁺⊑ (⊑-⊏-trans (0⁻-least l) r)) ⊑-refl) refl
    where
      0⁺⊑ : ∀ {c} → 0⁻ ⊏ c → (0ᴰ ∣ᶜ ⁺) ⊑ c
      0⁺⊑ = 0⁻⊏⇒0⁺⊑

------------------------------------------------------------------------
-- One failing comparison, kept failing by a length inside the box

-- `cl A +ʰ hi b +ʰ S` against `C`, with the piece read at a length `θ`

Fails : Carrier → Hi → Hi → Carrier → Set
Fails A S C θ = ¬ (cl A +ʰ cl θ +ʰ S ⊑ʰ C)

fails-mono : ∀ {A S C θ θ′} → θ ≤ᴰ θ′ → Fails A S C θ → Fails A S C θ′
fails-mono {A} {S} {C} r f t = f (⊑ʰ-trans (+ʰ-monoˡ S (+ʰ-monoʳ (cl A) (≤⇒⁺⊑⁺ r))) t)

witness : ∀ b A S C → ¬ (cl A +ʰ hi b +ʰ S ⊑ʰ C) → Σ[ θ ∈ Carrier ] θ ∈ⁱ b × Fails A S C θ
witness b A S ∞ f = ⊥-elim (f (⊑ʰ-∞ _))
witness b A ∞ (fin c′) f with inhabited b
... | θ , m = θ , m , λ t → subst (λ h → h ⊑ʰ fin c′) (+ʰ-∞′ (cl A +ʰ cl θ)) t
  where
    +ʰ-∞′ : ∀ h → h +ʰ ∞ ≡ ∞
    +ʰ-∞′ (fin (_ ∣ᶜ _)) = refl
    +ʰ-∞′ ∞             = refl
witness b A (fin (s ∣ᶜ u)) (fin (c ∣ᶜ t)) f with hi b in eh | lo◁hi b
... | ∞ | _ with between {lo b ⊔ᶜ (c ∣ᶜ ⁺)} {∞} tt
...   | x , r , _ =
  x , (⊑-trans (⊔ᶜ-ubˡ (lo b) _) r , tt) ,
  past (<-≤-trans (⊑⁻⇒< (⊑-trans (⊔ᶜ-ubʳ (lo b) _) r) refl)
                  (≤ᴰ-trans (≤ᴰ-+ˡ x A) (≤ᴰ-+ (A +ᴰ x) s)))
witness b A (fin (s ∣ᶜ u)) (fin (c ∣ᶜ t)) f | fin (w ∣ᶜ ⁺) | l◁ =
  w , (closed-end l◁ , ⊑-refl) , f
witness b A (fin (s ∣ᶜ u)) (fin (c ∣ᶜ t)) f | fin (w ∣ᶜ ⁻) | l◁
  with between {lo b ⊔ᶜ ((c ∸ᴰ (A +ᴰ s)) ∣ᶜ ⁺)} {fin (w ∣ᶜ ⁻)}
         (⊔-◁ {lo b} l◁ (⊏-by-pt (r<w (A +ᴰ s ≤ᴰ? c))))
  where
    c<Aws : c <ᴰ (A +ᴰ w) +ᴰ s
    c<Aws le = f (⊑-trans (≤⇒⁻⊑⁻ le) (by-side refl ⁻≤))
    r<w : Dec (A +ᴰ s ≤ᴰ c) → c ∸ᴰ (A +ᴰ s) <ᴰ w
    r<w (yes as≤c) le =
      c<Aws (≤ᴰ-trans (≤ᴰ-reflexive (trans (+ᴰ-assoc A w s)
                        (trans (cong (A +ᴰ_) (+ᴰ-comm w s)) (sym (+ᴰ-assoc A s w)))))
              (≤ᴰ-trans (+ᴰ-monoʳ-≤ (A +ᴰ s) le) (≤ᴰ-reflexive (+-∸ as≤c))))
    r<w (no ¬as) = subst (_<ᴰ w) (sym (∸-≰ ¬as)) (open-pos l◁)
... | x , r , xw =
  x , (⊑-trans (⊔ᶜ-ubˡ (lo b) _) r , xw) ,
  past (c<Axs (A +ᴰ s ≤ᴰ? c))
  where
    r<x : c ∸ᴰ (A +ᴰ s) <ᴰ x
    r<x = ⊑⁻⇒< (⊑-trans (⊔ᶜ-ubʳ (lo b) _) r) refl
    swap : (A +ᴰ s) +ᴰ x ≡ (A +ᴰ x) +ᴰ s
    swap = trans (+ᴰ-assoc A s x) (trans (cong (A +ᴰ_) (+ᴰ-comm s x)) (sym (+ᴰ-assoc A x s)))
    c<Axs : Dec (A +ᴰ s ≤ᴰ c) → c <ᴰ (A +ᴰ x) +ᴰ s
    c<Axs (yes as≤c) =
      subst₂ _<ᴰ_ (+-∸ as≤c) swap (+ᴰ-monoʳ-< (A +ᴰ s) r<x)
    c<Axs (no ¬as) =
      <-≤-trans (λ z → ¬as z) (subst (A +ᴰ s ≤ᴰ_) swap (≤ᴰ-+ (A +ᴰ s) x))

------------------------------------------------------------------------
-- The largest of finitely many lengths in a box is in the box

private
  ⊔-sel : ∀ a b → (a ⊔ᴰ b ≡ a) ⊎ (a ⊔ᴰ b ≡ b)
  ⊔-sel a b with a ≤ᴰ? b
  ... | yes _ = inj₂ refl
  ... | no _  = inj₁ refl

maxFrom : Carrier → List Carrier → Carrier
maxFrom = foldr _⊔ᴰ_

maxFrom-∈ : ∀ {b θ₀} ts → θ₀ ∈ⁱ b → (∀ {t} → t ∈ ts → t ∈ⁱ b) → maxFrom θ₀ ts ∈ⁱ b
maxFrom-∈ []       m h = m
maxFrom-∈ {b} {θ₀} (t ∷ ts) m h with ⊔-sel t (maxFrom θ₀ ts)
... | inj₁ e = subst (_∈ⁱ b) (sym e) (h (here refl))
... | inj₂ e = subst (_∈ⁱ b) (sym e) (maxFrom-∈ {b} ts m (λ x → h (there x)))

maxFrom-≥ : ∀ {θ₀ t} ts → t ∈ ts → t ≤ᴰ maxFrom θ₀ ts
maxFrom-≥ {θ₀} (t ∷ ts) (here refl) = ⊔-ubˡ t (maxFrom θ₀ ts)
maxFrom-≥ {θ₀} (t′ ∷ ts) (there x) = ≤ᴰ-trans (maxFrom-≥ ts x) (⊔-ubʳ t′ (maxFrom θ₀ ts))

------------------------------------------------------------------------
-- The lengths the failing comparisons ask for

-- the comparisons with a piece at the front: a closed amount `A` before
-- it, a bound `C`, and the extremal sum `S` of what follows it

reqs : Interval → List (Carrier × Hi) → List Hi → List Carrier
req  : Interval → Carrier × Hi → Hi → List Carrier
req b (A , C) S with cl A +ʰ hi b +ʰ S ⊑ʰ? C
... | yes _ = []
... | no f  = proj₁ (witness b A S C f) ∷ []
reqs b TS Ss = foldr (λ AC r → foldr (λ S r′ → req b AC S ++ r′) [] Ss ++ r) [] TS

private
  req-∈ : ∀ {b AC S t} → t ∈ req b AC S → t ∈ⁱ b
  req-∈ {b} {A , C} {S} m with cl A +ʰ hi b +ʰ S ⊑ʰ? C
  req-∈ {b} {A , C} {S} (here refl) | no f = proj₁ (proj₂ (witness b A S C f))

  req-fails : ∀ {b A C S} → ¬ (cl A +ʰ hi b +ʰ S ⊑ʰ C)
            → Σ[ t ∈ Carrier ] t ∈ req b (A , C) S × Fails A S C t
  req-fails {b} {A} {C} {S} f with cl A +ʰ hi b +ʰ S ⊑ʰ? C
  ... | yes y = ⊥-elim (f y)
  ... | no f′ = proj₁ (witness b A S C f′) , here refl , proj₂ (proj₂ (witness b A S C f′))

  inner-∈ : ∀ {b AC t} Ss → t ∈ foldr (λ S r′ → req b AC S ++ r′) [] Ss → t ∈ⁱ b
  inner-∈ {b} {AC} (S ∷ Ss) m with ∈-++⁻ (req b AC S) m
  ... | inj₁ m′ = req-∈ {S = S} m′
  ... | inj₂ m′ = inner-∈ Ss m′

  reqs-∈ : ∀ {b t} TS Ss → t ∈ reqs b TS Ss → t ∈ⁱ b
  reqs-∈ {b} (AC ∷ TS) Ss m with ∈-++⁻ (foldr (λ S r′ → req b AC S ++ r′) [] Ss) m
  ... | inj₁ m′ = inner-∈ Ss m′
  ... | inj₂ m′ = reqs-∈ TS Ss m′

  inner-has : ∀ {b AC S t} Ss → S ∈ Ss → t ∈ req b AC S → t ∈ foldr (λ S r′ → req b AC S ++ r′) [] Ss
  inner-has (S ∷ Ss) (here refl) m = ∈-++⁺ˡ m
  inner-has {b} {AC} (S′ ∷ Ss) (there x) m = ∈-++⁺ʳ (req b AC S′) (inner-has Ss x m)

  reqs-has : ∀ {b AC S t} TS Ss → AC ∈ TS → S ∈ Ss → t ∈ req b AC S → t ∈ reqs b TS Ss
  reqs-has (AC ∷ TS) Ss (here refl) s m = ∈-++⁺ˡ (inner-has Ss s m)
  reqs-has {b} (AC′ ∷ TS) Ss (there x) s m =
    ∈-++⁺ʳ (foldr (λ S r′ → req b AC′ S ++ r′) [] Ss) (reqs-has TS Ss x s m)

------------------------------------------------------------------------
-- The zone

-- pieces read two ways: extremal, and at chosen lengths

Z : List (Kind × Interval) → List Carrier → List (Ph × Ph)
Z = zipWith (λ kb θ → (proj₁ kb , hi (proj₂ kb)) , (proj₁ kb , cl θ))

symP : List (Kind × Interval) → List Ph
symP = map (λ kb → proj₁ kb , hi (proj₂ kb))

conP : List (Kind × Interval) → List Carrier → List Ph
conP kb θs = map π₂ (Z kb θs)

Σ₁ Σ₂ : List (Ph × Ph) → Hi
Σ₁ pre = sumʰ (map proj₂ (map π₁ pre))
Σ₂ pre = sumʰ (map proj₂ (map π₂ pre))

data InBoxes : List Carrier → List (Kind × Interval) → Set where
  []  : InBoxes [] []
  _∷_ : ∀ {θ k b θs kb} → θ ∈ⁱ b → InBoxes θs kb → InBoxes (θ ∷ θs) ((k , b) ∷ kb)

PrefixGood : List (Ph × Ph) → List (Carrier × Hi) → Set
PrefixGood zs TS = ∀ pre b → pre ++ b ≡ zs → ∀ {A C} → (A , C) ∈ TS
                 → ¬ (cl A +ʰ Σ₁ pre ⊑ʰ C) → ¬ (cl A +ʰ Σ₂ pre ⊑ʰ C)

InfixGood : List (Ph × Ph) → List Hi → Set
InfixGood zs 𝒞 = ∀ a pre b → a ++ pre ++ b ≡ zs → ∀ {C} → C ∈ 𝒞
               → ¬ (Σ₁ pre ⊑ʰ C) → ¬ (Σ₂ pre ⊑ʰ C)

prefixSumsʰ : List Hi → List Hi
prefixSumsʰ []       = fin 0⁺ ∷ []
prefixSumsʰ (h ∷ hs) = fin 0⁺ ∷ map (h +ʰ_) (prefixSumsʰ hs)

private
  ∷-inj : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-inj refl = refl , refl

  prefixʰ-∈ : ∀ (pre b : List (Ph × Ph)) {kb θs} → pre ++ b ≡ Z kb θs → InBoxes θs kb
            → Σ₁ pre ∈ prefixSumsʰ (map (λ kb → hi (proj₂ kb)) kb)
  prefixʰ-∈ [] b {[]} _ [] = here refl
  prefixʰ-∈ [] b {_ ∷ _} _ (_ ∷ _) = here refl
  prefixʰ-∈ (z ∷ pre) b {(k , bx) ∷ kb} {θ ∷ θs} e (_ ∷ ib) with ∷-inj {A = Ph × Ph} {x = z} {y = (k , hi bx) , (k , cl θ)} {xs = pre ++ b} {ys = Z kb θs} e
  ... | refl , e′ = there (∈-map⁺ (hi bx +ʰ_) (prefixʰ-∈ pre b e′ ib))

  0+ : ∀ h → cl 0ᴰ +ʰ h ≡ h
  0+ = +ʰ-identityˡ

record Zone (kb : List (Kind × Interval)) (TS : List (Carrier × Hi)) (𝒞 : List Hi) : Set where
  field
    θs     : List Carrier
    boxes  : InBoxes θs kb
    prefix : PrefixGood (Z kb θs) TS
    infixes : InfixGood (Z kb θs) 𝒞

zone : ∀ kb TS 𝒞 → Zone kb TS 𝒞
zone [] TS 𝒞 = record { θs = [] ; boxes = [] ; prefix = pg ; infixes = ig }
  where
    pg : PrefixGood [] TS
    pg [] b e _ f = f
    ig : InfixGood [] 𝒞
    ig [] [] b e _ f = f
zone ((k , b) ∷ kb) TS 𝒞 = record
  { θs = θ ∷ R.θs ; boxes = θ∈ ∷ R.boxes ; prefix = pg ; infixes = ig }
  where
    TS′ = TS ++ map (0ᴰ ,_) 𝒞
    Ss  = prefixSumsʰ (map (λ kb → hi (proj₂ kb)) kb)
    θ₀  = proj₁ (inhabited b)
    θ   = maxFrom θ₀ (reqs b TS′ Ss)
    θ∈ : θ ∈ⁱ b
    θ∈ = maxFrom-∈ {b} (reqs b TS′ Ss) (proj₂ (inhabited b)) (reqs-∈ TS′ Ss)
    module R = Zone (zone kb (map (λ AC → proj₁ AC +ᴰ θ , proj₂ AC) TS′) 𝒞)

    head : ∀ {A C} → (A , C) ∈ TS′ → ∀ pre′ b′ → pre′ ++ b′ ≡ Z kb R.θs
         → ¬ (cl A +ʰ (hi b +ʰ Σ₁ pre′) ⊑ʰ C) → ¬ (cl A +ʰ (cl θ +ʰ Σ₂ pre′) ⊑ʰ C)
    head {A} {C} m pre′ b′ e f with req-fails {b} {A} {C} {Σ₁ pre′}
                                       (λ t → f (subst (_⊑ʰ C) (+ʰ-assoc (cl A) (hi b) _) t))
    ... | t , tm , tf =
      λ g → R.prefix pre′ b′ e (∈-map⁺ (λ AC → proj₁ AC +ᴰ θ , proj₂ AC) m)
              (fails-mono (maxFrom-≥ (reqs b TS′ Ss) (reqs-has TS′ Ss m Sm tm)) tf)
              (subst (_⊑ʰ C) (sym (+ʰ-assoc (cl A) (cl θ) _)) g)
      where
        Sm : Σ₁ pre′ ∈ Ss
        Sm = prefixʰ-∈ pre′ b′ e R.boxes

    pg : PrefixGood (Z ((k , b) ∷ kb) (θ ∷ R.θs)) TS
    pg [] b′ e _ f = f
    pg (z ∷ pre′) b′ e {A} {C} m f with ∷-inj {x = z} {y = (k , hi b) , (k , cl θ)} {xs = pre′ ++ b′} {ys = Z kb R.θs} e
    ... | refl , e′ = head (∈-++⁺ˡ m) pre′ b′ e′ f

    ig : InfixGood (Z ((k , b) ∷ kb) (θ ∷ R.θs)) 𝒞
    ig [] [] b′ e _ f = f
    ig [] (z ∷ pre′) b′ e {C} m f with ∷-inj {x = z} {y = (k , hi b) , (k , cl θ)} {xs = pre′ ++ b′} {ys = Z kb R.θs} e
    ... | refl , e′ =
      λ g → head (∈-++⁺ʳ TS (∈-map⁺ (0ᴰ ,_) m)) pre′ b′ e′
                 (λ t → f (subst (_⊑ʰ C) (0+ _) t))
                 (subst (_⊑ʰ C) (sym (0+ _)) g)
    ig (a₀ ∷ a) pre b′ e m f with ∷-inj {x = a₀} {y = (k , hi b) , (k , cl θ)} {xs = a ++ pre ++ b′} {ys = Z kb R.θs} e
    ... | _ , e′ = R.infixes a pre b′ e′ m f
