------------------------------------------------------------------------
-- Exact runs near the extremal one read as it does, in the lower     --
-- reader.                                                            --
--                                                                    --
-- The lower reader reads a piece at the lower end of its box. For    --
-- finitely many comparisons there is a choice of a length in every   --
-- box such that every comparison the extremal reading fails, the     --
-- exact reading fails too: each failing comparison asks for some     --
-- length small enough, and the smallest of them serves all.          --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Reader.Lower.Zone
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; foldr; [_]; zipWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Cut; Hi; fin; ∞; _⊑ʰ_; ⁺; ⁻; 0⁻; _+ˡ_; ⊑⇒≤; ≤⇒⁻⊑⁻; by-pt; by-side; ⁺≤⁺;
         ⊑ʰ-trans; Interval; lo; hi; lo◁hi; _◁_; ⊏-cases; +ˡ-monoʳ; +ˡ-monoˡ; +ˡ-assoc;
         +ˡ-identityˡ; ≤⇒⁺⊑⁺; ⁻≤; ⊏-by-pt)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; _⊑?_ to _⊑ᶜ?_; ⊑-refl to ⊑ᶜ-refl; ⊑-trans to ⊑ᶜ-trans)
open import Syntax.Durations.Intervals.Dense T using (_∈ⁱ_; ⊑⁻⇒<; module Exact)
open Exact dense κ κ-pos using (between; inhabited)

open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower T Op n code code-injective running

private
  π₁ = proj₁
  π₂ = proj₂

  -- an upper end above a closed lower end admits its point
  closed-lo : ∀ {w h} → (w ∣ᶜ ⁻) ◁ h → fin (w ∣ᶜ ⁺) ⊑ʰ h
  closed-lo {w} {∞} _ = tt
  closed-lo {w} {fin c} r with ⊏-cases r
  ... | inj₁ a              = by-pt a
  ... | inj₂ (e , _ , refl) = by-side e ⁺≤⁺

  -- a closed point at or above a cut's point lies above the cut
  ≤⇒⊑⁺ : ∀ {c t z} → c ≤ᴰ z → (c ∣ᶜ t) ⊑ᶜ (z ∣ᶜ ⁺)
  ≤⇒⊑⁺ {c} {t} {z} le with compare c z
  ... | tri< a = by-pt a
  ... | tri> a = ⊥-elim (a le)
  ≤⇒⊑⁺ {c} {⁻} {z} le | tri≈ e = by-side e ⁻≤
  ≤⇒⊑⁺ {c} {⁺} {z} le | tri≈ e = by-side e ⁺≤⁺

  ⊓-sel : ∀ a b → (a ⊓ᴰ b ≡ a) ⊎ (a ⊓ᴰ b ≡ b)
  ⊓-sel a b with a ≤ᴰ? b
  ... | yes _ = inj₁ refl
  ... | no _  = inj₂ refl

  -- a duration below an upper end, and anything smaller
  hi-down : ∀ {a b h} → a ≤ᴰ b → fin (b ∣ᶜ ⁺) ⊑ʰ h → fin (a ∣ᶜ ⁺) ⊑ʰ h
  hi-down {a} {b} {h} r s = ⊑ʰ-trans {fin (a ∣ᶜ ⁺)} {fin (b ∣ᶜ ⁺)} {h} (≤⇒⁺⊑⁺ r) s

------------------------------------------------------------------------
-- One failing comparison, kept failing by a length inside the box

Fails : Carrier → Cut → Cut → Carrier → Set
Fails A S C θ = ¬ (C ⊑ᶜ cl⁻ A +ˡ cl⁻ θ +ˡ S)

fails-mono : ∀ {A S C θ θ′} → θ′ ≤ᴰ θ → Fails A S C θ → Fails A S C θ′
fails-mono {A} {S} {C} r f t = f (⊑ᶜ-trans t (+ˡ-monoˡ S (+ˡ-monoʳ (cl⁻ A) (≤⇒⁻⊑⁻ r))))

witness : ∀ b A S C → ¬ (C ⊑ᶜ cl⁻ A +ˡ lo b +ˡ S) → Σ[ θ ∈ Carrier ] θ ∈ⁱ b × Fails A S C θ
witness b A (s ∣ᶜ u) (c ∣ᶜ t) f = go (lo b) refl (lo◁hi b)
  where
    go : (l : Cut) → lo b ≡ l → l ◁ hi b → Σ[ θ ∈ Carrier ] θ ∈ⁱ b × Fails A (s ∣ᶜ u) (c ∣ᶜ t) θ
    go (w ∣ᶜ ⁻) el l◁ =
      w , (subst (_⊑ᶜ (w ∣ᶜ ⁻)) (sym el) ⊑ᶜ-refl , closed-lo l◁) ,
      (λ r → f (subst (λ l → (c ∣ᶜ t) ⊑ᶜ cl⁻ A +ˡ l +ˡ (s ∣ᶜ u)) (sym el) r))
    go (w ∣ᶜ ⁺) el l◁ = open-case (inhabited b) (between {w ∣ᶜ ⁺} {fin ((c ∸ᴰ (A +ᴰ s)) ∣ᶜ ⁻)} (⊏-by-pt w<))
      where
        swap : ∀ z → (A +ᴰ z) +ᴰ s ≡ (A +ᴰ s) +ᴰ z
        swap z = trans (+ᴰ-assoc A z s) (trans (cong (A +ᴰ_) (+ᴰ-comm z s)) (sym (+ᴰ-assoc A s z)))
        Aws<c : (A +ᴰ w) +ᴰ s <ᴰ c
        Aws<c le = f (subst (λ l → (c ∣ᶜ t) ⊑ᶜ cl⁻ A +ˡ l +ˡ (s ∣ᶜ u)) (sym el) (≤⇒⊑⁺ le))
        as≤c : A +ᴰ s ≤ᴰ c
        as≤c = ≤ᴰ-trans (≤ᴰ-trans (≤ᴰ-+ (A +ᴰ s) w) (≤ᴰ-reflexive (sym (swap w)))) (<⇒≤ Aws<c)
        w< : w <ᴰ c ∸ᴰ (A +ᴰ s)
        w< le = Aws<c (≤ᴰ-trans (≤ᴰ-reflexive (sym (+-∸ as≤c)))
                        (≤ᴰ-trans (+ᴰ-monoʳ-≤ (A +ᴰ s) le) (≤ᴰ-reflexive (sym (swap w)))))
        open-case : Σ Carrier (_∈ⁱ b)
                  → Σ Carrier (λ x → (w ∣ᶜ ⁺) ⊑ᶜ (x ∣ᶜ ⁻) × fin (x ∣ᶜ ⁺) ⊑ʰ fin ((c ∸ᴰ (A +ᴰ s)) ∣ᶜ ⁻))
                  → Σ[ θ ∈ Carrier ] θ ∈ⁱ b × Fails A (s ∣ᶜ u) (c ∣ᶜ t) θ
        open-case (x₂ , l₂ , h₂) (x₁ , r₁ , s₁) = θ , mem , fails
          where
            θ = x₁ ⊓ᴰ x₂
            w<x₁ : w <ᴰ x₁
            w<x₁ = ⊑⁻⇒< r₁ refl
            w<x₂ : w <ᴰ x₂
            w<x₂ = ⊑⁻⇒< (subst (_⊑ᶜ (x₂ ∣ᶜ ⁻)) el l₂) refl
            w<θ : w <ᴰ θ
            w<θ with ⊓-sel x₁ x₂
            ... | inj₁ e = subst (w <ᴰ_) (sym e) w<x₁
            ... | inj₂ e = subst (w <ᴰ_) (sym e) w<x₂
            mem : θ ∈ⁱ b
            mem = subst (_⊑ᶜ (θ ∣ᶜ ⁻)) (sym el) (by-pt w<θ) , hi-down (⊓-lbʳ x₁ x₂) h₂
            θ<c : (A +ᴰ θ) +ᴰ s <ᴰ c
            θ<c = subst (_<ᴰ c) (sym (swap θ))
                    (≤-<-trans (+ᴰ-monoʳ-≤ (A +ᴰ s) (⊓-lbˡ x₁ x₂))
                      (subst ((A +ᴰ s) +ᴰ x₁ <ᴰ_) (+-∸ as≤c) (+ᴰ-monoʳ-< (A +ᴰ s) (⊑⁻⇒< s₁ refl))))
            fails : Fails A (s ∣ᶜ u) (c ∣ᶜ t) θ
            fails r = θ<c (⊑⇒≤ r)

------------------------------------------------------------------------
-- The smallest of finitely many lengths in a box is in the box

minFrom : Carrier → List Carrier → Carrier
minFrom = foldr _⊓ᴰ_

minFrom-∈ : ∀ {b θ₀} ts → θ₀ ∈ⁱ b → (∀ {t} → t ∈ ts → t ∈ⁱ b) → minFrom θ₀ ts ∈ⁱ b
minFrom-∈ []       m h = m
minFrom-∈ {b} {θ₀} (t ∷ ts) m h with ⊓-sel t (minFrom θ₀ ts)
... | inj₁ e = subst (_∈ⁱ b) (sym e) (h (here refl))
... | inj₂ e = subst (_∈ⁱ b) (sym e) (minFrom-∈ {b} ts m (λ x → h (there x)))

minFrom-≤ : ∀ {θ₀ t} ts → t ∈ ts → minFrom θ₀ ts ≤ᴰ t
minFrom-≤ {θ₀} (t ∷ ts) (here refl) = ⊓-lbˡ t (minFrom θ₀ ts)
minFrom-≤ {θ₀} (t′ ∷ ts) (there x) = ≤ᴰ-trans (⊓-lbʳ t′ (minFrom θ₀ ts)) (minFrom-≤ ts x)

------------------------------------------------------------------------
-- The lengths the failing comparisons ask for

reqs : Interval → List (Carrier × Cut) → List Cut → List Carrier
req  : Interval → Carrier × Cut → Cut → List Carrier
req b (A , C) S with C ⊑ᶜ? cl⁻ A +ˡ lo b +ˡ S
... | yes _ = []
... | no f  = proj₁ (witness b A S C f) ∷ []
reqs b TS Ss = foldr (λ AC r → foldr (λ S r′ → req b AC S ++ r′) [] Ss ++ r) [] TS

private
  req-∈ : ∀ {b AC S t} → t ∈ req b AC S → t ∈ⁱ b
  req-∈ {b} {A , C} {S} m with C ⊑ᶜ? cl⁻ A +ˡ lo b +ˡ S
  req-∈ {b} {A , C} {S} (here refl) | no f = proj₁ (proj₂ (witness b A S C f))

  req-fails : ∀ {b A C S} → ¬ (C ⊑ᶜ cl⁻ A +ˡ lo b +ˡ S)
            → Σ[ t ∈ Carrier ] t ∈ req b (A , C) S × Fails A S C t
  req-fails {b} {A} {C} {S} f with C ⊑ᶜ? cl⁻ A +ˡ lo b +ˡ S
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

Zˡ : List (Kind × Interval) → List Carrier → List (Pl × Pl)
Zˡ = zipWith (λ kb θ → (proj₁ kb , lo (proj₂ kb)) , (proj₁ kb , cl⁻ θ))

symPˡ : List (Kind × Interval) → List Pl
symPˡ = map (λ kb → proj₁ kb , lo (proj₂ kb))

conPˡ : List (Kind × Interval) → List Carrier → List Pl
conPˡ kb θs = map π₂ (Zˡ kb θs)

Σ₁ Σ₂ : List (Pl × Pl) → Cut
Σ₁ pre = sumˡ (map proj₂ (map π₁ pre))
Σ₂ pre = sumˡ (map proj₂ (map π₂ pre))

data InBoxesˡ : List Carrier → List (Kind × Interval) → Set where
  []  : InBoxesˡ [] []
  _∷_ : ∀ {θ k b θs kb} → θ ∈ⁱ b → InBoxesˡ θs kb → InBoxesˡ (θ ∷ θs) ((k , b) ∷ kb)

PrefixGoodˡ : List (Pl × Pl) → List (Carrier × Cut) → Set
PrefixGoodˡ zs TS = ∀ pre b → pre ++ b ≡ zs → ∀ {A C} → (A , C) ∈ TS
                  → ¬ (C ⊑ᶜ cl⁻ A +ˡ Σ₁ pre) → ¬ (C ⊑ᶜ cl⁻ A +ˡ Σ₂ pre)

InfixGoodˡ : List (Pl × Pl) → List Cut → Set
InfixGoodˡ zs 𝒞 = ∀ a pre b → a ++ pre ++ b ≡ zs → ∀ {C} → C ∈ 𝒞
                → ¬ (C ⊑ᶜ Σ₁ pre) → ¬ (C ⊑ᶜ Σ₂ pre)

prefixSumsˡ : List Cut → List Cut
prefixSumsˡ []       = 0⁻ ∷ []
prefixSumsˡ (c ∷ cs) = 0⁻ ∷ map (c +ˡ_) (prefixSumsˡ cs)

private
  ∷-inj : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-inj refl = refl , refl

  prefixˡ-∈ : ∀ (pre b : List (Pl × Pl)) {kb θs} → pre ++ b ≡ Zˡ kb θs → InBoxesˡ θs kb
            → Σ₁ pre ∈ prefixSumsˡ (map (λ kb → lo (proj₂ kb)) kb)
  prefixˡ-∈ [] b {[]} _ [] = here refl
  prefixˡ-∈ [] b {_ ∷ _} _ (_ ∷ _) = here refl
  prefixˡ-∈ (z ∷ pre) b {(k , bx) ∷ kb} {θ ∷ θs} e (_ ∷ ib)
    with ∷-inj {A = Pl × Pl} {x = z} {y = (k , lo bx) , (k , cl⁻ θ)} {xs = pre ++ b} {ys = Zˡ kb θs} e
  ... | refl , e′ = there (∈-map⁺ (lo bx +ˡ_) (prefixˡ-∈ pre b e′ ib))

record Zoneˡ (kb : List (Kind × Interval)) (TS : List (Carrier × Cut)) (𝒞 : List Cut) : Set where
  field
    θs      : List Carrier
    boxes   : InBoxesˡ θs kb
    prefix  : PrefixGoodˡ (Zˡ kb θs) TS
    infixes : InfixGoodˡ (Zˡ kb θs) 𝒞

zoneˡ : ∀ kb TS 𝒞 → Zoneˡ kb TS 𝒞
zoneˡ [] TS 𝒞 = record { θs = [] ; boxes = [] ; prefix = pg ; infixes = ig }
  where
    pg : PrefixGoodˡ [] TS
    pg [] b e _ f = f
    ig : InfixGoodˡ [] 𝒞
    ig [] [] b e _ f = f
zoneˡ ((k , b) ∷ kb) TS 𝒞 = record
  { θs = θ ∷ R.θs ; boxes = θ∈ ∷ R.boxes ; prefix = pg ; infixes = ig }
  where
    TS′ = TS ++ map (0ᴰ ,_) 𝒞
    Ss  = prefixSumsˡ (map (λ kb → lo (proj₂ kb)) kb)
    θ₀  = proj₁ (inhabited b)
    θ   = minFrom θ₀ (reqs b TS′ Ss)
    θ∈ : θ ∈ⁱ b
    θ∈ = minFrom-∈ {b} (reqs b TS′ Ss) (proj₂ (inhabited b)) (reqs-∈ TS′ Ss)
    module R = Zoneˡ (zoneˡ kb (map (λ AC → proj₁ AC +ᴰ θ , proj₂ AC) TS′) 𝒞)

    head : ∀ {A C} → (A , C) ∈ TS′ → ∀ pre′ b′ → pre′ ++ b′ ≡ Zˡ kb R.θs
         → ¬ (C ⊑ᶜ cl⁻ A +ˡ (lo b +ˡ Σ₁ pre′)) → ¬ (C ⊑ᶜ cl⁻ A +ˡ (cl⁻ θ +ˡ Σ₂ pre′))
    head {A} {C} m pre′ b′ e f with req-fails {b} {A} {C} {Σ₁ pre′}
                                       (λ t → f (subst (C ⊑ᶜ_) (+ˡ-assoc (cl⁻ A) (lo b) _) t))
    ... | t , tm , tf =
      λ g → R.prefix pre′ b′ e (∈-map⁺ (λ AC → proj₁ AC +ᴰ θ , proj₂ AC) m)
              (fails-mono (minFrom-≤ (reqs b TS′ Ss) (reqs-has TS′ Ss m Sm tm)) tf)
              (subst (C ⊑ᶜ_) (sym (+ˡ-assoc (cl⁻ A) (cl⁻ θ) _)) g)
      where
        Sm : Σ₁ pre′ ∈ Ss
        Sm = prefixˡ-∈ pre′ b′ e R.boxes

    pg : PrefixGoodˡ (Zˡ ((k , b) ∷ kb) (θ ∷ R.θs)) TS
    pg [] b′ e _ f = f
    pg (z ∷ pre′) b′ e {A} {C} m f
      with ∷-inj {x = z} {y = (k , lo b) , (k , cl⁻ θ)} {xs = pre′ ++ b′} {ys = Zˡ kb R.θs} e
    ... | refl , e′ = head (∈-++⁺ˡ m) pre′ b′ e′ f

    ig : InfixGoodˡ (Zˡ ((k , b) ∷ kb) (θ ∷ R.θs)) 𝒞
    ig [] [] b′ e _ f = f
    ig [] (z ∷ pre′) b′ e {C} m f
      with ∷-inj {x = z} {y = (k , lo b) , (k , cl⁻ θ)} {xs = pre′ ++ b′} {ys = Zˡ kb R.θs} e
    ... | refl , e′ =
      λ g → head (∈-++⁺ʳ TS (∈-map⁺ (0ᴰ ,_) m)) pre′ b′ e′
                 (λ t → f (subst (C ⊑ᶜ_) (+ˡ-identityˡ _) t))
                 (subst (C ⊑ᶜ_) (sym (+ˡ-identityˡ _)) g)
    ig (a₀ ∷ a) pre b′ e m f
      with ∷-inj {x = a₀} {y = (k , lo b) , (k , cl⁻ θ)} {xs = a ++ pre ++ b′} {ys = Zˡ kb R.θs} e
    ... | _ , e′ = R.infixes a pre b′ e′ m f
