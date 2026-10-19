------------------------------------------------------------------------
-- The lower reader decides the order on words of lower letters.      --
--                                                                    --
-- A word is read at the lower ends of its letters: an operation at   --
-- the lower end of its running time, a stretch at its end. As for     --
-- the upper reader, an accepting run gives every run of the word a    --
-- run of the bound it fits, and a word whose runs all fit runs of     --
-- finitely many bounds is accepted against one of them.              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Reader.Lower.Correct
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; zipWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Cut; Hi; fin; ∞; ⁺; ⁻; 0⁺; _+ˡ_; +ˡ-monoˡ; +ˡ-monoʳ; Interval; ⟪_,_⟫; lo; hi)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-refl to ⊑ᶜ-refl; ⊑-trans to ⊑ᶜ-trans)
open import Syntax.Durations.Intervals.Dense T using (_∈ⁱ_; ⊑⁻⇒<)

open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Order T Op n code code-injective using (_⊑_)
open import Syntax.Grades.Exact.Lift T Op n code code-injective using (Lang; _≾_)
open import Syntax.Grades.Exact.Expression T Op n code code-injective running using (lower)
open import Syntax.Grades.Exact.Pour T Op n code code-injective using (pour-⊑)
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Transfer T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower.Build T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower.Read T Op n code code-injective running
  using (readᴸ; pcsᴸ; ValidL)
open import Syntax.Grades.Exact.Reader.Lower.Close T Op n code code-injective running dense κ κ-pos
  using (Withinˡ; closeᴸ; subsumsˡ; sub-∈ˡ; []; op; st)
open import Syntax.Grades.Exact.Reader.Lower.Zone T Op n code code-injective running dense κ κ-pos
open import Syntax.Grades.Exact.Reader.Lower.Mimic T Op n code code-injective running
  using (Ge*; mimicᴸ; []; _∷_)

open RunningTimes.RunningTimes running using (rt; rt-positive)

private
  π₁ = proj₁
  π₂ = proj₂

------------------------------------------------------------------------
-- A word read at the lower ends of its letters

symᴸ : Letter Cut → Pl
symᴸ (op o)   = opk o , lo (rt o)
symᴸ (st S c) = stk S , c

------------------------------------------------------------------------
-- Soundness

private
  ge-inst : ∀ {w cps x} → Shape w cps → WordOf cps x → Ge* (map symᴸ w) (map toLo cps)
  ge-inst []        []        = []
  ge-inst (op sh)   (op r wo) = (refl , proj₁ r) ∷ ge-inst sh wo
  ge-inst (st a sh) (st wo)   = (refl , a) ∷ ge-inst sh wo

  within-shape : ∀ {vc v ps} → Withinˡ vc v → Shape (map clo⁻ vc) ps → Shape v ps
  within-shape []          []        = []
  within-shape (op w)      (op sh)   = op (within-shape w sh)
  within-shape (st c≤ψ w)  (st a sh) = st (⊑ᶜ-trans c≤ψ a) (within-shape w sh)

soundᴸ : ∀ w v → RunL (map symᴸ w) v → ⟦ w ⟧ʷ ≾ ⟦ v ⟧ʷ
soundᴸ w v r x x∈ with ⟦⟧-inst w x∈
... | cps , sh , wo with closeᴸ cps v (mimicᴸ (ge-inst sh wo) r)
...   | vc , wi , r′ with build-runᴸ wo r′
...     | y , (ps , shy , woy) , p = y , inst-⟦⟧ v (ps , within-shape wi shy , woy) , pour-⊑ p

------------------------------------------------------------------------
-- The boxes of a word, and its runs near the lower ends

boxesᴸ : (w : Word′ lower) → List (Kind × Interval)
boxesᴸ []           = []
boxesᴸ (op o ∷ w)   = (opk o , rt o) ∷ boxesᴸ w
boxesᴸ (st S c ∷ w) = (stk S , ⟪ c , ∞ ⟫) ∷ boxesᴸ w

private
  sym-boxes : ∀ w → symPˡ (boxesᴸ w) ≡ map symᴸ w
  sym-boxes []           = refl
  sym-boxes (op o ∷ w)   = cong (_ ∷_) (sym-boxes w)
  sym-boxes (st S c ∷ w) = cong (_ ∷_) (sym-boxes w)

  conc : List (Kind × Interval) → List Carrier → List (Piece Carrier)
  conc = zipWith (λ kb θ → proj₁ kb , θ)

  conc-con : ∀ kb θs → map toLo (conc kb θs) ≡ conPˡ kb θs
  conc-con []       []       = refl
  conc-con []       (_ ∷ _)  = refl
  conc-con (_ ∷ _)  []       = refl
  conc-con (k ∷ kb) (θ ∷ θs) = cong (_ ∷_) (conc-con kb θs)

  sym-Z : ∀ kb θs → InBoxesˡ θs kb → map π₁ (Zˡ kb θs) ≡ symPˡ kb
  sym-Z []       []       []       = refl
  sym-Z (k ∷ kb) (θ ∷ θs) (_ ∷ ib) = cong (_ ∷_) (sym-Z kb θs ib)

  pos-in : ∀ {θ b} → 0⁺ ⊑ᶜ lo b → θ ∈ⁱ b → 0ᴰ <ᴰ θ
  pos-in z (l , _) = ⊑⁻⇒< (⊑ᶜ-trans z l) refl

  instance-of : ∀ w → ValidL w → ∀ θs → InBoxesˡ θs (boxesᴸ w)
              → Σ[ x ∈ Word ] Shape w (conc (boxesᴸ w) θs) × WordOf (conc (boxesᴸ w) θs) x
                              × pieces x ≡ conc (boxesᴸ w) θs
  instance-of [] _ [] [] = [] , [] , [] , refl
  instance-of (op o ∷ w) vw (θ ∷ θs) (m ∷ ib) with instance-of w vw θs ib
  ... | x , sh , wo , e =
    op o (pos⁺ θ (pos-in {b = rt o} (rt-positive o) m)) ∷ x , op sh , op m wo , cong (_ ∷_) e
  instance-of (st S c ∷ w) (z , vw) (θ ∷ θs) (m ∷ ib) with instance-of w vw θs ib
  ... | x , sh , wo , e =
    stretch S θ ++ x , st (proj₁ m) sh , st wo ,
    subst (λ y → pieces (y ++ x) ≡ (stk S , θ) ∷ conc (boxesᴸ w) θs)
          (sym (stretch-pos S θ pos)) (cong (_ ∷_) e)
    where
      pos : 0ᴰ <ᴰ θ
      pos = ⊑⁻⇒< (⊑ᶜ-trans z (proj₁ m)) refl

------------------------------------------------------------------------
-- The reading at chosen lengths, against a bound

private
  diag : ∀ {A : Set} → A → A × A
  diag a = a , a

  Q : Pl × Pl → Set
  Q z = proj₁ (π₁ z) ≡ proj₁ (π₂ z) × proj₂ (π₁ z) ⊑ᶜ proj₂ (π₂ z)

  AllQ : List (Pl × Pl) → Set
  AllQ []       = ⊤
  AllQ (z ∷ zs) = Q z × AllQ zs

  allQ : ∀ kb θs → InBoxesˡ θs kb → AllQ (Zˡ kb θs)
  allQ []       []       []       = tt
  allQ (k ∷ kb) (θ ∷ θs) (m ∷ ib) = (refl , proj₁ m) , allQ kb θs ib

  allQ-++ʳ : ∀ a {zs} → AllQ (a ++ zs) → AllQ zs
  allQ-++ʳ []      q       = q
  allQ-++ʳ (_ ∷ a) (_ , q) = allQ-++ʳ a q

  allQ-++ˡ : ∀ pre {zs} → AllQ (pre ++ zs) → AllQ pre
  allQ-++ˡ []        _       = tt
  allQ-++ˡ (_ ∷ pre) (z , q) = z , allQ-++ˡ pre q

  sum-Q : ∀ pre → AllQ pre → sumˡ (map proj₂ (map π₁ pre)) ⊑ᶜ sumˡ (map proj₂ (map π₂ pre))
  sum-Q []        _        = ⊑ᶜ-refl
  sum-Q (z ∷ pre) ((_ , r) , q) =
    ⊑ᶜ-trans (+ˡ-monoˡ (sumˡ (map proj₂ (map π₁ pre))) r) (+ˡ-monoʳ (proj₂ (π₂ z)) (sum-Q pre q))

  mapˡ-diag : ∀ (f : Cut × Cut → Cut) → (∀ h → f (h , h) ≡ h) → ∀ (v : Word′ lower)
            → map (mapˡ f) (map (mapˡ diag) v) ≡ v
  mapˡ-diag f e []           = refl
  mapˡ-diag f e (op o ∷ v)   = cong (op o ∷_) (mapˡ-diag f e v)
  mapˡ-diag f e (st S h ∷ v) = cong₂ _∷_ (cong (st S) (e h)) (mapˡ-diag f e v)

  caps-diag : ∀ (v : Word′ lower) → capsOf (map (mapˡ diag) v) ≡ map diag (capsOf v)
  caps-diag []           = refl
  caps-diag (op o ∷ v)   = caps-diag v
  caps-diag (st S h ∷ v) = cong (_ ∷_) (caps-diag v)

  sub-diag : ∀ {cs : List (Cut × Cut)} {hs : List Cut} → Sub cs (map diag hs)
           → map π₁ cs ≡ map π₂ cs × Sub (map π₁ cs) hs
  sub-diag {[]} {[]} [] = refl , []
  sub-diag {_ ∷ cs} {h ∷ hs} (keep s) with sub-diag s
  ... | e , s′ = cong (h ∷_) e , keep s′
  sub-diag {cs} {h ∷ hs} (drop s) with sub-diag s
  ... | e , s′ = e , drop s′

agree-vᴸ : ∀ kb θs (v : Word′ lower) {𝒞} → InBoxesˡ θs kb → InfixGoodˡ (Zˡ kb θs) 𝒞
         → (∀ {C} → C ∈ subsumsˡ (capsOf v) → C ∈ 𝒞)
         → RunL (conPˡ kb θs) v → RunL (symPˡ kb) v
agree-vᴸ kb θs v {𝒞} ib good inj r =
  subst₂ RunL (sym-Z kb θs ib) (mapˡ-diag π₁ (λ _ → refl) v)
    (Equivalence.from A.agreeᴸ
      (subst (RunL (conPˡ kb θs)) (sym (mapˡ-diag π₂ (λ _ → refl) v)) r))
  where
    zs₀ = Zˡ kb θs
    vz₀ : List (Letter (Cut × Cut))
    vz₀ = map (mapˡ diag) v

    kinds : ∀ a z b → a ++ z ∷ b ≡ zs₀ → proj₁ (π₁ z) ≡ proj₁ (π₂ z)
    kinds a z b e = proj₁ (proj₁ (allQ-++ʳ a (subst AllQ (sym e) (allQ kb θs ib))))

    agree : ∀ a pre b (cs : List (Cut × Cut)) → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf vz₀)
          → Fitsᴸ (map π₁ pre) (map π₁ cs) ⇔ Fitsᴸ (map π₂ pre) (map π₂ cs)
    agree a pre b cs e s with sub-diag (subst (Sub cs) (caps-diag v) s)
    ... | ec , s′ = mk⇔ to from
      where
        qpre : AllQ pre
        qpre = allQ-++ˡ pre (allQ-++ʳ a (subst AllQ (sym e) (allQ kb θs ib)))
        to : Fitsᴸ (map π₁ pre) (map π₁ cs) → Fitsᴸ (map π₂ pre) (map π₂ cs)
        to f = subst (λ X → Fitsᴸ (map π₂ pre) X) ec (⊑ᶜ-trans f (sum-Q pre qpre))
        from : Fitsᴸ (map π₂ pre) (map π₂ cs) → Fitsᴸ (map π₁ pre) (map π₁ cs)
        from g with Fitsᴸ? (map π₁ pre) (map π₁ cs)
        ... | yes f = f
        ... | no ¬f = ⊥-elim (good a pre b e (inj (sub-∈ˡ s′)) ¬f (subst (λ X → Fitsᴸ (map π₂ pre) X) (sym ec) g))

    module A = Agree proj₁ Fitsᴸ zs₀ vz₀ kinds agree

------------------------------------------------------------------------
-- Completeness, against finitely many bounds

UnionLᴸ : List (Word′ lower) → Lang
UnionLᴸ vs y = Any (λ v → ⟦ v ⟧ʷ y) vs

caps𝒞ᴸ : List (Word′ lower) → List Cut
caps𝒞ᴸ = concatMap (λ v → subsumsˡ (capsOf v))

AllValidL : List (Word′ lower) → Set
AllValidL []       = ⊤
AllValidL (v ∷ vs) = ValidL v × AllValidL vs

completeᴸ : ∀ w → ValidL w → ∀ vs → AllValidL vs → ⟦ w ⟧ʷ ≾ UnionLᴸ vs
          → Any (λ v → RunL (map symᴸ w) v) vs
completeᴸ w vw vs avs f with zoneˡ (boxesᴸ w) [] (caps𝒞ᴸ vs)
... | zn with instance-of w vw (Zoneˡ.θs zn) (Zoneˡ.boxes zn)
...   | x , sh , wo , ep with f x (inst-⟦⟧ w (_ , sh , wo))
...     | y , y∈ , fit = go vs avs (λ m → m) y∈
  where
    kb = boxesᴸ w
    θs = Zoneˡ.θs zn
    pcs-x : pcsᴸ x ≡ conPˡ kb θs
    pcs-x = trans (cong (map toLo) ep) (conc-con kb θs)
    go : ∀ vs′ → AllValidL vs′ → (∀ {C} → C ∈ caps𝒞ᴸ vs′ → C ∈ caps𝒞ᴸ vs) → Any (λ v → ⟦ v ⟧ʷ y) vs′
       → Any (λ v → RunL (map symᴸ w) v) vs′
    go (v ∷ vs′) (vv , _) inj (here y∈v) =
      here (subst (λ P → RunL P v) (sym-boxes w)
              (agree-vᴸ kb θs v (Zoneˡ.boxes zn) (Zoneˡ.infixes zn) (λ m → inj (∈-++⁺ˡ m))
                 (subst (λ P → RunL P v) pcs-x (readᴸ (⟦⟧-inst v y∈v) vv fit))))
    go (v ∷ vs′) (_ , avs′) inj (there a) =
      there (go vs′ avs′ (λ m → inj (∈-++⁺ʳ (subsumsˡ (capsOf v)) m)) a)

------------------------------------------------------------------------
-- The decision

complete-oneᴸ : ∀ w → ValidL w → ∀ v → ValidL v → ⟦ w ⟧ʷ ≾ ⟦ v ⟧ʷ → RunL (map symᴸ w) v
complete-oneᴸ w vw v vv f with completeᴸ w vw (v ∷ []) (vv , tt) (λ x x∈ → lift (f x x∈))
  where
    lift : ∀ {x} → Σ[ y ∈ Word ] ⟦ v ⟧ʷ y × x ⊑ y → Σ[ y ∈ Word ] UnionLᴸ (v ∷ []) y × x ⊑ y
    lift (y , y∈ , fit) = y , here y∈ , fit
... | here r = r

decideᴸ : ∀ w → ValidL w → ∀ v → ValidL v → ⟦ w ⟧ʷ ≾ ⟦ v ⟧ʷ ⇔ RunL (map symᴸ w) v
decideᴸ w vw v vv = mk⇔ (complete-oneᴸ w vw v vv) (soundᴸ w v)

_≾ᴸ?_ : ∀ w v → Dec (RunL (map symᴸ w) v)
w ≾ᴸ? v = runL? (map symᴸ w) v
