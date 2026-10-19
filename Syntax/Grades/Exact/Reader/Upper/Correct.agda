------------------------------------------------------------------------
-- The upper reader decides the order on words of upper letters.      --
--                                                                    --
-- A word is read at the upper ends of its letters: an operation at   --
-- the upper end of its running time, a stretch at its end.           --
--                                                                    --
--   sound:    an accepting run on a word against a bound gives, for  --
--             every run of the word, a run of the bound it fits:      --
--             the smaller weights of the run are read the same way,  --
--             the bound's ends are closed within it, and the word of --
--             the bound is built;                                    --
--   complete: if every run of the word fits a run of one of finitely --
--             many bounds, the reader accepts against one of them:   --
--             a run of the word close enough to its upper ends that  --
--             it reads as the word does fits some bound, and the fit --
--             is read.                                               --
--                                                                    --
-- With one bound this is the decision; with several it says that a   --
-- word is below a union of words only when it is below one of them.  --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Reader.Upper.Correct
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
open import Relation.Nullary.Decidable.Core using (fromWitness)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Hi; fin; ∞; _⊑ʰ_; ⁺; ⁻; 0⁺; _+ʰ_; ⊑ʰ-trans; ⊑ʰ-refl; +ʰ-mono;
         Interval; ⟪_,_⟫; lo; hi; _◁_; _◁?_; ⊑-trans)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-refl to ⊑ᶜ-refl)
open import Syntax.Durations.Intervals.Dense T using (_∈ⁱ_; ⊑⁻⇒<)

open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Order T Op n code code-injective using (_⊑_)
open import Syntax.Grades.Exact.Lift T Op n code code-injective using (Lang; _≾_)
open import Syntax.Grades.Exact.Expression T Op n code code-injective running using (upper)
open import Syntax.Grades.Exact.Pour T Op n code code-injective using (pour-⊑)
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Transfer T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Upper T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Upper.Build T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Upper.Read T Op n code code-injective running
  using (read; pcs)
open import Syntax.Grades.Exact.Reader.Upper.Close T Op n code code-injective running dense
  using (Valid; Within; closeᵁ; subsums; sub-∈; []; op; st)
open import Syntax.Grades.Exact.Reader.Upper.Zone T Op n code code-injective running dense κ κ-pos
open import Syntax.Grades.Exact.Reader.Upper.Mimic T Op n code code-injective running
  using (Le*; mimic; []; _∷_)

open RunningTimes.RunningTimes running using (rt; rt-positive)

private
  π₁ = proj₁
  π₂ = proj₂

------------------------------------------------------------------------
-- A word read at the upper ends of its letters

symᵁ : Letter Hi → Ph
symᵁ (op o)   = opk o , hi (rt o)
symᵁ (st S h) = stk S , h

------------------------------------------------------------------------
-- Soundness

private
  le-inst : ∀ {w cps x} → Shape w cps → WordOf cps x → Le* (map symᵁ w) (map toHi cps)
  le-inst []        []          = []
  le-inst (op sh)   (op r wo)   = (refl , proj₂ r) ∷ le-inst sh wo
  le-inst (st a sh) (st wo)     = (refl , a) ∷ le-inst sh wo

  within-shape : ∀ {vc v ps} → Within vc v → Shape (map clo vc) ps → Shape v ps
  within-shape []          []        = []
  within-shape (op w)      (op sh)   = op (within-shape w sh)
  within-shape (st c≤h w)  (st a sh) = st (⊑ʰ-trans a c≤h) (within-shape w sh)

soundᵁ : ∀ w v → Valid v → RunU (map symᵁ w) v → ⟦ w ⟧ʷ ≾ ⟦ v ⟧ʷ
soundᵁ w v val r x x∈ with ⟦⟧-inst w x∈
... | cps , sh , wo with closeᵁ cps v val (mimic (le-inst sh wo) r)
...   | vc , wi , r′ with build-run wo r′
...     | y , (ps , shy , woy) , p = y , inst-⟦⟧ v (ps , within-shape wi shy , woy) , pour-⊑ p

------------------------------------------------------------------------
-- The boxes of a word, and its runs near the upper ends

-- every stretch letter admits a positive length

ValidW : Word′ upper → Set
ValidW []           = ⊤
ValidW (op _ ∷ w)   = ValidW w
ValidW (st _ h ∷ w) = (0ᴰ ∣ᶜ ⁺) ◁ h × ValidW w

boxes : (w : Word′ upper) → ValidW w → List (Kind × Interval)
boxes []           _         = []
boxes (op o ∷ w)   vw        = (opk o , rt o) ∷ boxes w vw
boxes (st S h ∷ w) (p , vw)  = (stk S , ⟪ 0ᴰ ∣ᶜ ⁺ , h ⟫ {fromWitness p}) ∷ boxes w vw

private
  sym-boxes : ∀ w vw → symP (boxes w vw) ≡ map symᵁ w
  sym-boxes []           _        = refl
  sym-boxes (op o ∷ w)   vw       = cong (_ ∷_) (sym-boxes w vw)
  sym-boxes (st S h ∷ w) (p , vw) = cong (_ ∷_) (sym-boxes w vw)

  conc : List (Kind × Interval) → List Carrier → List Pc
  conc = zipWith (λ kb θ → proj₁ kb , θ)

  conc-con : ∀ kb θs → map toHi (conc kb θs) ≡ conP kb θs
  conc-con []       []       = refl
  conc-con []       (_ ∷ _)  = refl
  conc-con (_ ∷ _)  []       = refl
  conc-con (k ∷ kb) (θ ∷ θs) = cong (_ ∷_) (conc-con kb θs)

  sym-Z : ∀ kb θs → InBoxes θs kb → map π₁ (Z kb θs) ≡ symP kb
  sym-Z []       []       []       = refl
  sym-Z (k ∷ kb) (θ ∷ θs) (_ ∷ ib) = cong (_ ∷_) (sym-Z kb θs ib)

  -- a length in a box with a positive lower end is positive
  pos-in : ∀ {θ b} → (0ᴰ ∣ᶜ ⁺) ⊑ᶜ lo b → θ ∈ⁱ b → 0ᴰ <ᴰ θ
  pos-in z (l , _) = ⊑⁻⇒< (⊑-trans z l) refl

  -- the run with the chosen lengths
  instance-of : ∀ w vw θs → InBoxes θs (boxes w vw)
              → Σ[ x ∈ Word ] Shape w (conc (boxes w vw) θs) × WordOf (conc (boxes w vw) θs) x
                              × pieces x ≡ conc (boxes w vw) θs
  instance-of [] _ [] [] = [] , [] , [] , refl
  instance-of (op o ∷ w) vw (θ ∷ θs) (m ∷ ib) with instance-of w vw θs ib
  ... | x , sh , wo , e =
    op o (pos⁺ θ (pos-in {b = rt o} (rt-positive o) m)) ∷ x , op sh , op m wo , cong (_ ∷_) e
  instance-of (st S h ∷ w) (p , vw) (θ ∷ θs) (m ∷ ib) with instance-of w vw θs ib
  ... | x , sh , wo , e =
    stretch S θ ++ x , st (proj₂ m) sh , st wo ,
    subst (λ z → pieces (z ++ x) ≡ (stk S , θ) ∷ conc (boxes w vw) θs)
          (sym (stretch-pos S θ pos)) (cong (_ ∷_) e)
    where
      pos : 0ᴰ <ᴰ θ
      pos = ⊑⁻⇒< (proj₁ m) refl

------------------------------------------------------------------------
-- The reading at chosen lengths, against a bound

private
  diag : ∀ {A : Set} → A → A × A
  diag a = a , a

  -- the pieces of `Z`: one kind, the chosen weight below the extremal
  Q : Ph × Ph → Set
  Q z = proj₁ (π₁ z) ≡ proj₁ (π₂ z) × proj₂ (π₂ z) ⊑ʰ proj₂ (π₁ z)

  AllQ : List (Ph × Ph) → Set
  AllQ []       = ⊤
  AllQ (z ∷ zs) = Q z × AllQ zs

  allQ : ∀ kb θs → InBoxes θs kb → AllQ (Z kb θs)
  allQ []       []       []       = tt
  allQ (k ∷ kb) (θ ∷ θs) (m ∷ ib) = (refl , proj₂ m) , allQ kb θs ib

  allQ-++ʳ : ∀ a {zs} → AllQ (a ++ zs) → AllQ zs
  allQ-++ʳ []      q       = q
  allQ-++ʳ (_ ∷ a) (_ , q) = allQ-++ʳ a q

  allQ-++ˡ : ∀ pre {zs} → AllQ (pre ++ zs) → AllQ pre
  allQ-++ˡ []        _       = tt
  allQ-++ˡ (_ ∷ pre) (z , q) = z , allQ-++ˡ pre q

  sum-Q : ∀ pre → AllQ pre → sumʰ (map proj₂ (map π₂ pre)) ⊑ʰ sumʰ (map proj₂ (map π₁ pre))
  sum-Q []        _        = ⊑ʰ-refl
  sum-Q (z ∷ pre) ((_ , r) , q) = +ʰ-mono r (sum-Q pre q)

  mapˡ-diag : ∀ (f : Hi × Hi → Hi) → (∀ h → f (h , h) ≡ h) → ∀ (v : Word′ upper)
            → map (mapˡ f) (map (mapˡ diag) v) ≡ v
  mapˡ-diag f e []           = refl
  mapˡ-diag f e (op o ∷ v)   = cong (op o ∷_) (mapˡ-diag f e v)
  mapˡ-diag f e (st S h ∷ v) = cong₂ _∷_ (cong (st S) (e h)) (mapˡ-diag f e v)

  caps-diag : ∀ (v : Word′ upper) → capsOf (map (mapˡ diag) v) ≡ map diag (capsOf v)
  caps-diag []           = refl
  caps-diag (op o ∷ v)   = caps-diag v
  caps-diag (st S h ∷ v) = cong (_ ∷_) (caps-diag v)

  sub-diag : ∀ {cs : List (Hi × Hi)} {hs : List Hi} → Sub cs (map diag hs) → map π₁ cs ≡ map π₂ cs × Sub (map π₁ cs) hs
  sub-diag {[]} {[]} [] = refl , []
  sub-diag {_ ∷ cs} {h ∷ hs} (keep s) with sub-diag s
  ... | e , s′ = cong (h ∷_) e , keep s′
  sub-diag {cs} {h ∷ hs} (drop s) with sub-diag s
  ... | e , s′ = e , drop s′

agree-v : ∀ kb θs (v : Word′ upper) {𝒞} → InBoxes θs kb → InfixGood (Z kb θs) 𝒞
        → (∀ {C} → C ∈ subsums (capsOf v) → C ∈ 𝒞)
        → RunU (conP kb θs) v → RunU (symP kb) v
agree-v kb θs v {𝒞} ib good inj r =
  subst₂ RunU (sym-Z kb θs ib) (mapˡ-diag π₁ (λ _ → refl) v)
    (Equivalence.from A.agreeᵁ
      (subst (RunU (conP kb θs)) (sym (mapˡ-diag π₂ (λ _ → refl) v)) r))
  where
    zs₀ = Z kb θs
    vz₀ : List (Letter (Hi × Hi))
    vz₀ = map (mapˡ diag) v

    kinds : ∀ a z b → a ++ z ∷ b ≡ zs₀ → proj₁ (π₁ z) ≡ proj₁ (π₂ z)
    kinds a z b e = proj₁ (proj₁ (allQ-++ʳ a (subst AllQ (sym e) (allQ kb θs ib))))

    agree : ∀ a pre b (cs : List (Hi × Hi)) → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf vz₀)
          → Fitsᵁ (map π₁ pre) (map π₁ cs) ⇔ Fitsᵁ (map π₂ pre) (map π₂ cs)
    agree a pre b cs e s with sub-diag (subst (Sub cs) (caps-diag v) s)
    ... | ec , s′ = mk⇔ to from
      where
        qpre : AllQ pre
        qpre = allQ-++ˡ pre (allQ-++ʳ a (subst AllQ (sym e) (allQ kb θs ib)))
        to : Fitsᵁ (map π₁ pre) (map π₁ cs) → Fitsᵁ (map π₂ pre) (map π₂ cs)
        to f = subst (λ X → Fitsᵁ (map π₂ pre) X) ec (⊑ʰ-trans (sum-Q pre qpre) f)
        from : Fitsᵁ (map π₂ pre) (map π₂ cs) → Fitsᵁ (map π₁ pre) (map π₁ cs)
        from g with Fitsᵁ? (map π₁ pre) (map π₁ cs)
        ... | yes f = f
        ... | no ¬f = ⊥-elim (good a pre b e (inj (sub-∈ s′)) ¬f (subst (λ X → Fitsᵁ (map π₂ pre) X) (sym ec) g))

    module A = Agree proj₁ Fitsᵁ zs₀ vz₀ kinds agree

------------------------------------------------------------------------
-- Completeness, against finitely many bounds

UnionL : List (Word′ upper) → Lang
UnionL vs y = Any (λ v → ⟦ v ⟧ʷ y) vs

caps𝒞 : List (Word′ upper) → List Hi
caps𝒞 = concatMap (λ v → subsums (capsOf v))

completeᵁ : ∀ w (vw : ValidW w) vs → ⟦ w ⟧ʷ ≾ UnionL vs → Any (λ v → RunU (map symᵁ w) v) vs
completeᵁ w vw vs f with zone (boxes w vw) [] (caps𝒞 vs)
... | zn with instance-of w vw (Zone.θs zn) (Zone.boxes zn)
...   | x , sh , wo , ep with f x (inst-⟦⟧ w (_ , sh , wo))
...     | y , y∈ , fit = go vs (λ m → m) y∈
  where
    kb = boxes w vw
    θs = Zone.θs zn
    pcs-x : pcs x ≡ conP kb θs
    pcs-x = trans (cong (map toHi) ep) (conc-con kb θs)
    go : ∀ vs′ → (∀ {C} → C ∈ caps𝒞 vs′ → C ∈ caps𝒞 vs) → Any (λ v → ⟦ v ⟧ʷ y) vs′
       → Any (λ v → RunU (map symᵁ w) v) vs′
    go (v ∷ vs′) inj (here y∈v) =
      here (subst (λ P → RunU P v) (sym-boxes w vw)
              (agree-v kb θs v (Zone.boxes zn) (Zone.infixes zn) (λ m → inj (∈-++⁺ˡ m))
                 (subst (λ P → RunU P v) pcs-x (read (⟦⟧-inst v y∈v) fit))))
    go (v ∷ vs′) inj (there a) =
      there (go vs′ (λ m → inj (∈-++⁺ʳ (subsums (capsOf v)) m)) a)

------------------------------------------------------------------------
-- The decision

complete-oneᵁ : ∀ w (vw : ValidW w) v → ⟦ w ⟧ʷ ≾ ⟦ v ⟧ʷ → RunU (map symᵁ w) v
complete-oneᵁ w vw v f with completeᵁ w vw (v ∷ []) (λ x x∈ → lift (f x x∈))
  where
    lift : ∀ {x} → Σ[ y ∈ Word ] ⟦ v ⟧ʷ y × x ⊑ y → Σ[ y ∈ Word ] UnionL (v ∷ []) y × x ⊑ y
    lift (y , y∈ , fit) = y , here y∈ , fit
... | here r = r

decideᵁ : ∀ w (vw : ValidW w) v → Valid v → ⟦ w ⟧ʷ ≾ ⟦ v ⟧ʷ ⇔ RunU (map symᵁ w) v
decideᵁ w vw v val = mk⇔ (complete-oneᵁ w vw v) (soundᵁ w v val)

_≾ᵁ?_ : ∀ w v → Dec (RunU (map symᵁ w) v)
w ≾ᵁ? v = runU? (map symᵁ w) v
