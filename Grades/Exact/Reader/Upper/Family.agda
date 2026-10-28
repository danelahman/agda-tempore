------------------------------------------------------------------------
-- The upper reader is complete against any family of bounds on a     --
-- grid.                                                              --
--                                                                    --
-- A family of bounds is a predicate on words of upper letters, each  --
-- with its ends multiples of a positive unit `δ` (or `∞`). If every  --
-- run of a word of bounded letters fits a run of some bound of the   --
-- family, the reader accepts the word against one of them: in an     --
-- Archimedean time domain the extremal sums of the word lie below a  --
-- multiple `N × δ`, so only the grid ends up to it can fail against  --
-- them, and a run near the upper ends that keeps those comparisons   --
-- failing reads, against the bound it fits, as the word does.        --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus
import Grades.Exact.Grid as Grid

module Grades.Exact.Reader.Upper.Family
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ)
  (archimedean : Grid.Archimedean T)
  (δ : Duration.Carrier D) (δ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) δ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; upTo)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁻; ∈-upTo⁺; ∈-concatMap⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; Side; Hi; fin; ∞; _⊑ʰ_; ⊑ʰ-∞; ⁺; ⁻; 0⁺; _+ʰ_; _⊑_; ⊏⇒⊑; ⊑⇒≤; hi; _∧ˢ_)
  renaming (_∣_ to _∣ᶜ_)

open import Grades.Exact.Grid T using (_×ᴰ_; ×-+; ×-reflect; Grid)
open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective using (Lang; _≾_)
open import Grades.Exact.Expression T Op n code code-injective running using (upper)
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Positions T Op n code code-injective running using (sumᴰ-++)
open import Grades.Exact.Reader.Transfer T Op n code code-injective running using (capsOf)
open import Grades.Exact.Reader.Upper T Op n code code-injective running
open import Grades.Exact.Reader.Upper.Read T Op n code code-injective running
  using (read; pcs)
open import Grades.Exact.Reader.Upper.Close T Op n code code-injective running dense
  using (subsums)
open import Grades.Exact.Reader.Upper.Zone T Op n code code-injective running dense κ κ-pos
open import Grades.Exact.Reader.Upper.Correct T Op n code code-injective running dense κ κ-pos
  using (symᵁ; ValidW; boxes; sym-boxes; conc-con; instance-of; agree-v)

open RunningTimes.RunningTimes running using (rt; rt-bounded)
open RunningTimes T Op using (Bounded)

private
  π₁ = proj₁
  π₂ = proj₂

------------------------------------------------------------------------
-- Ends on the grid, and words of bounded letters

GridH : Hi → Set
GridH (fin (p ∣ᶜ _)) = Grid δ p
GridH ∞              = ⊤

GridW : Word′ upper → Set
GridW []           = ⊤
GridW (op _ ∷ v)   = GridW v
GridW (st _ h ∷ v) = GridH h × GridW v

BoundedW : Word′ upper → Set
BoundedW []           = ⊤
BoundedW (op _ ∷ w)   = BoundedW w
BoundedW (st _ h ∷ w) = Bounded h × BoundedW w

------------------------------------------------------------------------
-- Sums of grid ends are on the grid

private
  grid-+ : ∀ h h′ → GridH h → GridH h′ → GridH (h +ʰ h′)
  grid-+ (fin (p ∣ᶜ _)) (fin (q ∣ᶜ _)) (k , e) (l , e′) = k ℕ.+ l , trans (×-+ k l δ) (cong₂ _+ᴰ_ e e′)
  grid-+ (fin _) ∞ _ _ = tt
  grid-+ ∞ _ _ _ = tt

  grid-caps : ∀ v → GridW v → ∀ {h} → h ∈ capsOf v → GridH h
  grid-caps (op _ ∷ v)   g        m           = grid-caps v g m
  grid-caps (st _ h ∷ v) (gh , g) (here refl) = gh
  grid-caps (st _ h ∷ v) (gh , g) (there m)   = grid-caps v g m

  grid-subsums : ∀ hs → (∀ {h} → h ∈ hs → GridH h) → ∀ {C} → C ∈ subsums hs → GridH C
  grid-subsums []       _ (here refl) = 0 , refl
  grid-subsums (h ∷ hs) g m with ∈-++⁻ (subsums hs) m
  ... | inj₁ m′ = grid-subsums hs (λ x → g (there x)) m′
  ... | inj₂ m′ with ∈-map⁻ (h +ʰ_) m′
  ...   | C′ , m″ , refl = grid-+ h C′ (g (here refl)) (grid-subsums hs (λ x → g (there x)) m″)

------------------------------------------------------------------------
-- Sums of finite ends, by their points

private
  ptʰ : Hi → Carrier
  ptʰ (fin (p ∣ᶜ _)) = p
  ptʰ ∞              = 0ᴰ

  AllFin : List Hi → Set
  AllFin []       = ⊤
  AllFin (h ∷ hs) = Bounded h × AllFin hs

  fin-sum : ∀ hs → AllFin hs → Σ[ s ∈ Side ] sumʰ hs ≡ fin (sumᴰ (map ptʰ hs) ∣ᶜ s)
  fin-sum []                  _              = ⁺ , refl
  fin-sum (fin (p ∣ᶜ t) ∷ hs) (_ , fs) with fin-sum hs fs
  ... | s , e rewrite e = t ∧ˢ s , refl
  fin-sum (∞ ∷ hs) (() , _)

  allFin-++ʳ : ∀ a {b} → AllFin (a ++ b) → AllFin b
  allFin-++ʳ []      f       = f
  allFin-++ʳ (_ ∷ a) (_ , f) = allFin-++ʳ a f

  allFin-++ˡ : ∀ a {b} → AllFin (a ++ b) → AllFin a
  allFin-++ˡ []      _       = tt
  allFin-++ˡ (h ∷ a) (g , f) = g , allFin-++ˡ a f

  -- an infix of a list of points sums to at most the whole
  infix-≤ : ∀ a pre b → sumᴰ (pre) ≤ᴰ sumᴰ (a ++ pre ++ b)
  infix-≤ a pre b =
    ≤ᴰ-trans (≤ᴰ-+ (sumᴰ pre) (sumᴰ b))
      (≤ᴰ-trans (≤ᴰ-reflexive (sym (sumᴰ-++ pre b)))
        (≤ᴰ-trans (≤ᴰ-+ˡ (sumᴰ (pre ++ b)) (sumᴰ a)) (≤ᴰ-reflexive (sym (sumᴰ-++ a (pre ++ b))))))

  map-infix : ∀ {A B : Set} (f : A → B) a pre b {zs} → a ++ pre ++ b ≡ zs
            → map f a ++ map f pre ++ map f b ≡ map f zs
  map-infix f a pre b refl = sym (trans (map-++ f a (pre ++ b)) (cong (map f a ++_) (map-++ f pre b)))

  π₁-Z : ∀ kb θs → InBoxes θs kb → map π₁ (Z kb θs) ≡ symP kb
  π₁-Z []       []       []       = refl
  π₁-Z (k ∷ kb) (θ ∷ θs) (_ ∷ ib) = cong (_ ∷_) (π₁-Z kb θs ib)

  boxes-fin : ∀ w vw → BoundedW w → AllFin (map proj₂ (symP (boxes w vw)))
  boxes-fin []           _        _        = tt
  boxes-fin (op o ∷ w)   vw       bw       = rt-bounded o , boxes-fin w vw bw
  boxes-fin (st S h ∷ w) (p , vw) (b , bw) = b , boxes-fin w vw bw

------------------------------------------------------------------------
-- The grid ends up to a multiple

gridTo : ℕ → List Hi
gridTo N = concatMap (λ k → fin ((k ×ᴰ δ) ∣ᶜ ⁻) ∷ fin ((k ×ᴰ δ) ∣ᶜ ⁺) ∷ []) (upTo (ℕ.suc N))

private
  in-gridTo : ∀ {N k} s → k ℕ.≤ N → fin ((k ×ᴰ δ) ∣ᶜ s) ∈ gridTo N
  in-gridTo {N} {k} s r =
    ∈-concatMap⁺ (λ j → fin ((j ×ᴰ δ) ∣ᶜ ⁻) ∷ fin ((j ×ᴰ δ) ∣ᶜ ⁺) ∷ []) (Any-map (∈-upTo⁺ (ℕ.s≤s r)))
    where
      Any-map : k ∈ upTo (ℕ.suc N)
              → Any (λ j → fin ((k ×ᴰ δ) ∣ᶜ s) ∈ (fin ((j ×ᴰ δ) ∣ᶜ ⁻) ∷ fin ((j ×ᴰ δ) ∣ᶜ ⁺) ∷ [])) (upTo (ℕ.suc N))
      Any-map m = Data.List.Relation.Unary.Any.map (λ { refl → side s }) m
        where
          side : ∀ s → fin ((k ×ᴰ δ) ∣ᶜ s) ∈ (fin ((k ×ᴰ δ) ∣ᶜ ⁻) ∷ fin ((k ×ᴰ δ) ∣ᶜ ⁺) ∷ [])
          side ⁻ = here refl
          side ⁺ = there (here refl)

------------------------------------------------------------------------
-- Completeness against a family

Family : Set₁
Family = Word′ upper → Set

UnionF : Family → Lang
UnionF F y = Σ[ v ∈ Word′ upper ] F v × ⟦ v ⟧ʷ y

completeᶠ : ∀ w (vw : ValidW w) → BoundedW w → (F : Family) → (∀ {v} → F v → GridW v)
          → ⟦ w ⟧ʷ ≾ UnionF F → Σ[ v ∈ Word′ upper ] F v × RunU (map symᵁ w) v
completeᶠ w vw bw F gF f = main (zone kb [] (gridTo N))
  where
    kb = boxes w vw
    hs = map proj₂ (symP kb)
    tot = sumᴰ (map ptʰ hs)
    N = proj₁ (archimedean δ tot δ-pos)
    tot≤ : tot ≤ᴰ N ×ᴰ δ
    tot≤ = proj₂ (archimedean δ tot δ-pos)

    main : Zone kb [] (gridTo N) → Σ[ v ∈ Word′ upper ] F v × RunU (map symᵁ w) v
    main zn with instance-of w vw (Zone.θs zn) (Zone.boxes zn)
    ... | x , sh , wo , ep with f x (inst-⟦⟧ w (_ , sh , wo))
    ...   | y , (v , v∈ , y∈v) , fit =
      v , v∈ ,
      subst (λ P → RunU P v) (sym-boxes w vw)
        (agree-v kb θs v (Zone.boxes zn) good (λ m → m)
           (subst (λ P → RunU P v) pcs-x (read (⟦⟧-inst v y∈v) fit)))
      where
        θs = Zone.θs zn
        pcs-x : pcs x ≡ conP kb θs
        pcs-x = trans (cong (map toHi) ep) (conc-con kb θs)

        -- a grid end that an infix's extremal sum passes is among the
        -- grid ends up to `N`
        listed : ∀ a pre b → a ++ pre ++ b ≡ Z kb θs → ∀ {C} → GridH C
               → ¬ (Σ₁ pre ⊑ʰ C) → C ∈ gridTo N
        listed a pre b e {∞} _ f′ = ⊥-elim (f′ (⊑ʰ-∞ (Σ₁ pre)))
        listed a pre b e {fin (c ∣ᶜ s)} (k , refl) f′ =
          in-gridTo {N} {k} s (×-reflect δ-pos (≤ᴰ-trans kδ≤ (≤ᴰ-trans pre≤ tot≤)))
          where
            P = map proj₂ (map π₁ pre)
            A = map proj₂ (map π₁ a)
            B = map proj₂ (map π₁ b)
            e₂ : A ++ P ++ B ≡ hs
            e₂ = trans (map-infix proj₂ (map π₁ a) (map π₁ pre) (map π₁ b) (map-infix π₁ a pre b e))
                       (cong (map proj₂) (π₁-Z kb θs (Zone.boxes zn)))
            fpre : AllFin P
            fpre = allFin-++ˡ P (allFin-++ʳ A (subst AllFin (sym e₂) (boxes-fin w vw bw)))
            σ = proj₁ (fin-sum P fpre)
            eσ = proj₂ (fin-sum P fpre)
            kδ≤ : k ×ᴰ δ ≤ᴰ sumᴰ (map ptʰ P)
            kδ≤ = ⊑⇒≤ (⊏⇒⊑ (λ r → f′ (subst (_⊑ʰ fin ((k ×ᴰ δ) ∣ᶜ s)) (sym eσ) r)))
            pre≤ : sumᴰ (map ptʰ P) ≤ᴰ tot
            pre≤ = subst (λ z → sumᴰ (map ptʰ P) ≤ᴰ sumᴰ (map ptʰ z)) e₂
                     (subst (sumᴰ (map ptʰ P) ≤ᴰ_)
                       (cong sumᴰ (map-infix ptʰ A P B refl))
                       (infix-≤ (map ptʰ A) (map ptʰ P) (map ptʰ B)))

        good : InfixGood (Z kb θs) (subsums (capsOf v))
        good a pre b e {C} m f′ =
          Zone.infixes zn a pre b e
            (listed a pre b e (grid-subsums (capsOf v) (grid-caps v (gF v∈)) m) f′) f′
