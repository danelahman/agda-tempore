------------------------------------------------------------------------
-- The lower reader is complete against any family of bounds on a     --
-- grid.                                                              --
--                                                                    --
-- As for the upper reader: a family of bounds is a predicate on      --
-- words of lower letters, each with its ends multiples of a positive --
-- unit `δ`. The extremal sums of a word lie below a multiple         --
-- `N × δ`; a grid end failing against one of them lies above it, and --
-- the grid end `(N + 1) × δ` below that one fails too, so finitely   --
-- many grid ends serve for every bound of the family.                --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus
import Syntax.Grades.Exact.Grid as Grid

module Syntax.Grades.Exact.Reader.Lower.Family
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
import Data.List.Relation.Unary.Any as Any
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Cut; pt; ⁺; ⁻; 0⁻; _+ˡ_; ⊑⇒≤; by-pt)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-trans to ⊑ᶜ-trans)

open import Syntax.Grades.Exact.Grid T using (_×ᴰ_; ×-+; ×-reflect; ×-<-mono; Grid)
open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Lift T Op n code code-injective using (Lang; _≾_)
open import Syntax.Grades.Exact.Expression T Op n code code-injective running using (lower)
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Positions T Op n code code-injective running using (sumᴰ-++)
open import Syntax.Grades.Exact.Reader.Transfer T Op n code code-injective running using (capsOf)
open import Syntax.Grades.Exact.Reader.Lower T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower.Read T Op n code code-injective running
  using (readᴸ; pcsᴸ; ValidL)
open import Syntax.Grades.Exact.Reader.Lower.Close T Op n code code-injective running dense κ κ-pos
  using (subsumsˡ)
open import Syntax.Grades.Exact.Reader.Lower.Zone T Op n code code-injective running dense κ κ-pos
open import Syntax.Grades.Exact.Reader.Lower.Correct T Op n code code-injective running dense κ κ-pos
  using (symᴸ; boxesᴸ; sym-boxes; conc-con; instance-of; agree-vᴸ)

private
  π₁ = proj₁
  π₂ = proj₂

------------------------------------------------------------------------
-- Ends on the grid

GridC : Cut → Set
GridC c = Grid δ (pt c)

GridWˡ : Word′ lower → Set
GridWˡ []           = ⊤
GridWˡ (op _ ∷ v)   = GridWˡ v
GridWˡ (st _ c ∷ v) = GridC c × GridWˡ v

private
  grid-+ : ∀ c c′ → GridC c → GridC c′ → GridC (c +ˡ c′)
  grid-+ (p ∣ᶜ _) (q ∣ᶜ _) (k , e) (l , e′) = k ℕ.+ l , trans (×-+ k l δ) (cong₂ _+ᴰ_ e e′)

  grid-caps : ∀ v → GridWˡ v → ∀ {c} → c ∈ capsOf v → GridC c
  grid-caps (op _ ∷ v)   g        m           = grid-caps v g m
  grid-caps (st _ c ∷ v) (gc , g) (here refl) = gc
  grid-caps (st _ c ∷ v) (gc , g) (there m)   = grid-caps v g m

  grid-subsums : ∀ cs → (∀ {c} → c ∈ cs → GridC c) → ∀ {C} → C ∈ subsumsˡ cs → GridC C
  grid-subsums []       _ (here refl) = 0 , refl
  grid-subsums (c ∷ cs) g m with ∈-++⁻ (subsumsˡ cs) m
  ... | inj₁ m′ = grid-subsums cs (λ x → g (there x)) m′
  ... | inj₂ m′ with ∈-map⁻ (c +ˡ_) m′
  ...   | C′ , m″ , refl = grid-+ c C′ (g (here refl)) (grid-subsums cs (λ x → g (there x)) m″)

------------------------------------------------------------------------
-- Sums of lower ends, by their points

private
  pt-sum : ∀ cs → pt (sumˡ cs) ≡ sumᴰ (map pt cs)
  pt-sum []       = refl
  pt-sum (c ∷ cs) = cong (pt c +ᴰ_) (pt-sum cs)

  infix-≤ : ∀ a pre b → sumᴰ pre ≤ᴰ sumᴰ (a ++ pre ++ b)
  infix-≤ a pre b =
    ≤ᴰ-trans (≤ᴰ-+ (sumᴰ pre) (sumᴰ b))
      (≤ᴰ-trans (≤ᴰ-reflexive (sym (sumᴰ-++ pre b)))
        (≤ᴰ-trans (≤ᴰ-+ˡ (sumᴰ (pre ++ b)) (sumᴰ a)) (≤ᴰ-reflexive (sym (sumᴰ-++ a (pre ++ b))))))

  map-infix : ∀ {A B : Set} (f : A → B) a pre b {zs} → a ++ pre ++ b ≡ zs
            → map f a ++ map f pre ++ map f b ≡ map f zs
  map-infix f a pre b refl = sym (trans (map-++ f a (pre ++ b)) (cong (map f a ++_) (map-++ f pre b)))

  π₁-Z : ∀ kb θs → InBoxesˡ θs kb → map π₁ (Zˡ kb θs) ≡ symPˡ kb
  π₁-Z []       []       []       = refl
  π₁-Z (k ∷ kb) (θ ∷ θs) (_ ∷ ib) = cong (_ ∷_) (π₁-Z kb θs ib)

------------------------------------------------------------------------
-- The grid ends up to a multiple

gridToˡ : ℕ → List Cut
gridToˡ N = concatMap (λ k → ((k ×ᴰ δ) ∣ᶜ ⁻) ∷ ((k ×ᴰ δ) ∣ᶜ ⁺) ∷ []) (upTo (ℕ.suc N))

private
  in-gridTo : ∀ {N k} s → k ℕ.≤ N → ((k ×ᴰ δ) ∣ᶜ s) ∈ gridToˡ N
  in-gridTo {N} {k} s r =
    ∈-concatMap⁺ (λ j → ((j ×ᴰ δ) ∣ᶜ ⁻) ∷ ((j ×ᴰ δ) ∣ᶜ ⁺) ∷ []) (Any.map (λ { refl → side s }) (∈-upTo⁺ (ℕ.s≤s r)))
    where
      side : ∀ s → ((k ×ᴰ δ) ∣ᶜ s) ∈ (((k ×ᴰ δ) ∣ᶜ ⁻) ∷ ((k ×ᴰ δ) ∣ᶜ ⁺) ∷ [])
      side ⁻ = here refl
      side ⁺ = there (here refl)

------------------------------------------------------------------------
-- Completeness against a family

Familyˡ : Set₁
Familyˡ = Word′ lower → Set

UnionFˡ : Familyˡ → Lang
UnionFˡ F y = Σ[ v ∈ Word′ lower ] F v × ⟦ v ⟧ʷ y

completeᶠᴸ : ∀ w → ValidL w → (F : Familyˡ) → (∀ {v} → F v → GridWˡ v × ValidL v)
           → ⟦ w ⟧ʷ ≾ UnionFˡ F → Σ[ v ∈ Word′ lower ] F v × RunL (map symᴸ w) v
completeᶠᴸ w vw F gF f = main (zoneˡ kb [] (gridToˡ (ℕ.suc N)))
  where
    kb = boxesᴸ w
    cs = map proj₂ (symPˡ kb)
    tot = sumᴰ (map pt cs)
    N = proj₁ (archimedean δ tot δ-pos)
    tot≤ : tot ≤ᴰ N ×ᴰ δ
    tot≤ = proj₂ (archimedean δ tot δ-pos)

    main : Zoneˡ kb [] (gridToˡ (ℕ.suc N)) → Σ[ v ∈ Word′ lower ] F v × RunL (map symᴸ w) v
    main zn with instance-of w vw (Zoneˡ.θs zn) (Zoneˡ.boxes zn)
    ... | x , sh , wo , ep with f x (inst-⟦⟧ w (_ , sh , wo))
    ...   | y , (v , v∈ , y∈v) , fit =
      v , v∈ ,
      subst (λ P → RunL P v) (sym-boxes w)
        (agree-vᴸ kb θs v (Zoneˡ.boxes zn) good (λ m → m)
           (subst (λ P → RunL P v) pcs-x (readᴸ (⟦⟧-inst v y∈v) (proj₂ (gF v∈)) fit)))
      where
        θs = Zoneˡ.θs zn
        pcs-x : pcsᴸ x ≡ conPˡ kb θs
        pcs-x = trans (cong (map toLo) ep) (conc-con kb θs)

        -- the point of an infix's extremal sum is at most `N × δ`
        below : ∀ a pre b → a ++ pre ++ b ≡ Zˡ kb θs → pt (Σ₁ pre) ≤ᴰ N ×ᴰ δ
        below a pre b e =
          ≤ᴰ-trans (≤ᴰ-reflexive (pt-sum P)) (≤ᴰ-trans pre≤ tot≤)
          where
            P = map proj₂ (map π₁ pre)
            A = map proj₂ (map π₁ a)
            B = map proj₂ (map π₁ b)
            e₂ : A ++ P ++ B ≡ cs
            e₂ = trans (map-infix proj₂ (map π₁ a) (map π₁ pre) (map π₁ b) (map-infix π₁ a pre b e))
                       (cong (map proj₂) (π₁-Z kb θs (Zoneˡ.boxes zn)))
            pre≤ : sumᴰ (map pt P) ≤ᴰ tot
            pre≤ = subst (λ z → sumᴰ (map pt P) ≤ᴰ sumᴰ (map pt z)) e₂
                     (subst (sumᴰ (map pt P) ≤ᴰ_)
                       (cong sumᴰ (map-infix pt A P B refl))
                       (infix-≤ (map pt A) (map pt P) (map pt B)))

        good : InfixGoodˡ (Zˡ kb θs) (subsumsˡ (capsOf v))
        good a pre b e {C} m f′ with grid-subsums (capsOf v) (grid-caps v (proj₁ (gF v∈))) m
        good a pre b e {c ∣ᶜ s} m f′ | k , refl with k ℕ.≤? ℕ.suc N
        ... | yes r = Zoneˡ.infixes zn a pre b e (in-gridTo {ℕ.suc N} {k} s r) f′
        ... | no ¬r = λ g → Zoneˡ.infixes zn a pre b e (in-gridTo {ℕ.suc N} {ℕ.suc N} ⁻ ℕ.≤-refl)
                              far (⊑ᶜ-trans C′⊑C g)
          where
            C′⊑C : ((ℕ.suc N ×ᴰ δ) ∣ᶜ ⁻) ⊑ᶜ ((k ×ᴰ δ) ∣ᶜ s)
            C′⊑C = by-pt (×-<-mono δ-pos (ℕ.≰⇒> ¬r))
            far : ¬ (((ℕ.suc N ×ᴰ δ) ∣ᶜ ⁻) ⊑ᶜ Σ₁ pre)
            far h = ℕ.<-irrefl {N} refl (×-reflect δ-pos {ℕ.suc N} {N} (≤ᴰ-trans (⊑⇒≤ h) (below a pre b e)))
