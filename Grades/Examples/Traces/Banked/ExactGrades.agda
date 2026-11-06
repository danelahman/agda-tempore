------------------------------------------------------------------------
-- The trace grades with banked delays as interval-letter grades.     --
--                                                                    --
-- A grade of written-out traces maps to the union of their           --
-- translations (`Banked.Upper`, `Banked.Lower`), at the costs of     --
-- the running times:                                                 --
--                                                                    --
--   upper  `Banked.UpperBound`  →  `upperᵍ`, `unbounded` to `≤∞`     --
--   lower  `Banked.LowerBound`   →  `lowerᵍ`                         --
--   both   `Banked.Interval`    →  `intervalᵍ`, end by end           --
--                                                                    --
-- Each map preserves and reflects the order, and sends products and  --
-- joins to products and joins. The upper map sends the unit to the   --
-- unit and the greatest grade to the greatest; it grades a delay `τ` --
-- by the span of at most `τ` admitting every operation, so it is a   --
-- grade morphism into `upperᵇ`, the upper grade with delays read as  --
-- such spans. The lower map sends the unit `{ ε }`, the greatest     --
-- guarantee, to the greatest grade `≥0`; the interval map sends the  --
-- unit to `(≥0 , ε)`. A run consistent with both ends of a trace     --
-- interval gives a word both translations admit, so the translated   --
-- ends are consistent.                                               --
--                                                                    --
-- The grades' orders are decided, the interval-letter ones by the    --
-- reader, so the decisions agree.                                    --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus

module Grades.Examples.Traces.Banked.ExactGrades
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Bool.Base using (Bool; true; false; _∧_) renaming (T to IsTrue)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (⁅_⁆) renaming (⊤ to all)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_; map; cartesianProductWith)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (find; lose) renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness; isYes)
import Data.Vec.Base as V

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T using (fin; ∞; ⁺; ⁻; ⊑⇒≤; ≤⇒⁺⊑⁺) renaming (_∣_ to _∣ᶜ_; ⊑-refl to ⊑ᶜ-refl)

open import Grades.Base using (Grade; GradeMorphism; _→ᵍ_)
open import Grades.Product using (_×ᵍ_)

open RunningTimes.RunningTimes running using (rt; costˡᵒ; costʰⁱ; cost-≤; costʰⁱ-pos)

open import Grades.Traces.Base T Op as Tr
  using (Trace; Trace⁻; operation; delay; operation⁻; inj⁻; ⟨_⟩; ⟨⟩-pos; ⟨⟩-zero; pos⁺)
  renaming (ε to εᵗ; ε⁻ to ε⁻ᵗ; _∙_ to _∙ᵗ_)
open import Grades.Traces.Sets T Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans using (NonEmpty; _·ˢ_)
open import Grades.Traces.Allowance.Core T Op costʰⁱ using (_≼ᵃ_)
open import Grades.Traces.Coverage.Core T Op costˡᵒ using (_≼ᶜ_)
import Grades.Traces.Allowance.Core T Op costʰⁱ as AC
import Grades.Traces.Coverage.Core T Op costˡᵒ as CC

import Grades.Examples.Traces.Banked.UpperBound
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos as BU
import Grades.Examples.Traces.Banked.LowerBound
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ as BL
import Grades.Examples.Traces.Banked.Interval
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos as BI

open import Grades.Exact.Base T Op n code code-injective using (Word; stretch; dur; dur-stretch; op; ∣_∣⁺)
open import Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-refl; ⊑-trans; ⊑-dur)
open import Grades.Exact.Lift T Op n code code-injective
  using (Lang; 𝟏ᴸ; _·ᴸ_; _∪ᴸ_)
  renaming (_≈_ to _≈ᴸ_; _≾_ to _≾ᴸ_; ≾-refl to ≾ᴸ-refl; ≾-trans to ≾ᴸ-trans)
open import Grades.Exact.Expression T Op n code code-injective running
  using (Instance; upper; lower; Expr; ε; ops; str; _∣_; _·_; ‵_; _ˀ; ⟦_⟧; strᴸ)
open import Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos
  using (starFree; words; strWords; members; opw; nonEmpty; Proper)
open import Grades.Exact.Finite.Grades T Op n code code-injective name code-name running dense κ κ-pos
  using (Proper′; ⌜_⌝; expr; _·ᵉ_; _∣ᵉ_; εᵉ; _≾ᵉ_; _≾ᵉ?_; _≾ᴳ_; decided; by-reader; upperᵍ; lowerᵍ)

open import Grades.Exact.Finite.Interval T Op n code code-injective name code-name running dense κ κ-pos
  using (Consistent; intervalᵍ)
open RunningTimes.RunningTimes running using (rt-inhabited⁺)
import Grades.Exact.Lift T Op n code code-injective as LiftM
import Grades.Exact.Banked.Upper T Op n code code-injective running dense κ κ-pos as U
import Grades.Exact.Banked.Lower T Op n code code-injective running dense κ κ-pos as L
open import Grades.Exact.Banked.Base T Op n code code-injective running
  using (stretch-0; span-split)

------------------------------------------------------------------------
-- The decided order and the order of the denotations

private
  ↑ : ∀ {s} (c d : Proper′ s) → c ≾ᵉ d → c ≾ᴳ d
  ↑ c d p = decided (fromWitness {a? = c ≾ᵉ? d} p)

  ↓ : ∀ {s} (c d : Proper′ s) → c ≾ᴳ d → c ≾ᵉ d
  ↓ c d p = toWitness {a? = c ≾ᵉ? d} (by-reader p)

  ↑² : ∀ {s} (c d : Proper′ s) → ⟦ expr c ⟧ ≈ᴸ ⟦ expr d ⟧ → c ≾ᴳ d × d ≾ᴳ c
  ↑² c d (p , q) = ↑ c d p , ↑ d c q

  ≈-sym : ∀ {X Y : Lang} → X ≈ᴸ Y → Y ≈ᴸ X
  ≈-sym (a , b) = b , a

  ≈-trans : ∀ {X Y Z : Lang} → X ≈ᴸ Y → Y ≈ᴸ Z → X ≈ᴸ Z
  ≈-trans (a , b) (c , d) = ≾ᴸ-trans a c , ≾ᴸ-trans d b

  ⊆⇒≈ : ∀ {X Y : Lang} → (∀ {w} → X w → Y w) → (∀ {w} → Y w → X w) → X ≈ᴸ Y
  ⊆⇒≈ f g = (λ w w∈ → w , f w∈ , ⊑-refl) , (λ w w∈ → w , g w∈ , ⊑-refl)

------------------------------------------------------------------------
-- Finite expressions with a word

private
  ∧-intro : ∀ {a b} → IsTrue a → IsTrue b → IsTrue (a ∧ b)
  ∧-intro {true} _ t = t

  NE : ∀ {A : Set} → List A → Set
  NE xs = IsTrue (nonEmpty xs)

  ne-++ʳ : ∀ {A : Set} (xs ys : List A) → NE ys → NE (xs ++ ys)
  ne-++ʳ []      ys t = t
  ne-++ʳ (_ ∷ _) ys _ = tt

  ne-map : ∀ {A B : Set} (f : A → B) xs → NE xs → NE (map f xs)
  ne-map f (_ ∷ _) _ = tt

  ne-cp : ∀ {A : Set} (f : A → A → A) xs ys → NE xs → NE ys → NE (cartesianProductWith f xs ys)
  ne-cp f (x ∷ xs) (y ∷ ys) _ _ = tt

  ne-members : ∀ {m} (c : Fin m) → NE (members ⁅ c ⁆)
  ne-members zero    = tt
  ne-members (suc c) = ne-map suc (members ⁅ c ⁆) (ne-members c)

  ne-op : ∀ {s} o → NE (words {s} (‵ o))
  ne-op o = ne-map opw (members ⁅ code o ⁆) (ne-members (code o))

  ne-strU : ∀ τ → NE (strWords upper all (fin (τ ∣ᶜ ⁺)))
  ne-strU τ with 0ᴰ <ᴰ? τ
  ... | yes _ = tt
  ... | no _  = tt

  ne-strL : ∀ τ → NE (strWords lower all (τ ∣ᶜ ⁻))
  ne-strL τ with 0ᴰ <ᴰ? τ
  ... | yes _ = tt
  ... | no _  = tt

  mutual

    sf-up : ∀ t → IsTrue (starFree (U.up t))
    sf-up εᵗ              = tt
    sf-up (operation o t) = sf-up t
    sf-up (delay d t⁻)    = sf-up⁻ t⁻

    sf-up⁻ : ∀ t⁻ → IsTrue (starFree (U.up⁻ t⁻))
    sf-up⁻ ε⁻ᵗ              = tt
    sf-up⁻ (operation⁻ o t) = sf-up t

  mutual

    ne-up : ∀ t → NE (words (U.up t))
    ne-up εᵗ              = tt
    ne-up (operation o t) =
      ne-cp _ (words (‵_ {upper} o) ++ [] ∷ []) _ (ne-++ʳ (words (‵_ {upper} o)) _ tt) (ne-up t)
    ne-up (delay d t⁻)    = ne-cp _ _ _ (ne-strU Tr.∣ d ∣⁺) (ne-up⁻ t⁻)

    ne-up⁻ : ∀ t⁻ → NE (words (U.up⁻ t⁻))
    ne-up⁻ ε⁻ᵗ              = tt
    ne-up⁻ (operation⁻ o t) =
      ne-cp _ (words (‵_ {upper} o) ++ [] ∷ []) _ (ne-++ʳ (words (‵_ {upper} o)) _ tt) (ne-up t)

  mutual

    sf-lo : ∀ t → IsTrue (starFree (L.lo t))
    sf-lo εᵗ              = tt
    sf-lo (operation o t) = sf-lo t
    sf-lo (delay d t⁻)    = sf-lo⁻ t⁻

    sf-lo⁻ : ∀ t⁻ → IsTrue (starFree (L.lo⁻ t⁻))
    sf-lo⁻ ε⁻ᵗ              = tt
    sf-lo⁻ (operation⁻ o t) = sf-lo t

  mutual

    ne-lo : ∀ t → NE (words (L.lo t))
    ne-lo εᵗ              = ne-strL 0ᴰ
    ne-lo (operation o t) =
      ne-cp _ _ _ (ne-strL 0ᴰ) (ne-cp _ _ _ (ne-op {lower} o) (ne-lo t))
    ne-lo (delay d t⁻)    = ne-cp _ _ _ (ne-strL Tr.∣ d ∣⁺) (ne-lo⁻ t⁻)

    ne-lo⁻ : ∀ t⁻ → NE (words (L.lo⁻ t⁻))
    ne-lo⁻ ε⁻ᵗ              = ne-strL 0ᴰ
    ne-lo⁻ (operation⁻ o t) =
      ne-cp _ _ _ (ne-strL 0ᴰ) (ne-cp _ _ _ (ne-op {lower} o) (ne-lo t))

-- the translations, as grades of each instance

upᵉ : Trace → Proper′ upper
upᵉ t = ⌜ U.up t ⌝ {∧-intro {starFree (U.up t)} (sf-up t) (ne-up t)}

loᵉ : Trace → Proper′ lower
loᵉ t = ⌜ L.lo t ⌝ {∧-intro {starFree (L.lo t)} (sf-lo t) (ne-lo t)}

------------------------------------------------------------------------
-- Unions of translations, at either order

module Lifted {s : Instance} (tr : Trace → Proper′ s)
  (R : Trace → Trace → Set)
  (sound : ∀ {v y} → R v y → ⟦ expr (tr v) ⟧ ≾ᴸ ⟦ expr (tr y) ⟧)
  (reflect : ∀ v ys → ⟦ expr (tr v) ⟧ ≾ᴸ (λ w → Any (λ y → ⟦ expr (tr y) ⟧ w) ys) → Any (R v) ys)
  (R-refl : ∀ v → R v v)
  (∙-sem : ∀ p q → ⟦ expr (tr (p ∙ᵗ q)) ⟧ ≈ᴸ (⟦ expr (tr p) ⟧ ·ᴸ ⟦ expr (tr q) ⟧))
  (nf : List Trace → List Trace)
  (nf-∈⁻ : ∀ {v xs} → v ∈ˡ nf xs → v ∈ˡ xs)
  (nf-◃⁻ : ∀ xs {v} → Any (R v) xs → Any (R v) (nf xs))
  where

  ⋃ᵉ : Trace → List Trace → Proper′ s
  ⋃ᵉ t []        = tr t
  ⋃ᵉ t (t′ ∷ ts) = tr t ∣ᵉ ⋃ᵉ t′ ts

  ⋃ᴾ : (xs : List Trace) → NonEmpty xs → Proper′ s
  ⋃ᴾ (t ∷ ts) _ = ⋃ᵉ t ts

  -- the runs of some listed translation

  Uᴸ : List Trace → Lang
  Uᴸ xs w = Any (λ t → ⟦ expr (tr t) ⟧ w) xs

  private
    ⋃→ : ∀ t ts {w} → ⟦ expr (⋃ᵉ t ts) ⟧ w → Uᴸ (t ∷ ts) w
    ⋃→ t []        w∈        = here w∈
    ⋃→ t (t′ ∷ ts) (inj₁ w∈) = here w∈
    ⋃→ t (t′ ∷ ts) (inj₂ w∈) = there (⋃→ t′ ts w∈)

    ⋃← : ∀ t ts {w} → Uᴸ (t ∷ ts) w → ⟦ expr (⋃ᵉ t ts) ⟧ w
    ⋃← t []        (here w∈)  = w∈
    ⋃← t (t′ ∷ ts) (here w∈)  = inj₁ w∈
    ⋃← t (t′ ∷ ts) (there a)  = inj₂ (⋃← t′ ts a)

  sem→ : ∀ xs nx {w} → ⟦ expr (⋃ᴾ xs nx) ⟧ w → Uᴸ xs w
  sem→ (t ∷ ts) _ = ⋃→ t ts

  sem← : ∀ xs nx {w} → Uᴸ xs w → ⟦ expr (⋃ᴾ xs nx) ⟧ w
  sem← (t ∷ ts) _ = ⋃← t ts

  -- the order: each listed trace related to one listed above

  ≾⇔ : ∀ xs ys nx ny
     → (∀ {v} → v ∈ˡ xs → Any (R v) ys) ⇔ (⟦ expr (⋃ᴾ xs nx) ⟧ ≾ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧)
  ≾⇔ xs ys nx ny = mk⇔ to from
    where
      to : (∀ {v} → v ∈ˡ xs → Any (R v) ys) → ⟦ expr (⋃ᴾ xs nx) ⟧ ≾ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧
      to h w w∈ with find (sem→ xs nx w∈)
      ... | v , v∈ , w∈v with find (h v∈)
      ...   | y , y∈ , r with sound r w w∈v
      ...     | z , z∈ , fit = z , sem← ys ny (lose y∈ z∈) , fit
      from : ⟦ expr (⋃ᴾ xs nx) ⟧ ≾ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧ → ∀ {v} → v ∈ˡ xs → Any (R v) ys
      from f {v} v∈ = reflect v ys g
        where
          g : ⟦ expr (tr v) ⟧ ≾ᴸ Uᴸ ys
          g w w∈ with f w (sem← xs nx (lose v∈ w∈))
          ... | z , z∈ , fit = z , sem→ ys ny z∈ , fit

  -- products of normal forms

  ·-sem : ∀ xs ys nx ny nz
        → ⟦ expr (⋃ᴾ (nf (xs ·ˢ ys)) nz) ⟧ ≈ᴸ (⟦ expr (⋃ᴾ xs nx) ⟧ ·ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧)
  ·-sem xs ys nx ny nz = to , from
    where
      to : ⟦ expr (⋃ᴾ (nf (xs ·ˢ ys)) nz) ⟧ ≾ᴸ (⟦ expr (⋃ᴾ xs nx) ⟧ ·ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧)
      to w w∈ with find (sem→ _ nz w∈)
      ... | r , r∈ , w∈r with ∈-cartesianProductWith⁻ _∙ᵗ_ xs ys (nf-∈⁻ r∈)
      ...   | p , q , p∈ , q∈ , refl with proj₁ (∙-sem p q) w w∈r
      ...     | _ , (z₁ , z₂ , refl , z₁∈ , z₂∈) , fit =
        z₁ ++ z₂ , (z₁ , z₂ , refl , sem← xs nx (lose p∈ z₁∈) , sem← ys ny (lose q∈ z₂∈)) , fit
      from : (⟦ expr (⋃ᴾ xs nx) ⟧ ·ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧) ≾ᴸ ⟦ expr (⋃ᴾ (nf (xs ·ˢ ys)) nz) ⟧
      from _ (w₁ , w₂ , refl , w₁∈ , w₂∈) with find (sem→ xs nx w₁∈) | find (sem→ ys ny w₂∈)
      ... | p , p∈ , w₁∈p | q , q∈ , w₂∈q
        with proj₂ (∙-sem p q) (w₁ ++ w₂) (w₁ , w₂ , refl , w₁∈p , w₂∈q)
      ...   | y , y∈ , fit
        with find (nf-◃⁻ (xs ·ˢ ys) (lose (∈-cartesianProductWith⁺ _∙ᵗ_ p∈ q∈) (R-refl (p ∙ᵗ q))))
      ...     | r , r∈ , rel with sound rel y y∈
      ...       | z , z∈ , fit′ = z , sem← _ nz (lose r∈ z∈) , ⊑-trans fit fit′

  -- joins of normal forms

  ⊔-sem : ∀ xs ys nx ny nz
        → ⟦ expr (⋃ᴾ (nf (xs ++ ys)) nz) ⟧ ≈ᴸ (⟦ expr (⋃ᴾ xs nx) ⟧ ∪ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧)
  ⊔-sem xs ys nx ny nz = to , from
    where
      to : ⟦ expr (⋃ᴾ (nf (xs ++ ys)) nz) ⟧ ≾ᴸ (⟦ expr (⋃ᴾ xs nx) ⟧ ∪ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧)
      to w w∈ with find (sem→ _ nz w∈)
      ... | r , r∈ , w∈r with ∈-++⁻ xs (nf-∈⁻ r∈)
      ...   | inj₁ m = w , inj₁ (sem← xs nx (lose m w∈r)) , ⊑-refl
      ...   | inj₂ m = w , inj₂ (sem← ys ny (lose m w∈r)) , ⊑-refl
      lift : ∀ {v w} → v ∈ˡ xs ++ ys → ⟦ expr (tr v) ⟧ w
           → Σ[ z ∈ Word ] ⟦ expr (⋃ᴾ (nf (xs ++ ys)) nz) ⟧ z × w ⊑ z
      lift {v} {w} m w∈ with find (nf-◃⁻ (xs ++ ys) (lose m (R-refl v)))
      ... | r , r∈ , rel with sound rel w w∈
      ...   | z , z∈ , fit = z , sem← _ nz (lose r∈ z∈) , fit
      from : (⟦ expr (⋃ᴾ xs nx) ⟧ ∪ᴸ ⟦ expr (⋃ᴾ ys ny) ⟧) ≾ᴸ ⟦ expr (⋃ᴾ (nf (xs ++ ys)) nz) ⟧
      from w (inj₁ w∈) with find (sem→ xs nx w∈)
      ... | v , v∈ , w∈v = lift (∈-++⁺ˡ v∈) w∈v
      from w (inj₂ w∈) with find (sem→ ys ny w∈)
      ... | v , v∈ , w∈v = lift (∈-++⁺ʳ xs v∈) w∈v

------------------------------------------------------------------------
-- Allowances: the upper map

private
  module UL = Lifted upᵉ _≼ᵃ_ U.sound U.reflect
                (λ v → AC.≼ᵃ-refl v)
                U.up-∙ BU.n (λ {v} {xs} → BU.n-∈⁻ {v} {xs}) BU.n-◃⁻

  ⊤ᵁ : Proper′ upper
  ⊤ᵁ = ⌜ str all ∞ ⌝

upᴮ : BU.Bounds → Proper′ upper
upᴮ (BU.within P) = UL.⋃ᴾ (BU.traces P) (BU.nonempty P)
upᴮ BU.unbounded  = ⊤ᵁ

private
  ε∈⋃ : ∀ xs nx → ⟦ expr (UL.⋃ᴾ xs nx) ⟧ []
  ε∈⋃ (t ∷ ts) nx = UL.sem← (t ∷ ts) nx (here (U.ε∈ t))

  ε∈ᴮ : ∀ B → ⟦ expr (upᴮ B) ⟧ []
  ε∈ᴮ (BU.within P) = ε∈⋃ (BU.traces P) (BU.nonempty P)
  ε∈ᴮ BU.unbounded  = 0ᴰ , tt , sym (stretch-0 all)

  ≾⊤ : ∀ c → c ≾ᴳ ⊤ᵁ
  ≾⊤ = Grade.≾-⊤ upperᵍ

  -- written-out bounds do not reach the unrestricted stretch

  totals : List Trace → Carrier
  totals []       = 0ᴰ
  totals (t ∷ ts) = U.total t +ᴰ totals ts

  total-≤ : ∀ {t} ts → t ∈ˡ ts → U.total t ≤ᴰ totals ts
  total-≤ (t ∷ ts) (here refl) = ≤ᴰ-+ (U.total t) (totals ts)
  total-≤ (t ∷ ts) (there m)   = ≤ᴰ-trans (total-≤ ts m) (≤ᴰ-+ˡ (totals ts) (U.total t))

  no-top : ∀ P → ¬ (⟦ expr ⊤ᵁ ⟧ ≾ᴸ ⟦ expr (upᴮ (BU.within P)) ⟧)
  no-top P f with f (stretch all (B +ᴰ κ)) (B +ᴰ κ , tt , refl)
    where B = totals (BU.traces P)
  ... | y , y∈ , fit with find (UL.sem→ (BU.traces P) (BU.nonempty P) y∈)
  ...   | q , q∈ , y∈q = κ-pos (+ᴰ-cancelˡ-≤ B (subst (_≤ᴰ B +ᴰ 0ᴰ) eq (≤ᴰ-trans (U.up-dur q y∈q) bound)))
    where
      B = totals (BU.traces P)
      eq : dur y ≡ B +ᴰ κ
      eq = trans (sym (⊑-dur fit)) (dur-stretch all (B +ᴰ κ))
      bound : U.total q ≤ᴰ B +ᴰ 0ᴰ
      bound = subst (U.total q ≤ᴰ_) (sym (+ᴰ-identityʳ B)) (total-≤ (BU.traces P) q∈)

-- the upper map preserves and reflects the order

up-≾⇔ : ∀ P Q → P BU.≾ Q ⇔ upᴮ P ≾ᴳ upᴮ Q
up-≾⇔ (BU.within P) (BU.within Q) = mk⇔
  (λ p → ↑ _ _ (Equivalence.to (UL.≾⇔ (BU.traces P) (BU.traces Q) (BU.nonempty P) (BU.nonempty Q))
                  (λ m → BU.≾ˢ-◃ {BU.traces P} {BU.traces Q} p m)))
  (λ g → BU.◃-≾ˢ {BU.traces P} {BU.traces Q}
           (Equivalence.from (UL.≾⇔ (BU.traces P) (BU.traces Q) (BU.nonempty P) (BU.nonempty Q))
              (↓ _ _ g)))
up-≾⇔ (BU.within P) BU.unbounded = mk⇔ (λ _ → ≾⊤ _) (λ _ → tt)
up-≾⇔ BU.unbounded (BU.within Q) = mk⇔ (λ ()) (λ g → ⊥-elim (no-top Q (↓ _ _ g)))
up-≾⇔ BU.unbounded BU.unbounded  = mk⇔ (λ _ → ≾⊤ _) (λ _ → tt)

-- products, joins, the unit and the greatest grade

private
  ⊤≾·ʳ : ∀ B → ⊤ᵁ ≾ᴳ (upᴮ B ·ᵉ ⊤ᵁ)
  ⊤≾·ʳ B = ↑ _ _ (λ w w∈ → w , ([] , w , refl , ε∈ᴮ B , w∈) , ⊑-refl)

  ⊤≾·ˡ : ∀ B → ⊤ᵁ ≾ᴳ (⊤ᵁ ·ᵉ upᴮ B)
  ⊤≾·ˡ B = ↑ _ _ (λ w w∈ → w ++ [] , (w , [] , refl , w∈ , ε∈ᴮ B) ,
                   subst (w ⊑_) (sym (++-identityʳ w)) ⊑-refl)

up-· : ∀ P Q → Grade._≃_ upperᵍ (upᴮ (P BU.·ᵇ Q)) (upᴮ P ·ᵉ upᴮ Q)
up-· (BU.within P) (BU.within Q) =
  ↑² _ _ (UL.·-sem (BU.traces P) (BU.traces Q) (BU.nonempty P) (BU.nonempty Q)
                   (BU.nonempty (P BU.· Q)))
up-· (BU.within P) BU.unbounded  = ⊤≾·ʳ (BU.within P) , ≾⊤ _
up-· BU.unbounded  Q             = ⊤≾·ˡ Q , ≾⊤ _

up-⊔ : ∀ P Q → Grade._≃_ upperᵍ (upᴮ (P BU.⊔ᵇ Q)) (upᴮ P ∣ᵉ upᴮ Q)
up-⊔ (BU.within P) (BU.within Q) =
  ↑² _ _ (UL.⊔-sem (BU.traces P) (BU.traces Q) (BU.nonempty P) (BU.nonempty Q)
                   (BU.nonempty (P BU.⊔ Q)))
up-⊔ (BU.within P) BU.unbounded  = Grade.⊔-ubʳ upperᵍ (upᴮ (BU.within P)) ⊤ᵁ , ≾⊤ _
up-⊔ BU.unbounded  Q             = Grade.⊔-ubˡ upperᵍ ⊤ᵁ (upᴮ Q) , ≾⊤ _

up-𝟏 : Grade._≃_ upperᵍ (upᴮ BU.𝟏ᵇ) εᵉ
up-𝟏 = Grade.≾-refl upperᵍ , Grade.≾-refl upperᵍ

up-⊤ : upᴮ BU.unbounded ≡ Grade.⊤ upperᵍ
up-⊤ = refl

------------------------------------------------------------------------
-- The upper grade with delays read as spans admitting every operation

spanᵁ : Carrier → Proper′ upper
spanᵁ τ = ⌜ str all (fin (τ ∣ᶜ ⁺)) ⌝ {ne-strU τ}

private
  span-zero : strᴸ {upper} all (fin (0ᴰ ∣ᶜ ⁺)) ≈ᴸ 𝟏ᴸ
  span-zero =
    ⊆⇒≈ (λ { (τ , r , refl) → trans (cong (stretch all) (≤0⇒≡0 (⊑⇒≤ r))) (stretch-0 all) })
        (λ { refl → 0ᴰ , ≤⇒⁺⊑⁺ ≤ᴰ-refl , sym (stretch-0 all) })

upperᵇ : Grade D
upperᵇ = record upperᵍ
  { ι           = spanᵁ
  ; ι-zero = ↑² (spanᵁ 0ᴰ) εᵉ span-zero
  ; ι-plus = λ {m} {k} → ↑² (spanᵁ (m +ᴰ k)) (spanᵁ m ·ᵉ spanᵁ k) (span-split all m k)
  }

private
  up-ι : ∀ τ → ⟦ U.up ⟨ τ ⟩ ⟧ ≈ᴸ strᴸ {upper} all (fin (τ ∣ᶜ ⁺))
  up-ι τ = case (0ᴰ <ᴰ? τ)
    where
      case : Dec (0ᴰ <ᴰ τ) → ⟦ U.up ⟨ τ ⟩ ⟧ ≈ᴸ strᴸ {upper} all (fin (τ ∣ᶜ ⁺))
      case (yes p) rewrite ⟨⟩-pos τ p =
        LiftM.·-identityʳ (strᴸ {upper} all (fin (τ ∣ᶜ ⁺)))
      case (no ¬p) rewrite ⟨⟩-zero τ ¬p | ≮0⇒≡0 ¬p = ≈-sym span-zero

-- the upper map is a grade algebra morphism into the grade algebra with
-- span delays

up-morphism : BU.upper-bound →ᵍ upperᵇ
up-morphism = record
  { map          = upᴮ
  ; map-monotone = λ {c} {c′} → Equivalence.to (up-≾⇔ c c′)
  ; map-𝟏        = up-𝟏
  ; map-·        = λ {c} {c′} → up-· c c′
  ; map-⊤        = Grade.≾-refl upperᵍ , Grade.≾-refl upperᵍ
  ; map-⊔        = λ {c} {c′} → up-⊔ c c′
  ; map-ι        = λ {τ} → ↑² _ _ (up-ι τ)
  }

------------------------------------------------------------------------
-- Guarantees: the lower map

private
  module LL = Lifted loᵉ (λ v y → y ≼ᶜ v) L.sound L.reflect
                (λ v → CC.≼ᶜ-refl v)
                L.lo-∙ BL.n (λ {v} {xs} → BL.n-∈⁻ {v} {xs}) BL.n-◃⁻

loᴬ : BL.Antichain → Proper′ lower
loᴬ P = LL.⋃ᴾ (BL.traces P) (BL.nonempty P)

-- the lower map preserves and reflects the order

lo-≾⇔ : ∀ P Q → P BL.≾ Q ⇔ loᴬ P ≾ᴳ loᴬ Q
lo-≾⇔ P Q = mk⇔
  (λ p → ↑ _ _ (Equivalence.to (LL.≾⇔ (BL.traces P) (BL.traces Q) (BL.nonempty P) (BL.nonempty Q))
                  (λ m → BL.≾ˢ-◃ {BL.traces P} {BL.traces Q} p m)))
  (λ g → BL.◃-≾ˢ {BL.traces P} {BL.traces Q}
           (Equivalence.from (LL.≾⇔ (BL.traces P) (BL.traces Q) (BL.nonempty P) (BL.nonempty Q))
              (↓ _ _ g)))

lo-· : ∀ P Q → Grade._≃_ lowerᵍ (loᴬ (P BL.· Q)) (loᴬ P ·ᵉ loᴬ Q)
lo-· P Q =
  ↑² _ _ (LL.·-sem (BL.traces P) (BL.traces Q) (BL.nonempty P) (BL.nonempty Q)
                   (BL.nonempty (P BL.· Q)))

lo-⊔ : ∀ P Q → Grade._≃_ lowerᵍ (loᴬ (P BL.⊔ Q)) (loᴬ P ∣ᵉ loᴬ Q)
lo-⊔ P Q =
  ↑² _ _ (LL.⊔-sem (BL.traces P) (BL.traces Q) (BL.nonempty P) (BL.nonempty Q)
                   (BL.nonempty (P BL.⊔ Q)))

-- the unit, the greatest guarantee, goes to the greatest grade

lo-𝟏 : Grade._≃_ lowerᵍ (loᴬ BL.𝟏) (Grade.⊤ lowerᵍ)
lo-𝟏 = ↑² _ _ (≾ᴸ-refl , ≾ᴸ-refl)

------------------------------------------------------------------------
-- Intervals: the two maps end by end

-- a word both translations of a trace admit: each operation at a
-- running time it admits, each delay a stretch of its length

private
  run  : Trace → Word
  run⁻ : Trace⁻ → Word
  run εᵗ              = []
  run (operation o t) = op o (proj₁ (rt-inhabited⁺ o)) ∷ run t
  run (delay d t⁻)    = stretch all ∣ d ∣⁺ ++ run⁻ t⁻
  run⁻ ε⁻ᵗ              = []
  run⁻ (operation⁻ o t) = op o (proj₁ (rt-inhabited⁺ o)) ∷ run t

  op-∈ : ∀ {s} o → ⟦ ‵_ {s} o ⟧ (op o (proj₁ (rt-inhabited⁺ o)) ∷ [])
  op-∈ o = o , proj₁ (rt-inhabited⁺ o) , x∈⁅x⁆ (code o) , proj₂ (rt-inhabited⁺ o) , refl

  ≥0-∈ : ⟦ L.≥0 ⟧ []
  ≥0-∈ = 0ᴰ , ⊑ᶜ-refl , sym (stretch-0 all)

  run-lo  : ∀ t → ⟦ L.lo t ⟧ (run t)
  run-lo⁻ : ∀ t → ⟦ L.lo⁻ t ⟧ (run⁻ t)
  run-lo εᵗ              = ≥0-∈
  run-lo (operation o t) = [] , _ , refl , ≥0-∈ , (_ , run t , refl , op-∈ {lower} o , run-lo t)
  run-lo (delay d t⁻)    = _ , run⁻ t⁻ , refl , (∣ d ∣⁺ , ⊑ᶜ-refl , refl) , run-lo⁻ t⁻
  run-lo⁻ ε⁻ᵗ              = ≥0-∈
  run-lo⁻ (operation⁻ o t) = [] , _ , refl , ≥0-∈ , (_ , run t , refl , op-∈ {lower} o , run-lo t)

  run-up  : ∀ t → ⟦ U.up t ⟧ (run t)
  run-up⁻ : ∀ t → ⟦ U.up⁻ t ⟧ (run⁻ t)
  run-up εᵗ              = refl
  run-up (operation o t) = _ , run t , refl , inj₁ (op-∈ {upper} o) , run-up t
  run-up (delay d t⁻)    = _ , run⁻ t⁻ , refl , (∣ d ∣⁺ , ≤⇒⁺⊑⁺ ≤ᴰ-refl , refl) , run-up⁻ t⁻
  run-up⁻ ε⁻ᵗ              = refl
  run-up⁻ (operation⁻ o t) = _ , run t , refl , inj₁ (op-∈ {upper} o) , run-up t

  -- a run consistent with a guarantee and an allowance makes their
  -- translations consistent
  lo-fits : ∀ P {p x} → p ∈ˡ BL.traces P → p ≼ᶜ x
          → Σ[ y ∈ Word ] ⟦ expr (loᴬ P) ⟧ y × run x ⊑ y
  lo-fits P {p} {x} p∈ px with Equivalence.to (L.≼ᶜ⇔ p x) px (run x) (run-lo x)
  ... | y , y∈ , xy = y , LL.sem← (BL.traces P) (BL.nonempty P) (lose p∈ y∈) , xy

  up-fits : ∀ Q {q x} → q ∈ˡ BU.traces Q → x ≼ᵃ q
          → Σ[ y ∈ Word ] ⟦ expr (upᴮ (BU.within Q)) ⟧ y × run x ⊑ y
  up-fits Q {q} {x} q∈ xq with Equivalence.to (U.≼ᵃ⇔ x q) xq (run x) (run-up x)
  ... | y , y∈ , xy = y , UL.sem← (BU.traces Q) (BU.nonempty Q) (lose q∈ y∈) , xy

  -- every word fits the unbounded allowance
  ⊤-fits : ∀ w → Σ[ y ∈ Word ] ⟦ expr ⊤ᵁ ⟧ y × w ⊑ y
  ⊤-fits w = stretch all (dur w) , (dur w , tt , refl) , LiftM.⊑-all w

  two-consistent : ∀ (P : BL.Antichain) (Y : BU.Bounds) → BL.traces P BI.◇ˢ Y
                 → Consistent (loᴬ P , upᴮ Y)
  two-consistent P (BU.within Q) c with BI.◇ˢ₀-elim c
  ... | BI.witness p∈ q∈ (x , px , xq) = run x , lo-fits P p∈ px , up-fits Q q∈ xq
  two-consistent P BU.unbounded _ = first (BL.traces P) (BL.nonempty P) (λ m → m)
    where
      first : ∀ xs → NonEmpty xs → (∀ {p} → p ∈ˡ xs → p ∈ˡ BL.traces P)
            → Consistent (loᴬ P , ⊤ᵁ)
      first (p ∷ _) _ f =
        run p , lo-fits P (f (here refl)) (CC.≼ᶜ-refl p) , ⊤-fits (run p)

two : BI.Interval → Grade.Carrier intervalᵍ
two i = (loᴬ (BI.lo i) , upᴮ (BI.hi i)) , two-consistent (BI.lo i) (BI.hi i) (BI.lo◇hi i)

private
  G₂ : Grade D
  G₂ = intervalᵍ

two-≾⇔ : ∀ i j → i BI.≾ᵗˢ j ⇔ Grade._≾_ G₂ (two i) (two j)
two-≾⇔ i j = mk⇔
  (λ (l , h) → Equivalence.to (lo-≾⇔ (BI.lo i) (BI.lo j)) l , Equivalence.to (up-≾⇔ (BI.hi i) (BI.hi j)) h)
  (λ (l , h) → Equivalence.from (lo-≾⇔ (BI.lo i) (BI.lo j)) l , Equivalence.from (up-≾⇔ (BI.hi i) (BI.hi j)) h)

two-· : ∀ i j → Grade._≃_ G₂ (two (i BI.·ᵗˢ j)) (Grade._·_ G₂ (two i) (two j))
two-· i j =
  (proj₁ (lo-· (BI.lo i) (BI.lo j)) , proj₁ (up-· (BI.hi i) (BI.hi j))) ,
  (proj₂ (lo-· (BI.lo i) (BI.lo j)) , proj₂ (up-· (BI.hi i) (BI.hi j)))

two-⊔ : ∀ i j → Grade._≃_ G₂ (two (i BI.⊔ᵗˢ j)) (Grade._⊔_ G₂ (two i) (two j))
two-⊔ i j =
  (proj₁ (lo-⊔ (BI.lo i) (BI.lo j)) , proj₁ (up-⊔ (BI.hi i) (BI.hi j))) ,
  (proj₂ (lo-⊔ (BI.lo i) (BI.lo j)) , proj₂ (up-⊔ (BI.hi i) (BI.hi j)))

-- the unit goes to the guarantee of nothing under the empty run

two-𝟏 : Grade._≃_ G₂ (two BI.𝟏ᵗˢ) ((Grade.⊤ lowerᵍ , εᵉ) , [] , ([] , ≥0-∈ , ⊑-refl) , ([] , refl , ⊑-refl))
two-𝟏 = (proj₁ lo-𝟏 , proj₁ up-𝟏) , (proj₂ lo-𝟏 , proj₂ up-𝟏)

two-⊤ : Grade._≃_ G₂ (two BI.⊤ᵗˢ) (Grade.⊤ G₂)
two-⊤ = (proj₁ lo-𝟏 , Grade.≾-refl upperᵍ) , (proj₂ lo-𝟏 , Grade.≾-refl upperᵍ)

------------------------------------------------------------------------
-- The decisions agree

private
  isYes-⇔ : ∀ {A B : Set} → A ⇔ B → (a : Dec A) (b : Dec B) → isYes a ≡ isYes b
  isYes-⇔ e (yes _) (yes _) = refl
  isYes-⇔ e (yes a) (no ¬b) = ⊥-elim (¬b (Equivalence.to e a))
  isYes-⇔ e (no ¬a) (yes b) = ⊥-elim (¬a (Equivalence.from e b))
  isYes-⇔ e (no _)  (no _)  = refl

up-decides : ∀ P Q → isYes (P BU.≾? Q) ≡ isYes (Grade._≾?_ upperᵍ (upᴮ P) (upᴮ Q))
up-decides P Q = isYes-⇔ (up-≾⇔ P Q) _ _

lo-decides : ∀ P Q → isYes (Grade._≾?_ BL.lower-bound P Q) ≡ isYes (Grade._≾?_ lowerᵍ (loᴬ P) (loᴬ Q))
lo-decides P Q = isYes-⇔ (lo-≾⇔ P Q) _ _

two-decides : ∀ i j → isYes (Grade._≾?_ BI.interval i j) ≡ isYes (Grade._≾?_ G₂ (two i) (two j))
two-decides i j = isYes-⇔ (two-≾⇔ i j) _ _
