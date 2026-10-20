------------------------------------------------------------------------
-- The non-rigid timed trace grades as interval-letter grades.        --
--                                                                    --
-- A grade of written-out traces maps to the union of their           --
-- translations (`NonRigid.Upper`, `NonRigid.Lower`), at the costs of --
-- the running times:                                                 --
--                                                                    --
--   upper  `Timed.RightSided`  →  `upperᵍ`, `unbounded` to `≤∞`      --
--   lower  `Timed.LeftSided`   →  `lowerᵍ`                           --
--   both   `Timed.TwoSided`    →  `lowerᵍ ×ᵍ upperᵍ`, end by end     --
--                                                                    --
-- Each map preserves and reflects the order, and sends products and  --
-- joins to products and joins. The upper map sends the unit to the   --
-- unit and the greatest grade to the greatest; it grades a delay by  --
-- a budget, so it is a grade morphism into `upperᵇ`, the upper grade --
-- with delays read as budgets. The lower map sends the unit `{ ε }`, --
-- the greatest guarantee, to the greatest grade `≥0`; the interval   --
-- map sends the unit to `(≥0 , ε)`.                                  --
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

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.NonRigid.Grades
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

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T using (fin; ∞; ⁺; ⁻; ⊑⇒≤; ≤⇒⁺⊑⁺) renaming (_∣_ to _∣ᶜ_)

open import Syntax.Grades using (Grade; GradeMorphism; _→ᵍ_)
open import Syntax.Grades.Product using (_×ᵍ_)

open RunningTimes.RunningTimes running using (rt; costˡᵒ; costʰⁱ; cost-≤; costʰⁱ-pos)

open import Syntax.Grades.Traces.Base T Op as Tr
  using (Trace; Trace⁻; operation; delay; operation⁻; inj⁻; ⟨_⟩; ⟨⟩-pos; ⟨⟩-zero; pos⁺)
  renaming (ε to εᵗ; ε⁻ to ε⁻ᵗ; _∙_ to _∙ᵗ_)
open import Syntax.Grades.Traces.Sets T Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans using (NonEmpty; _·ˢ_)
open import Syntax.Grades.Traces.Allowance.Core T Op costʰⁱ using (_≼ᵃ_)
open import Syntax.Grades.Traces.Coverage.Core T Op costˡᵒ using (_≼ᶜ_)
import Syntax.Grades.Traces.Allowance.Core T Op costʰⁱ as AC
import Syntax.Grades.Traces.Coverage.Core T Op costˡᵒ as CC

import Syntax.Grades.Example.Traces.Timed.RightSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos as NR
import Syntax.Grades.Example.Traces.Timed.LeftSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ as NL
import Syntax.Grades.Example.Traces.Timed.TwoSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos as N2

open import Syntax.Grades.Exact.Base T Op n code code-injective using (Word; stretch; dur; dur-stretch)
open import Syntax.Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-refl; ⊑-trans; ⊑-dur)
open import Syntax.Grades.Exact.Lift T Op n code code-injective
  using (Lang; uᴸ; _·ᴸ_; _∪ᴸ_)
  renaming (_≈_ to _≈ᴸ_; _≾_ to _≾ᴸ_; ≾-refl to ≾ᴸ-refl; ≾-trans to ≾ᴸ-trans)
open import Syntax.Grades.Exact.Expression T Op n code code-injective running
  using (Instance; upper; lower; Expr; ε; ops; str; _∣_; _·_; ‵_; _？; ⟦_⟧; strᴸ)
open import Syntax.Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos
  using (starFree; words; strWords; members; opw; nonEmpty; Proper)
open import Syntax.Grades.Exact.Finite.Grades T Op n code code-injective name code-name running dense κ κ-pos
  using (Proper′; ⌜_⌝; expr; _·ᵉ_; _∣ᵉ_; εᵉ; _≾ᵉ_; _≾ᵉ?_; _≾ᴳ_; decided; by-reader; upperᵍ; lowerᵍ)

import Syntax.Grades.Exact.Lift T Op n code code-injective as LiftM
import Syntax.Grades.Exact.NonRigid.Upper T Op n code code-injective running dense κ κ-pos as U
import Syntax.Grades.Exact.NonRigid.Lower T Op n code code-injective running dense κ κ-pos as L
open import Syntax.Grades.Exact.NonRigid.Base T Op n code code-injective running
  using (stretch-0; budget-split)

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
                U.up-∙ NR.n (λ {v} {xs} → NR.n-∈⁻ {v} {xs}) NR.n-◃⁻

  ⊤ᵁ : Proper′ upper
  ⊤ᵁ = ⌜ str all ∞ ⌝

upᴮ : NR.Bounds → Proper′ upper
upᴮ (NR.within P) = UL.⋃ᴾ (NR.traces P) (NR.nonempty P)
upᴮ NR.unbounded  = ⊤ᵁ

private
  ε∈⋃ : ∀ xs nx → ⟦ expr (UL.⋃ᴾ xs nx) ⟧ []
  ε∈⋃ (t ∷ ts) nx = UL.sem← (t ∷ ts) nx (here (U.ε∈ t))

  ε∈ᴮ : ∀ B → ⟦ expr (upᴮ B) ⟧ []
  ε∈ᴮ (NR.within P) = ε∈⋃ (NR.traces P) (NR.nonempty P)
  ε∈ᴮ NR.unbounded  = 0ᴰ , tt , sym (stretch-0 all)

  ≾⊤ : ∀ c → c ≾ᴳ ⊤ᵁ
  ≾⊤ = Grade.≾-⊤ upperᵍ

  -- written-out bounds do not reach the unrestricted stretch

  spans : List Trace → Carrier
  spans []       = 0ᴰ
  spans (t ∷ ts) = U.span t +ᴰ spans ts

  span-≤ : ∀ {t} ts → t ∈ˡ ts → U.span t ≤ᴰ spans ts
  span-≤ (t ∷ ts) (here refl) = ≤ᴰ-+ (U.span t) (spans ts)
  span-≤ (t ∷ ts) (there m)   = ≤ᴰ-trans (span-≤ ts m) (≤ᴰ-+ˡ (spans ts) (U.span t))

  no-top : ∀ P → ¬ (⟦ expr ⊤ᵁ ⟧ ≾ᴸ ⟦ expr (upᴮ (NR.within P)) ⟧)
  no-top P f with f (stretch all (B +ᴰ κ)) (B +ᴰ κ , tt , refl)
    where B = spans (NR.traces P)
  ... | y , y∈ , fit with find (UL.sem→ (NR.traces P) (NR.nonempty P) y∈)
  ...   | q , q∈ , y∈q = κ-pos (+ᴰ-cancelˡ-≤ B (subst (_≤ᴰ B +ᴰ 0ᴰ) eq (≤ᴰ-trans (U.up-dur q y∈q) bound)))
    where
      B = spans (NR.traces P)
      eq : dur y ≡ B +ᴰ κ
      eq = trans (sym (⊑-dur fit)) (dur-stretch all (B +ᴰ κ))
      bound : U.span q ≤ᴰ B +ᴰ 0ᴰ
      bound = subst (U.span q ≤ᴰ_) (sym (+ᴰ-identityʳ B)) (span-≤ (NR.traces P) q∈)

-- the upper map preserves and reflects the order

up-≾⇔ : ∀ P Q → P NR.≾ Q ⇔ upᴮ P ≾ᴳ upᴮ Q
up-≾⇔ (NR.within P) (NR.within Q) = mk⇔
  (λ p → ↑ _ _ (Equivalence.to (UL.≾⇔ (NR.traces P) (NR.traces Q) (NR.nonempty P) (NR.nonempty Q))
                  (λ m → NR.≾ˢ-◃ {NR.traces P} {NR.traces Q} p m)))
  (λ g → NR.◃-≾ˢ {NR.traces P} {NR.traces Q}
           (Equivalence.from (UL.≾⇔ (NR.traces P) (NR.traces Q) (NR.nonempty P) (NR.nonempty Q))
              (↓ _ _ g)))
up-≾⇔ (NR.within P) NR.unbounded = mk⇔ (λ _ → ≾⊤ _) (λ _ → tt)
up-≾⇔ NR.unbounded (NR.within Q) = mk⇔ (λ ()) (λ g → ⊥-elim (no-top Q (↓ _ _ g)))
up-≾⇔ NR.unbounded NR.unbounded  = mk⇔ (λ _ → ≾⊤ _) (λ _ → tt)

-- products, joins, the unit and the greatest grade

private
  ⊤≾·ʳ : ∀ B → ⊤ᵁ ≾ᴳ (upᴮ B ·ᵉ ⊤ᵁ)
  ⊤≾·ʳ B = ↑ _ _ (λ w w∈ → w , ([] , w , refl , ε∈ᴮ B , w∈) , ⊑-refl)

  ⊤≾·ˡ : ∀ B → ⊤ᵁ ≾ᴳ (⊤ᵁ ·ᵉ upᴮ B)
  ⊤≾·ˡ B = ↑ _ _ (λ w w∈ → w ++ [] , (w , [] , refl , w∈ , ε∈ᴮ B) ,
                   subst (w ⊑_) (sym (++-identityʳ w)) ⊑-refl)

up-· : ∀ P Q → Grade._≃_ upperᵍ (upᴮ (P NR.·ᵇ Q)) (upᴮ P ·ᵉ upᴮ Q)
up-· (NR.within P) (NR.within Q) =
  ↑² _ _ (UL.·-sem (NR.traces P) (NR.traces Q) (NR.nonempty P) (NR.nonempty Q)
                   (NR.nonempty (P NR.· Q)))
up-· (NR.within P) NR.unbounded  = ⊤≾·ʳ (NR.within P) , ≾⊤ _
up-· NR.unbounded  Q             = ⊤≾·ˡ Q , ≾⊤ _

up-⊔ : ∀ P Q → Grade._≃_ upperᵍ (upᴮ (P NR.⊔ᵇ Q)) (upᴮ P ∣ᵉ upᴮ Q)
up-⊔ (NR.within P) (NR.within Q) =
  ↑² _ _ (UL.⊔-sem (NR.traces P) (NR.traces Q) (NR.nonempty P) (NR.nonempty Q)
                   (NR.nonempty (P NR.⊔ Q)))
up-⊔ (NR.within P) NR.unbounded  = Grade.⊔-ubʳ upperᵍ (upᴮ (NR.within P)) ⊤ᵁ , ≾⊤ _
up-⊔ NR.unbounded  Q             = Grade.⊔-ubˡ upperᵍ ⊤ᵁ (upᴮ Q) , ≾⊤ _

up-u : Grade._≃_ upperᵍ (upᴮ NR.uᵇ) εᵉ
up-u = Grade.≾-refl upperᵍ , Grade.≾-refl upperᵍ

up-⊤ : upᴮ NR.unbounded ≡ Grade.⊤ upperᵍ
up-⊤ = refl

------------------------------------------------------------------------
-- The upper grade with delays read as budgets

budgetᵁ : Carrier → Proper′ upper
budgetᵁ τ = ⌜ str all (fin (τ ∣ᶜ ⁺)) ⌝ {ne-strU τ}

private
  budget-zero : strᴸ {upper} all (fin (0ᴰ ∣ᶜ ⁺)) ≈ᴸ uᴸ
  budget-zero =
    ⊆⇒≈ (λ { (τ , r , refl) → trans (cong (stretch all) (≤0⇒≡0 (⊑⇒≤ r))) (stretch-0 all) })
        (λ { refl → 0ᴰ , ≤⇒⁺⊑⁺ ≤ᴰ-refl , sym (stretch-0 all) })

upperᵇ : Grade D
upperᵇ = record upperᵍ
  { of-dur      = budgetᵁ
  ; of-dur-zero = ↑² (budgetᵁ 0ᴰ) εᵉ budget-zero
  ; of-dur-plus = λ {m} {k} → ↑² (budgetᵁ (m +ᴰ k)) (budgetᵁ m ·ᵉ budgetᵁ k) (budget-split all m k)
  }

private
  up-of-dur : ∀ τ → ⟦ U.up ⟨ τ ⟩ ⟧ ≈ᴸ strᴸ {upper} all (fin (τ ∣ᶜ ⁺))
  up-of-dur τ = case (0ᴰ <ᴰ? τ)
    where
      case : Dec (0ᴰ <ᴰ τ) → ⟦ U.up ⟨ τ ⟩ ⟧ ≈ᴸ strᴸ {upper} all (fin (τ ∣ᶜ ⁺))
      case (yes p) rewrite ⟨⟩-pos τ p =
        LiftM.·-identityʳ (strᴸ {upper} all (fin (τ ∣ᶜ ⁺)))
      case (no ¬p) rewrite ⟨⟩-zero τ ¬p | ≮0⇒≡0 ¬p = ≈-sym budget-zero

-- the upper map is a grade morphism into the grade with budget delays

up-morphism : NR.right-sided →ᵍ upperᵇ
up-morphism = record
  { map          = upᴮ
  ; map-monotone = λ {c} {c′} → Equivalence.to (up-≾⇔ c c′)
  ; map-u        = up-u
  ; map-·        = λ {c} {c′} → up-· c c′
  ; map-⊤        = Grade.≾-refl upperᵍ , Grade.≾-refl upperᵍ
  ; map-⊔        = λ {c} {c′} → up-⊔ c c′
  ; map-of-dur   = λ {τ} → ↑² _ _ (up-of-dur τ)
  }

------------------------------------------------------------------------
-- Guarantees: the lower map

private
  module LL = Lifted loᵉ (λ v y → y ≼ᶜ v) L.sound L.reflect
                (λ v → CC.≼ᶜ-refl v)
                L.lo-∙ NL.n (λ {v} {xs} → NL.n-∈⁻ {v} {xs}) NL.n-◃⁻

loᴬ : NL.Antichain → Proper′ lower
loᴬ P = LL.⋃ᴾ (NL.traces P) (NL.nonempty P)

-- the lower map preserves and reflects the order

lo-≾⇔ : ∀ P Q → P NL.≾ Q ⇔ loᴬ P ≾ᴳ loᴬ Q
lo-≾⇔ P Q = mk⇔
  (λ p → ↑ _ _ (Equivalence.to (LL.≾⇔ (NL.traces P) (NL.traces Q) (NL.nonempty P) (NL.nonempty Q))
                  (λ m → NL.≾ˢ-◃ {NL.traces P} {NL.traces Q} p m)))
  (λ g → NL.◃-≾ˢ {NL.traces P} {NL.traces Q}
           (Equivalence.from (LL.≾⇔ (NL.traces P) (NL.traces Q) (NL.nonempty P) (NL.nonempty Q))
              (↓ _ _ g)))

lo-· : ∀ P Q → Grade._≃_ lowerᵍ (loᴬ (P NL.· Q)) (loᴬ P ·ᵉ loᴬ Q)
lo-· P Q =
  ↑² _ _ (LL.·-sem (NL.traces P) (NL.traces Q) (NL.nonempty P) (NL.nonempty Q)
                   (NL.nonempty (P NL.· Q)))

lo-⊔ : ∀ P Q → Grade._≃_ lowerᵍ (loᴬ (P NL.⊔ Q)) (loᴬ P ∣ᵉ loᴬ Q)
lo-⊔ P Q =
  ↑² _ _ (LL.⊔-sem (NL.traces P) (NL.traces Q) (NL.nonempty P) (NL.nonempty Q)
                   (NL.nonempty (P NL.⊔ Q)))

-- the unit, the greatest guarantee, goes to the greatest grade

lo-u : Grade._≃_ lowerᵍ (loᴬ NL.u) (Grade.⊤ lowerᵍ)
lo-u = ↑² _ _ (≾ᴸ-refl , ≾ᴸ-refl)

------------------------------------------------------------------------
-- Intervals: the two maps end by end

two : N2.TwoSided → Proper′ lower × Proper′ upper
two i = loᴬ (N2.lo i) , upᴮ (N2.hi i)

private
  G₂ : Grade D
  G₂ = lowerᵍ ×ᵍ upperᵍ

two-≾⇔ : ∀ i j → i N2.≾ᵗˢ j ⇔ Grade._≾_ G₂ (two i) (two j)
two-≾⇔ i j = mk⇔
  (λ (l , h) → Equivalence.to (lo-≾⇔ (N2.lo i) (N2.lo j)) l , Equivalence.to (up-≾⇔ (N2.hi i) (N2.hi j)) h)
  (λ (l , h) → Equivalence.from (lo-≾⇔ (N2.lo i) (N2.lo j)) l , Equivalence.from (up-≾⇔ (N2.hi i) (N2.hi j)) h)

two-· : ∀ i j → Grade._≃_ G₂ (two (i N2.·ᵗˢ j)) (Grade._·_ G₂ (two i) (two j))
two-· i j =
  (proj₁ (lo-· (N2.lo i) (N2.lo j)) , proj₁ (up-· (N2.hi i) (N2.hi j))) ,
  (proj₂ (lo-· (N2.lo i) (N2.lo j)) , proj₂ (up-· (N2.hi i) (N2.hi j)))

two-⊔ : ∀ i j → Grade._≃_ G₂ (two (i N2.⊔ᵗˢ j)) (Grade._⊔_ G₂ (two i) (two j))
two-⊔ i j =
  (proj₁ (lo-⊔ (N2.lo i) (N2.lo j)) , proj₁ (up-⊔ (N2.hi i) (N2.hi j))) ,
  (proj₂ (lo-⊔ (N2.lo i) (N2.lo j)) , proj₂ (up-⊔ (N2.hi i) (N2.hi j)))

-- the unit goes to the guarantee of nothing under the empty run

two-u : Grade._≃_ G₂ (two N2.uᵗˢ) (Grade.⊤ lowerᵍ , εᵉ)
two-u = (proj₁ lo-u , proj₁ up-u) , (proj₂ lo-u , proj₂ up-u)

two-⊤ : Grade._≃_ G₂ (two N2.⊤ᵗˢ) (Grade.⊤ G₂)
two-⊤ = (proj₁ lo-u , Grade.≾-refl upperᵍ) , (proj₂ lo-u , Grade.≾-refl upperᵍ)

------------------------------------------------------------------------
-- The decisions agree

private
  isYes-⇔ : ∀ {A B : Set} → A ⇔ B → (a : Dec A) (b : Dec B) → isYes a ≡ isYes b
  isYes-⇔ e (yes _) (yes _) = refl
  isYes-⇔ e (yes a) (no ¬b) = ⊥-elim (¬b (Equivalence.to e a))
  isYes-⇔ e (no ¬a) (yes b) = ⊥-elim (¬a (Equivalence.from e b))
  isYes-⇔ e (no _)  (no _)  = refl

up-decides : ∀ P Q → isYes (P NR.≾? Q) ≡ isYes (Grade._≾?_ upperᵍ (upᴮ P) (upᴮ Q))
up-decides P Q = isYes-⇔ (up-≾⇔ P Q) _ _

lo-decides : ∀ P Q → isYes (Grade._≾?_ NL.left-sided P Q) ≡ isYes (Grade._≾?_ lowerᵍ (loᴬ P) (loᴬ Q))
lo-decides P Q = isYes-⇔ (lo-≾⇔ P Q) _ _

two-decides : ∀ i j → isYes (Grade._≾?_ N2.two-sided i j) ≡ isYes (Grade._≾?_ G₂ (two i) (two j))
two-decides i j = isYes-⇔ (two-≾⇔ i j) _ _
