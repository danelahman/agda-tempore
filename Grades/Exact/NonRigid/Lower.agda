------------------------------------------------------------------------
-- Guarantees as lower interval-letter expressions.                   --
--                                                                    --
-- A timed trace read as a guarantee translates letter by letter,     --
-- activity allowed before every operation and at the end:            --
--                                                                    --
--   lo (o ; t)  =  ≥0 · o · lo t                                     --
--   lo (d ; t)  =  ≥d · lo t                                         --
--   lo ε        =  ≥0                                                --
--                                                                    --
-- where `≥d` is a stretch of at least `d` admitting every operation. --
-- Then, at the costs `costˡᵒ` of the running times,                  --
--                                                                    --
--   s ≼ᶜ t   iff   ⟦ lo t ⟧ ≾ ⟦ lo s ⟧                               --
--                                                                    --
-- and a run is below a union of guarantees when it covers one of     --
-- them. Soundness is by induction on the coverage, a stretch in      --
-- front of the run standing for the slack it has banked. Reflection  --
-- reads the word of the run without flanks at the lower reader: the  --
-- chains of a run of the reader bank what they pour and close by     --
-- paying the demands they span. The translation sends the product of --
-- traces to the product of expressions.                              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus

module Grades.Exact.NonRigid.Lower
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Fin.Subset using (⁅_⁆) renaming (⊤ to all)
open import Data.Fin.Subset.Properties using (x∈⁅y⁆⇒x≡y; x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; [_])
open import Data.List.Properties using (map-++; ++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (find) renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻; map⁺)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; ⁺; ⁻; 0⁺; 0⁻; pt; _+ˡ_; ⊑⇒≤; ≤⇒⁻⊑⁻; by-pt)
  renaming (_∣_ to _∣ᶜ_; lo to loⁱ; ⊑-refl to ⊑ᶜ-refl)
open import Grades.Durations.Intervals.Dense T using (_∈ⁱ_)

open RunningTimes.RunningTimes running using (rt; costˡᵒ; costˡᵒ-≤; costˡᵒ-dense)

open import Grades.Traces.Base T Op as Tr
  using (Trace; Trace⁻; operation; delay; operation⁻; inj⁻; prepend)
  renaming (ε to εᵗ; ε⁻ to ε⁻ᵗ; _∙_ to _∙ᵗ_)
open import Grades.Traces.Coverage.Core T Op costˡᵒ
  using (_≼ᶜ[_]_; _≼ᶜ_; nil; keep; pay-op; del-delay; use-delay)

open import Grades.Exact.Base T Op n code code-injective
  using (Word; OpSet; op; st; stretch; dur; D⁺; ∣_∣⁺; ∣∣⁺-pos; _+⁺_)
open import Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-trans) renaming (⊑-refl to ⊑ʷ-refl)
open import Grades.Exact.Lift T Op n code code-injective
  using (Lang; 𝟏ᴸ; _·ᴸ_; ⊑-++; ⊑-all; ·-mono; ·-assoc; ·-identityˡ; ·-identityʳ)
  renaming (_≈_ to _≈ᴸ_; _≾_ to _≾ᴸ_; ≾-refl to ≾ᴸ-refl; ≾-trans to ≾ᴸ-trans)
open import Grades.Exact.Expression T Op n code code-injective running
  using (Instance; lower; Expr; ε; ops; str; _∣_; _·_; ‵_; ⟦_⟧; strᴸ)
open import Grades.Exact.Letters T Op n code code-injective running
  using (Letter; op; st; Word′; ⟦_⟧ʷ; Kind; opk; stk)
open import Grades.Exact.Reader.Lower T Op n code code-injective running
  using (Pl; sumˡ; Fitsᴸ; RunL; ChL; done; match; start; pour; over; close)
open import Grades.Exact.Reader.Lower.Read T Op n code code-injective running
  using (ValidL)
open import Grades.Exact.Reader.Lower.Correct T Op n code code-injective running dense κ κ-pos
  using (symᴸ; AllValidL; UnionLᴸ; completeᴸ)
open import Grades.Exact.NonRigid.Base T Op n code code-injective running

------------------------------------------------------------------------
-- The translation

-- a stretch of at least a length, admitting every operation

≥ᶜ : Carrier → Expr lower
≥ᶜ τ = str all (τ ∣ᶜ ⁻)

≥0 : Expr lower
≥0 = ≥ᶜ 0ᴰ

mutual

  lo : Trace → Expr lower
  lo εᵗ              = ≥0
  lo (operation o t) = ≥0 · (‵ o · lo t)
  lo (delay d t⁻)    = ≥ᶜ ∣ d ∣⁺ · lo⁻ t⁻

  lo⁻ : Trace⁻ → Expr lower
  lo⁻ ε⁻ᵗ              = ≥0
  lo⁻ (operation⁻ o t) = ≥0 · (‵ o · lo t)

lo-inj⁻ : ∀ t⁻ → lo (inj⁻ t⁻) ≡ lo⁻ t⁻
lo-inj⁻ ε⁻ᵗ              = refl
lo-inj⁻ (operation⁻ o t) = refl

private
  to⁻ : ∀ t⁻ {y} → ⟦ lo (inj⁻ t⁻) ⟧ y → ⟦ lo⁻ t⁻ ⟧ y
  to⁻ t⁻ {y} = subst (λ e → ⟦ e ⟧ y) (lo-inj⁻ t⁻)

  from⁻ : ∀ t⁻ {y} → ⟦ lo⁻ t⁻ ⟧ y → ⟦ lo (inj⁻ t⁻) ⟧ y
  from⁻ t⁻ {y} = subst (λ e → ⟦ e ⟧ y) (sym (lo-inj⁻ t⁻))

  any≥0 : ∀ τ → strᴸ {lower} all (0ᴰ ∣ᶜ ⁻) (stretch all τ)
  any≥0 τ = τ , ≤⇒⁻⊑⁻ (0ᴰ-least τ) , refl

  -- a running time is at least the cost

  lo-≤ : ∀ o {τ} → τ ∈ⁱ rt o → costˡᵒ o ≤ᴰ τ
  lo-≤ = costˡᵒ-≤

------------------------------------------------------------------------
-- Soundness

-- a stretch of at least the banked slack, followed by a run of `lo t`,
-- fits a run of `lo s`

sound↓ : ∀ {k s t} → s ≼ᶜ[ k ] t → ∀ x → ⟦ lo t ⟧ x → ∀ a → k ≤ᴰ a
       → Σ[ y ∈ Word ] ⟦ lo s ⟧ y × stretch all a ++ x ⊑ y
sound↓ nil x x∈ a _ =
  stretch all (a +ᴰ dur x) , any≥0 (a +ᴰ dur x) ,
  ⊑-trans (⊑-++ (⊑ʷ-refl {stretch all a}) (⊑-all x)) (join⊑ all a (dur x))
sound↓ (keep {o = o} {s = s} d) _ (_ , _ , refl , (b , _ , refl) , (_ , x₂ , refl , (o′ , dd , c , r , refl) , x₂∈)) a _
  with code-injective (x∈⁅y⁆⇒x≡y (code o) c)
... | refl with sound↓ d x₂ x₂∈ 0ᴰ ≤ᴰ-refl
...   | y , y∈ , fit =
  stretch all (a +ᴰ b) ++ (op o dd ∷ [] ++ y) ,
  (stretch all (a +ᴰ b) , op o dd ∷ [] ++ y , refl , any≥0 (a +ᴰ b) ,
   (op o dd ∷ [] , y , refl , (o , dd , x∈⁅x⁆ (code o) , r , refl) , y∈)) ,
  join-front all a b
    (⊑-++ (⊑ʷ-refl {stretch all a}) (⊑-++ (⊑ʷ-refl {stretch all b})
      (⊑-++ (⊑ʷ-refl {op o dd ∷ []}) (subst (λ z → z ++ x₂ ⊑ y) (stretch-0 all) fit))))
sound↓ (pay-op {k = k} {o = o} d) _ (_ , _ , refl , (b , _ , refl) , (_ , x₂ , refl , (o′ , dd , c , r , refl) , x₂∈)) a ka
  with code-injective (x∈⁅y⁆⇒x≡y (code o) c)
... | refl with sound↓ d x₂ x₂∈ ((a +ᴰ b) +ᴰ ∣ dd ∣⁺)
                  (+ᴰ-mono-≤ (≤ᴰ-trans ka (≤ᴰ-+ a b)) (lo-≤ o r))
...   | y , y∈ , fit =
  y , y∈ ,
  ⊑-trans (join-front all (a +ᴰ b) ∣ dd ∣⁺
            (join-front all a b
              (⊑-++ (⊑ʷ-refl {stretch all a}) (⊑-++ (⊑ʷ-refl {stretch all b})
                (⊑-++ (⊑-all′ (op o dd ∷ []) (+ᴰ-identityʳ _)) (⊑ʷ-refl {x₂}))))))
          fit
sound↓ (del-delay {k = k} {e = e} {t⁻ = t⁻} d) _ (_ , x₂ , refl , (τ , r , refl) , x₂∈) a ka
  with sound↓ d x₂ (from⁻ t⁻ x₂∈) (a +ᴰ τ) (+ᴰ-mono-≤ ka (⊑⇒≤ r))
... | y , y∈ , fit = y , y∈ , ⊑-trans (join-front all a τ ⊑ʷ-refl) fit
sound↓ (use-delay {k = k} {d = d} {s⁻ = s⁻} p d′) x x∈ a ka
  with sound↓ d′ x x∈ (a ∸ᴰ ∣ d ∣⁺) (∸-monoˡ-≤ ∣ d ∣⁺ ka)
... | y , y∈ , fit =
  stretch all ∣ d ∣⁺ ++ y ,
  (stretch all ∣ d ∣⁺ , y , refl , (∣ d ∣⁺ , ⊑ᶜ-refl , refl) , to⁻ s⁻ y∈) ,
  ⊑-trans (split-front all ∣ d ∣⁺ (a ∸ᴰ ∣ d ∣⁺)
             (subst (λ z → stretch all a ++ x ⊑ stretch all z ++ x)
                    (sym (+-∸ (≤ᴰ-trans p ka))) ⊑ʷ-refl))
          (⊑-++ (⊑ʷ-refl {stretch all ∣ d ∣⁺}) fit)

sound : ∀ {s t} → s ≼ᶜ t → ⟦ lo t ⟧ ≾ᴸ ⟦ lo s ⟧
sound d x x∈ with sound↓ d x x∈ 0ᴰ ≤ᴰ-refl
... | y , y∈ , fit = y , y∈ , subst (λ z → z ++ x ⊑ y) (stretch-0 all) fit

------------------------------------------------------------------------
-- The word of a run without flanks

mutual

  fullᴸ : Trace → Word′ lower
  fullᴸ εᵗ              = []
  fullᴸ (operation o t) = op o ∷ fullᴸ t
  fullᴸ (delay d t⁻)    = st all (∣ d ∣⁺ ∣ᶜ ⁻) ∷ fullᴸ⁻ t⁻

  fullᴸ⁻ : Trace⁻ → Word′ lower
  fullᴸ⁻ ε⁻ᵗ              = []
  fullᴸ⁻ (operation⁻ o t) = op o ∷ fullᴸ t

private
  none≥0 : strᴸ {lower} all (0ᴰ ∣ᶜ ⁻) []
  none≥0 = 0ᴰ , ≤⇒⁻⊑⁻ ≤ᴰ-refl , sym (stretch-0 all)

mutual

  fullᴸ-⊆ : ∀ t {x} → ⟦ fullᴸ t ⟧ʷ x → ⟦ lo t ⟧ x
  fullᴸ-⊆ εᵗ refl = none≥0
  fullᴸ-⊆ (operation o t) (x₁ , x₂ , e , x₁∈ , x₂∈) =
    [] , _ , refl , none≥0 , (x₁ , x₂ , e , x₁∈ , fullᴸ-⊆ t x₂∈)
  fullᴸ-⊆ (delay d t⁻) (x₁ , x₂ , e , x₁∈ , x₂∈) = x₁ , x₂ , e , x₁∈ , fullᴸ-⊆⁻ t⁻ x₂∈

  fullᴸ-⊆⁻ : ∀ t⁻ {x} → ⟦ fullᴸ⁻ t⁻ ⟧ʷ x → ⟦ lo⁻ t⁻ ⟧ x
  fullᴸ-⊆⁻ ε⁻ᵗ refl = none≥0
  fullᴸ-⊆⁻ (operation⁻ o t) (x₁ , x₂ , e , x₁∈ , x₂∈) =
    [] , _ , refl , none≥0 , (x₁ , x₂ , e , x₁∈ , fullᴸ-⊆ t x₂∈)

mutual

  validL-full : ∀ t → ValidL (fullᴸ t)
  validL-full εᵗ              = tt
  validL-full (operation o t) = validL-full t
  validL-full (delay d t⁻)    = by-pt (∣∣⁺-pos d) , validL-full⁻ t⁻

  validL-full⁻ : ∀ t⁻ → ValidL (fullᴸ⁻ t⁻)
  validL-full⁻ ε⁻ᵗ              = tt
  validL-full⁻ (operation⁻ o t) = validL-full t

------------------------------------------------------------------------
-- The words of a translation

-- a flank of positive length

fl : Letter Cut
fl = st all (0ᴰ ∣ᶜ ⁺)

flanked : List (Word′ lower) → List (Word′ lower)
flanked ws = ws ++ map (fl ∷_) ws

mutual

  choicesᴸ : Trace → List (Word′ lower)
  choicesᴸ εᵗ              = flanked ([] ∷ [])
  choicesᴸ (operation o t) = flanked (map (op o ∷_) (choicesᴸ t))
  choicesᴸ (delay d t⁻)    = map (st all (∣ d ∣⁺ ∣ᶜ ⁻) ∷_) (choicesᴸ⁻ t⁻)

  choicesᴸ⁻ : Trace⁻ → List (Word′ lower)
  choicesᴸ⁻ ε⁻ᵗ              = flanked ([] ∷ [])
  choicesᴸ⁻ (operation⁻ o t) = flanked (map (op o ∷_) (choicesᴸ t))

-- a word of the guarantee: flanks anywhere, its operations, every delay
-- a demand

data ChoiceL : Trace → Word′ lower → Set where
  nilᶜ : ChoiceL εᵗ []
  flᶜ  : ∀ {s v} → ChoiceL s v → ChoiceL s (fl ∷ v)
  opᶜ  : ∀ {o s v} → ChoiceL s v → ChoiceL (operation o s) (op o ∷ v)
  delᶜ : ∀ {d s⁻ v} → ChoiceL (inj⁻ s⁻) v → ChoiceL (delay d s⁻) (st all (∣ d ∣⁺ ∣ᶜ ⁻) ∷ v)

private
  flank : ∀ τ ws {z} → Any (λ v → ⟦ v ⟧ʷ z) ws → Any (λ v → ⟦ v ⟧ʷ (stretch all τ ++ z)) (flanked ws)
  flank τ ws {z} a = case (0ᴰ <ᴰ? τ)
    where
      case : Dec (0ᴰ <ᴰ τ) → Any (λ v → ⟦ v ⟧ʷ (stretch all τ ++ z)) (flanked ws)
      case (yes p) = ++⁺ʳ ws (map⁺ (Any.map (λ v∈ → stretch all τ , z , refl , (τ , by-pt p , refl) , v∈) a))
      case (no ¬p) = ++⁺ˡ (subst (λ w → Any (λ v → ⟦ v ⟧ʷ (w ++ z)) ws)
                                 (sym (trans (cong (stretch all) (≮0⇒≡0 ¬p)) (stretch-0 all))) a)

mutual

  choicesᴸ-cover : ∀ t {y} → ⟦ lo t ⟧ y → Any (λ v → ⟦ v ⟧ʷ y) (choicesᴸ t)
  choicesᴸ-cover εᵗ (τ , _ , refl) =
    subst (λ y → Any (λ v → ⟦ v ⟧ʷ y) (choicesᴸ εᵗ)) (++-identityʳ (stretch all τ))
          (flank τ ([] ∷ []) (here refl))
  choicesᴸ-cover (operation o t) (_ , _ , refl , (τ , _ , refl) , (y₁ , y₂ , refl , y₁∈ , y₂∈)) =
    flank τ (map (op o ∷_) (choicesᴸ t))
      (map⁺ (Any.map (λ v∈ → y₁ , y₂ , refl , y₁∈ , v∈) (choicesᴸ-cover t y₂∈)))
  choicesᴸ-cover (delay d t⁻) (y₁ , y₂ , refl , y₁∈ , y₂∈) =
    map⁺ (Any.map (λ v∈ → y₁ , y₂ , refl , y₁∈ , v∈) (choicesᴸ-cover⁻ t⁻ y₂∈))

  choicesᴸ-cover⁻ : ∀ t⁻ {y} → ⟦ lo⁻ t⁻ ⟧ y → Any (λ v → ⟦ v ⟧ʷ y) (choicesᴸ⁻ t⁻)
  choicesᴸ-cover⁻ ε⁻ᵗ (τ , _ , refl) =
    subst (λ y → Any (λ v → ⟦ v ⟧ʷ y) (choicesᴸ⁻ ε⁻ᵗ)) (++-identityʳ (stretch all τ))
          (flank τ ([] ∷ []) (here refl))
  choicesᴸ-cover⁻ (operation⁻ o t) (_ , _ , refl , (τ , _ , refl) , (y₁ , y₂ , refl , y₁∈ , y₂∈)) =
    flank τ (map (op o ∷_) (choicesᴸ t))
      (map⁺ (Any.map (λ v∈ → y₁ , y₂ , refl , y₁∈ , v∈) (choicesᴸ-cover t y₂∈)))

private
  flanked-choice : ∀ {s} ws → (∀ {v} → v ∈ˡ ws → ChoiceL s v) → ∀ {v} → v ∈ˡ flanked ws → ChoiceL s v
  flanked-choice ws h m with ∈-++⁻ ws m
  ... | inj₁ m′ = h m′
  ... | inj₂ m′ with ∈-map⁻ (fl ∷_) m′
  ...   | v′ , m″ , refl = flᶜ (h m″)

  nil-choice : ∀ {v} → v ∈ˡ [] ∷ [] → ChoiceL εᵗ v
  nil-choice (here refl) = nilᶜ

mutual

  choicesᴸ-choice : ∀ t {v} → v ∈ˡ choicesᴸ t → ChoiceL t v
  choicesᴸ-choice εᵗ m = flanked-choice ([] ∷ []) nil-choice m
  choicesᴸ-choice (operation o t) m =
    flanked-choice (map (op o ∷_) (choicesᴸ t)) (op-choice o t) m
  choicesᴸ-choice (delay d t⁻) m with ∈-map⁻ (st all (∣ d ∣⁺ ∣ᶜ ⁻) ∷_) m
  ... | v′ , m′ , refl = delᶜ (choicesᴸ-choice⁻ t⁻ m′)

  choicesᴸ-choice⁻ : ∀ t⁻ {v} → v ∈ˡ choicesᴸ⁻ t⁻ → ChoiceL (inj⁻ t⁻) v
  choicesᴸ-choice⁻ ε⁻ᵗ m = flanked-choice ([] ∷ []) nil-choice m
  choicesᴸ-choice⁻ (operation⁻ o t) m =
    flanked-choice (map (op o ∷_) (choicesᴸ t)) (op-choice o t) m

  op-choice : ∀ o t {v} → v ∈ˡ map (op o ∷_) (choicesᴸ t) → ChoiceL (operation o t) v
  op-choice o t m with ∈-map⁻ (op o ∷_) m
  ... | v′ , m′ , refl = opᶜ (choicesᴸ-choice t m′)

choice-valid : ∀ {s v} → ChoiceL s v → ValidL v
choice-valid nilᶜ               = tt
choice-valid (flᶜ c)            = ⊑ᶜ-refl , choice-valid c
choice-valid (opᶜ c)            = choice-valid c
choice-valid (delᶜ {d = d} c)   = by-pt (∣∣⁺-pos d) , choice-valid c

------------------------------------------------------------------------
-- Reading a run of the reader as a coverage

-- the pieces of the word of a run

data PcsL : Trace → List Pl → Set where
  []ᵖ  : PcsL εᵗ []
  opᵖ  : ∀ {o t ps} → PcsL t ps → PcsL (operation o t) ((opk o , loⁱ (rt o)) ∷ ps)
  delᵖ : ∀ {d t⁻ ps} → PcsL (inj⁻ t⁻) ps
       → PcsL (delay d t⁻) ((stk all , (∣ d ∣⁺ ∣ᶜ ⁻)) ∷ ps)

mutual

  pcs-full : ∀ t → PcsL t (map symᴸ (fullᴸ t))
  pcs-full εᵗ              = []ᵖ
  pcs-full (operation o t) = opᵖ (pcs-full t)
  pcs-full (delay d t⁻)    = delᵖ (pcs-full⁻ t⁻)

  pcs-full⁻ : ∀ t⁻ → PcsL (inj⁻ t⁻) (map symᴸ (fullᴸ⁻ t⁻))
  pcs-full⁻ ε⁻ᵗ              = []ᵖ
  pcs-full⁻ (operation⁻ o t) = opᵖ (pcs-full t)

private
  Σˡ : List Cut → Carrier
  Σˡ []       = 0ᴰ
  Σˡ (c ∷ cs) = pt c +ᴰ Σˡ cs

  wts : List Pl → List Cut
  wts = map proj₂

  pt-+ˡ : ∀ c c′ → pt (c +ˡ c′) ≡ pt c +ᴰ pt c′
  pt-+ˡ (p ∣ᶜ s) (q ∣ᶜ t) = refl

  pt-sum : ∀ cs → pt (sumˡ cs) ≡ Σˡ cs
  pt-sum []       = refl
  pt-sum (c ∷ cs) = trans (pt-+ˡ c (sumˡ cs)) (cong (pt c +ᴰ_) (pt-sum cs))

  fits-pt : ∀ pre cs → Fitsᴸ pre cs → Σˡ cs ≤ᴰ Σˡ (wts pre)
  fits-pt pre cs f = subst₂ _≤ᴰ_ (pt-sum cs) (pt-sum (wts pre)) (⊑⇒≤ f)

  Σˡ-∷ʳ : ∀ (pre : List Pl) p → Σˡ (wts (pre ∷ʳ p)) ≡ Σˡ (wts pre) +ᴰ pt (proj₂ p)
  Σˡ-∷ʳ []       p = trans (+ᴰ-identityʳ _) (sym (+ᴰ-identityˡ _))
  Σˡ-∷ʳ (x ∷ pre) p =
    trans (cong (pt (proj₂ x) +ᴰ_) (Σˡ-∷ʳ pre p)) (sym (+ᴰ-assoc (pt (proj₂ x)) _ _))

  stl : OpSet × Cut → Letter Cut
  stl (S , c) = st S c

  -- a closed chain pays the demands it spans

  closeL : ∀ {s v k t} ls → ChoiceL s (map stl ls ++ v) → Σˡ (map proj₂ ls) ≤ᴰ k
         → (∀ {s′} → ChoiceL s′ v → ∀ k′ → s′ ≼ᶜ[ k′ ] t) → s ≼ᶜ[ k ] t
  closeL [] c b K = K c _
  closeL (_ ∷ ls) (flᶜ c) b K = closeL ls c (subst (_≤ᴰ _) (+ᴰ-identityˡ _) b) K
  closeL {k = k} (_ ∷ ls) (delᶜ {d = d} c) b K =
    use-delay (≤ᴰ-trans (≤ᴰ-+ ∣ d ∣⁺ _) b)
              (closeL ls c (+-≤-∸ (≤ᴰ-trans (≤ᴰ-+ ∣ d ∣⁺ _) b) b) K)

  -- the chain grows by a letter

  grow : ∀ {s} ls x v → ChoiceL s (map stl ls ++ stl x ∷ v) → ChoiceL s (map stl (ls ∷ʳ x) ++ v)
  grow {s} ls x v c =
    subst (λ w → ChoiceL s w)
          (trans (sym (++-assoc (map stl ls) [ stl x ] v))
                 (cong (_++ v) (sym (map-++ stl ls [ x ])))) c

mutual

  runL⇒ : ∀ {ps v s t} → RunL ps v → PcsL t ps → ChoiceL s v → ∀ k → s ≼ᶜ[ k ] t
  runL⇒ done []ᵖ nilᶜ k = nil
  runL⇒ (match refl r) (opᵖ pc) (opᶜ c) k = keep (runL⇒ r pc c 0ᴰ)
  runL⇒ {s = s} (start {S = S} {c = c₀} h) pc c k =
    chL⇒ h pc ((S , c₀) ∷ []) refl c (0ᴰ-least k)

  chL⇒ : ∀ {S pre cs m ps v s t k} → ChL S pre cs m ps v → PcsL t ps
       → (ls : List (OpSet × Cut)) → cs ≡ map proj₂ ls → ChoiceL s (map stl ls ++ v)
       → Σˡ (wts pre) ≤ᴰ k → s ≼ᶜ[ k ] t
  chL⇒ {pre = pre} {k = k} (pour {p = p} a h) (opᵖ {o = o} pc) ls e c b =
    pay-op (chL⇒ h pc ls e c (subst (_≤ᴰ k +ᴰ costˡᵒ o)
                               (sym (trans (Σˡ-∷ʳ pre p) (cong (Σˡ (wts pre) +ᴰ_) (sym (costˡᵒ-dense dense o)))))
                               (+ᴰ-monoˡ-≤ (costˡᵒ o) b)))
  chL⇒ {pre = pre} {k = k} (pour {p = p} a h) (delᵖ {d = d} pc) ls e c b =
    del-delay (chL⇒ h pc ls e c (subst (_≤ᴰ k +ᴰ ∣ d ∣⁺) (sym (Σˡ-∷ʳ pre p)) (+ᴰ-monoˡ-≤ ∣ d ∣⁺ b)))
  chL⇒ {cs = cs} (over {S′ = S′} {c = c₀} {v = v} a ¬f g h) pc ls e c b =
    chL⇒ h pc (ls ∷ʳ (S′ , c₀))
         (trans (cong (_∷ʳ c₀) e) (sym (map-++ proj₂ ls [ (S′ , c₀) ])))
         (grow ls (S′ , c₀) v c) b
  chL⇒ {pre = pre} {cs = cs} (close f r) pc ls refl c b =
    closeL ls c (≤ᴰ-trans (fits-pt pre cs f) b) (λ c′ k′ → runL⇒ r pc c′ k′)

------------------------------------------------------------------------
-- Reflection

allChoicesᴸ : List Trace → List (Word′ lower)
allChoicesᴸ []       = []
allChoicesᴸ (s ∷ ss) = choicesᴸ s ++ allChoicesᴸ ss

private
  all⁻ : ∀ {P : Word′ lower → Set} ss → Any P (allChoicesᴸ ss) → Any (λ s → Any P (choicesᴸ s)) ss
  all⁻ (s ∷ ss) a with ++⁻ (choicesᴸ s) a
  ... | inj₁ a′ = here a′
  ... | inj₂ a′ = there (all⁻ ss a′)

  all⁺ : ∀ {P : Word′ lower → Set} ss → Any (λ s → Any P (choicesᴸ s)) ss → Any P (allChoicesᴸ ss)
  all⁺ (s ∷ ss) (here a)  = ++⁺ˡ a
  all⁺ (s ∷ ss) (there a) = ++⁺ʳ (choicesᴸ s) (all⁺ ss a)

  all-valid : ∀ ss → AllValidL (allChoicesᴸ ss)
  all-valid []       = tt
  all-valid (s ∷ ss) = go (choicesᴸ s) (choicesᴸ-choice s)
    where
      go : ∀ vs → (∀ {v} → v ∈ˡ vs → ChoiceL s v) → AllValidL (vs ++ allChoicesᴸ ss)
      go []       _ = all-valid ss
      go (v ∷ vs) h = choice-valid (h (here refl)) , go vs (λ m → h (there m))

-- below a union of guarantees, covering one of them

reflect : ∀ t ss → ⟦ lo t ⟧ ≾ᴸ (λ y → Any (λ s → ⟦ lo s ⟧ y) ss) → Any (λ s → s ≼ᶜ t) ss
reflect t ss f =
  Any.map read (all⁻ ss (completeᴸ (fullᴸ t) (validL-full t) (allChoicesᴸ ss) (all-valid ss) g))
  where
    g : ⟦ fullᴸ t ⟧ʷ ≾ᴸ UnionLᴸ (allChoicesᴸ ss)
    g x x∈ with f x (fullᴸ-⊆ t x∈)
    ... | y , y∈ , fit = y , all⁺ ss (Any.map (λ {s} y∈s → choicesᴸ-cover s y∈s) y∈) , fit
    read : ∀ {s} → Any (λ v → RunL (map symᴸ (fullᴸ t)) v) (choicesᴸ s) → s ≼ᶜ t
    read {s} a with find a
    ... | v , v∈ , r = runL⇒ r (pcs-full t) (choicesᴸ-choice s v∈) 0ᴰ

-- the coverage order is the converse of the order of the translations

≼ᶜ⇔ : ∀ s t → s ≼ᶜ t ⇔ ⟦ lo t ⟧ ≾ᴸ ⟦ lo s ⟧
≼ᶜ⇔ s t = mk⇔ sound from
  where
    from : ⟦ lo t ⟧ ≾ᴸ ⟦ lo s ⟧ → s ≼ᶜ t
    from f with reflect t (s ∷ []) (λ x x∈ → let (y , y∈ , fit) = f x x∈ in y , here y∈ , fit)
    ... | here d = d

------------------------------------------------------------------------
-- Products

private
  ≈-refl : ∀ {X : Lang} → X ≈ᴸ X
  ≈-refl = ≾ᴸ-refl , ≾ᴸ-refl

  ≈-sym : ∀ {X Y : Lang} → X ≈ᴸ Y → Y ≈ᴸ X
  ≈-sym (a , b) = b , a

  ≈-trans : ∀ {X Y Z : Lang} → X ≈ᴸ Y → Y ≈ᴸ Z → X ≈ᴸ Z
  ≈-trans (a , b) (c , d) = ≾ᴸ-trans a c , ≾ᴸ-trans d b

  ·-cong : ∀ {X X′ Y Y′ : Lang} → X ≈ᴸ X′ → Y ≈ᴸ Y′ → (X ·ᴸ Y) ≈ᴸ (X′ ·ᴸ Y′)
  ·-cong (a , b) (c , d) = ·-mono a c , ·-mono b d

  assoc : ∀ X Y Z → ((X ·ᴸ Y) ·ᴸ Z) ≈ᴸ (X ·ᴸ (Y ·ᴸ Z))
  assoc = ·-assoc

  -- stretches of at least `m` then `n` are one of at least `m + n`

  at-least-split : ∀ m n → ⟦ ≥ᶜ (m +ᴰ n) ⟧ ≈ᴸ (⟦ ≥ᶜ m ⟧ ·ᴸ ⟦ ≥ᶜ n ⟧)
  at-least-split m n = to , from
    where
      to : ⟦ ≥ᶜ (m +ᴰ n) ⟧ ≾ᴸ (⟦ ≥ᶜ m ⟧ ·ᴸ ⟦ ≥ᶜ n ⟧)
      to x (τ , r , refl) =
        stretch all m ++ stretch all (τ ∸ᴰ m) ,
        (stretch all m , stretch all (τ ∸ᴰ m) , refl , (m , ≤⇒⁻⊑⁻ ≤ᴰ-refl , refl) ,
         (τ ∸ᴰ m , ≤⇒⁻⊑⁻ (+-≤-∸ m≤τ (⊑⇒≤ r)) , refl)) ,
        subst (λ z → stretch all z ⊑ stretch all m ++ stretch all (τ ∸ᴰ m)) (+-∸ m≤τ)
              (split⊑ all m (τ ∸ᴰ m))
        where
          m≤τ : m ≤ᴰ τ
          m≤τ = ≤ᴰ-trans (≤ᴰ-+ m n) (⊑⇒≤ r)
      from : (⟦ ≥ᶜ m ⟧ ·ᴸ ⟦ ≥ᶜ n ⟧) ≾ᴸ ⟦ ≥ᶜ (m +ᴰ n) ⟧
      from x (_ , _ , refl , (a , ra , refl) , (b , rb , refl)) =
        stretch all (a +ᴰ b) , (a +ᴰ b , ≤⇒⁻⊑⁻ (+ᴰ-mono-≤ (⊑⇒≤ ra) (⊑⇒≤ rb)) , refl) , join⊑ all a b

  -- a flank in front of a stretch of at least `m` is absorbed

  absorb≥ : ∀ m → (⟦ ≥0 ⟧ ·ᴸ ⟦ ≥ᶜ m ⟧) ≈ᴸ ⟦ ≥ᶜ m ⟧
  absorb≥ m =
    ≈-trans (≈-sym (at-least-split 0ᴰ m)) (subst (λ z → ⟦ ≥ᶜ z ⟧ ≈ᴸ ⟦ ≥ᶜ m ⟧) (sym (+ᴰ-identityˡ m)) ≈-refl)

  -- and in front of any translation

  absorb : ∀ t → (⟦ ≥0 ⟧ ·ᴸ ⟦ lo t ⟧) ≈ᴸ ⟦ lo t ⟧
  absorb εᵗ = absorb≥ 0ᴰ
  absorb (operation o t) =
    ≈-trans (≈-sym (assoc ⟦ ≥0 ⟧ ⟦ ≥0 ⟧ _)) (·-cong (absorb≥ 0ᴰ) ≈-refl)
  absorb (delay d t⁻) =
    ≈-trans (≈-sym (assoc ⟦ ≥0 ⟧ ⟦ ≥ᶜ ∣ d ∣⁺ ⟧ _)) (·-cong (absorb≥ ∣ d ∣⁺) ≈-refl)

  absorb⁻ : ∀ t⁻ → (⟦ ≥0 ⟧ ·ᴸ ⟦ lo⁻ t⁻ ⟧) ≈ᴸ ⟦ lo⁻ t⁻ ⟧
  absorb⁻ t⁻ = subst (λ e → (⟦ ≥0 ⟧ ·ᴸ ⟦ e ⟧) ≈ᴸ ⟦ e ⟧) (lo-inj⁻ t⁻) (absorb (inj⁻ t⁻))

lo-prepend : ∀ d t → ⟦ lo (prepend d t) ⟧ ≈ᴸ ((⟦ ≥ᶜ ∣ d ∣⁺ ⟧ ·ᴸ ⟦ ≥0 ⟧) ·ᴸ ⟦ lo t ⟧)
lo-prepend d t = ≈-trans (go t) (≈-sym (assoc ⟦ ≥ᶜ ∣ d ∣⁺ ⟧ ⟦ ≥0 ⟧ ⟦ lo t ⟧))
  where
    go : ∀ t → ⟦ lo (prepend d t) ⟧ ≈ᴸ (⟦ ≥ᶜ ∣ d ∣⁺ ⟧ ·ᴸ (⟦ ≥0 ⟧ ·ᴸ ⟦ lo t ⟧))
    go εᵗ              = ·-cong ≈-refl (≈-sym (absorb εᵗ))
    go (operation o t) = ·-cong ≈-refl (≈-sym (absorb (operation o t)))
    go (delay e t⁻)    =
      ≈-trans (·-cong (at-least-split ∣ d ∣⁺ ∣ e ∣⁺) ≈-refl)
        (≈-trans (assoc ⟦ ≥ᶜ ∣ d ∣⁺ ⟧ ⟦ ≥ᶜ ∣ e ∣⁺ ⟧ ⟦ lo⁻ t⁻ ⟧)
                 (·-cong ≈-refl (≈-sym (absorb (delay e t⁻)))))

lo-∙ : ∀ s t → ⟦ lo (s ∙ᵗ t) ⟧ ≈ᴸ (⟦ lo s ⟧ ·ᴸ ⟦ lo t ⟧)
lo-∙ εᵗ t = ≈-sym (absorb t)
lo-∙ (operation o s) t =
  ≈-trans (·-cong ≈-refl (≈-trans (·-cong ≈-refl (lo-∙ s t))
                                   (≈-sym (assoc ⟦ ‵_ {lower} o ⟧ ⟦ lo s ⟧ ⟦ lo t ⟧))))
          (≈-sym (assoc ⟦ ≥0 ⟧ (⟦ ‵_ {lower} o ⟧ ·ᴸ ⟦ lo s ⟧) ⟦ lo t ⟧))
lo-∙ (delay d ε⁻ᵗ) t = lo-prepend d t
lo-∙ (delay d (operation⁻ o s)) t =
  ≈-trans (·-cong ≈-refl (lo-∙ (operation o s) t))
          (≈-sym (assoc ⟦ ≥ᶜ ∣ d ∣⁺ ⟧ ⟦ lo (operation o s) ⟧ ⟦ lo t ⟧))
