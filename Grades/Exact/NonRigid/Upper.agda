------------------------------------------------------------------------
-- Allowances as upper interval-letter expressions.                   --
--                                                                    --
-- A timed trace read as a bound translates letter by letter:         --
--                                                                    --
--   up (o ; t)  =  o? · up t       an operation the bound permits    --
--   up (d ; t)  =  ≤d · up t       a budget of at most the delay     --
--                                                                    --
-- where `≤d` is a stretch admitting every operation. Then            --
--                                                                    --
--   s ≼ᵃ t   iff   ⟦ up s ⟧ ≾ ⟦ up t ⟧                               --
--                                                                    --
-- at the costs `costʰⁱ` of the running times, and a trace is below   --
-- one of several bounds when its translation is below their union.   --
-- Soundness is by induction on the allowance, a fit placing what the --
-- banked budget pays for in a stretch in front. Reflection reads the --
-- word of the trace with all its operations at the upper reader:     --
-- completeness of the reader gives a run against a word of a bound,  --
-- and the run is an allowance. The translation sends the product of  --
-- traces to the product of expressions.                              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus

module Grades.Exact.NonRigid.Upper
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Fin.Subset using (⁅_⁆) renaming (⊤ to all)
open import Data.Fin.Subset.Properties using (x∈⁅y⁆⇒x≡y; x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; [_])
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (find) renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻; map⁺)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; Hi; fin; ∞; ⁺; ⁻; 0⁺; pt; sup-dense; _⊑ʰ_; _+ʰ_; _∧ˢ_; ⊑⇒≤; ≤⇒⁺⊑⁺; ⊏-by-pt; hi; lo)
  renaming (_∣_ to _∣ᶜ_)
open import Grades.Durations.Intervals.Dense T using (_∈ⁱ_)

open RunningTimes.RunningTimes running using (rt; rt-bounded; costʰⁱ; ≤-costʰⁱ)

open import Grades.Traces.Base T Op as Tr
  using (Trace; Trace⁻; operation; delay; operation⁻; inj⁻; prepend)
  renaming (ε to εᵗ; ε⁻ to ε⁻ᵗ; _∙_ to _∙ᵗ_)
open import Grades.Traces.Allowance.Core T Op costʰⁱ
  using (_≼ᵃ[_]_; _≼ᵃ_; nil; keep; skip-op; bank-delay; use-delay; use-op)

open import Grades.Exact.Base T Op n code code-injective
  using (Word; op; st; stretch; dur; dur-++; dur-stretch; D⁺; ∣_∣⁺; ∣∣⁺-pos; _+⁺_)
open import Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-refl)
open import Grades.Exact.Lift T Op n code code-injective
  using (Lang; uᴸ; _·ᴸ_; ⊑-++; ·-mono; ·-assoc; ·-identityˡ; ·-identityʳ)
  renaming (_≈_ to _≈ᴸ_; _≾_ to _≾ᴸ_; ≾-refl to ≾ᴸ-refl; ≾-trans to ≾ᴸ-trans)
open import Grades.Exact.Expression T Op n code code-injective running
  using (Instance; upper; Expr; ε; ops; str; _∣_; _·_; ‵_; _？; ⟦_⟧; strᴸ)
open import Grades.Exact.Letters T Op n code code-injective running
  using (Letter; op; st; Word′; ⟦_⟧ʷ; Kind; opk; stk)
open import Grades.Exact.Reader.Upper T Op n code code-injective running
  using (Ph; sumʰ; Fitsᵁ; RunU; ChU; OverU; done; match; start; pour; over; close; enter; pass)
open import Grades.Exact.Reader.Upper.Correct T Op n code code-injective running dense κ κ-pos
  using (symᵁ; ValidW; UnionL; completeᵁ)
open import Grades.Exact.NonRigid.Base T Op n code code-injective running

------------------------------------------------------------------------
-- The translation

-- a budget of at most a delay

≤ᵇ : D⁺ → Expr upper
≤ᵇ d = str all (fin (∣ d ∣⁺ ∣ᶜ ⁺))

mutual

  up : Trace → Expr upper
  up εᵗ              = ε
  up (operation o t) = o ？ · up t
  up (delay d t⁻)    = ≤ᵇ d · up⁻ t⁻

  up⁻ : Trace⁻ → Expr upper
  up⁻ ε⁻ᵗ              = ε
  up⁻ (operation⁻ o t) = o ？ · up t

up-inj⁻ : ∀ t⁻ → up (inj⁻ t⁻) ≡ up⁻ t⁻
up-inj⁻ ε⁻ᵗ              = refl
up-inj⁻ (operation⁻ o t) = refl

private
  to⁻ : ∀ t⁻ {y} → ⟦ up (inj⁻ t⁻) ⟧ y → ⟦ up⁻ t⁻ ⟧ y
  to⁻ t⁻ {y} = subst (λ e → ⟦ e ⟧ y) (up-inj⁻ t⁻)

  from⁻ : ∀ t⁻ {y} → ⟦ up⁻ t⁻ ⟧ y → ⟦ up (inj⁻ t⁻) ⟧ y
  from⁻ t⁻ {y} = subst (λ e → ⟦ e ⟧ y) (sym (up-inj⁻ t⁻))

  -- an operation kept, or left out

  kept : ∀ {o d y} {e : Expr upper} → ∣ d ∣⁺ ∈ⁱ rt o → ⟦ e ⟧ y → ⟦ o ？ · e ⟧ (op o d ∷ [] ++ y)
  kept {o} {d} {y} r y∈ = op o d ∷ [] , y , refl , inj₁ (o , d , x∈⁅x⁆ (code o) , r , refl) , y∈

  skipped : ∀ {o y} {e : Expr upper} → ⟦ e ⟧ y → ⟦ o ？ · e ⟧ y
  skipped {y = y} y∈ = [] , y , refl , inj₂ refl , y∈

  -- a running time is at most the cost

  rt-≤ : ∀ o {τ} → τ ∈ⁱ rt o → τ ≤ᴰ costʰⁱ o
  rt-≤ = ≤-costʰⁱ

------------------------------------------------------------------------
-- Every translation has the empty run

mutual

  ε∈ : ∀ t → ⟦ up t ⟧ []
  ε∈ εᵗ              = refl
  ε∈ (operation o t) = skipped {o} {e = up t} (ε∈ t)
  ε∈ (delay d t⁻)    =
    [] , [] , refl , (0ᴰ , ≤⇒⁺⊑⁺ (0ᴰ-least _) , sym (stretch-0 all)) , ε∈⁻ t⁻

  ε∈⁻ : ∀ t⁻ → ⟦ up⁻ t⁻ ⟧ []
  ε∈⁻ ε⁻ᵗ              = refl
  ε∈⁻ (operation⁻ o t) = skipped {o} {e = up t} (ε∈ t)

------------------------------------------------------------------------
-- Soundness

private
  split-budget : ∀ k e a → a ≤ᴰ k +ᴰ e
               → Σ[ b ∈ Carrier ] Σ[ τ ∈ Carrier ] b ≤ᴰ k × τ ≤ᴰ e × b +ᴰ τ ≡ a
  split-budget k e a r with a ≤ᴰ? k
  ... | yes ak = a , 0ᴰ , ak , 0ᴰ-least e , +ᴰ-identityʳ a
  ... | no ¬ak = k , a ∸ᴰ k , ≤ᴰ-refl , ∸-≤-+ r , +-∸ (<⇒≤ ¬ak)

-- a run of `up s` fits a stretch of at most the banked budget followed
-- by a run of `up t`

sound↑ : ∀ {k s t} → s ≼ᵃ[ k ] t → ∀ x → ⟦ up s ⟧ x
       → Σ[ a ∈ Carrier ] a ≤ᴰ k × Σ[ y ∈ Word ] ⟦ up t ⟧ y × x ⊑ stretch all a ++ y
sound↑ {t = t} nil x refl = 0ᴰ , 0ᴰ-least _ , [] , ε∈ t , pad0 all ⊑-refl
sound↑ (keep {o = o} {t = t} d) _ (_ , x₂ , refl , inj₁ (o′ , dd , c , r , refl) , x₂∈)
  with code-injective (x∈⁅y⁆⇒x≡y (code o) c)
... | refl with sound↑ d x₂ x₂∈
...   | a , a≤0 , y , y∈ , fit =
  0ᴰ , 0ᴰ-least _ , op o dd ∷ [] ++ y , kept {o} {e = up t} r y∈ ,
  pad0 all (⊑-++ (⊑-refl {op o dd ∷ []}) (unpad all (≤0⇒≡0 a≤0) fit))
sound↑ (keep {o = o} {t = t} d) _ (_ , x₂ , refl , inj₂ refl , x₂∈) with sound↑ d x₂ x₂∈
... | a , a≤0 , y , y∈ , fit = a , ≤ᴰ-trans a≤0 (0ᴰ-least _) , y , skipped {o} {e = up t} y∈ , fit
sound↑ (skip-op {o = o} {t = t} d) x x∈ with sound↑ d x x∈
... | a , a≤ , y , y∈ , fit = a , a≤ , y , skipped {o} {e = up t} y∈ , fit
sound↑ (bank-delay {k = k} {e = e} {t⁻ = t⁻} d) x x∈ with sound↑ d x x∈
... | a , a≤ , y , y∈ , fit with split-budget k ∣ e ∣⁺ a a≤
...   | b , τ , b≤ , τ≤ , refl =
  b , b≤ , stretch all τ ++ y ,
  (stretch all τ , y , refl , (τ , ≤⇒⁺⊑⁺ τ≤ , refl) , to⁻ t⁻ y∈) ,
  split-front all b τ fit
sound↑ (use-delay {k = k} {d = d} {s⁻ = s⁻} p d′) _ (_ , x₂ , refl , (τ , r , refl) , x₂∈)
  with sound↑ d′ x₂ (from⁻ s⁻ x₂∈)
... | a , a≤ , y , y∈ , fit =
  τ +ᴰ a ,
  ≤ᴰ-trans (+ᴰ-mono-≤ (⊑⇒≤ r) a≤) (≤ᴰ-reflexive (+-∸ p)) ,
  y , y∈ , join-front all τ a (⊑-++ (⊑-refl {stretch all τ}) fit)
sound↑ (use-op {k = k} {o = o} p d′) _ (_ , x₂ , refl , inj₁ (o′ , dd , c , r , refl) , x₂∈)
  with code-injective (x∈⁅y⁆⇒x≡y (code o) c)
... | refl with sound↑ d′ x₂ x₂∈
...   | a , a≤ , y , y∈ , fit =
  ∣ dd ∣⁺ +ᴰ a ,
  ≤ᴰ-trans (+ᴰ-mono-≤ (rt-≤ o r) a≤) (≤ᴰ-reflexive (+-∸ p)) ,
  y , y∈ ,
  join-front all ∣ dd ∣⁺ a (⊑-++ (⊑-all′ (op o dd ∷ []) (+ᴰ-identityʳ _)) fit)
sound↑ (use-op {k = k} {o = o} p d′) _ (_ , x₂ , refl , inj₂ refl , x₂∈) with sound↑ d′ x₂ x₂∈
... | a , a≤ , y , y∈ , fit = a , ≤ᴰ-trans a≤ (∸-≤-self k (costʰⁱ o)) , y , y∈ , fit

sound : ∀ {s t} → s ≼ᵃ t → ⟦ up s ⟧ ≾ᴸ ⟦ up t ⟧
sound d x x∈ with sound↑ d x x∈
... | a , a≤0 , y , y∈ , fit = y , y∈ , unpad all (≤0⇒≡0 a≤0) fit

------------------------------------------------------------------------
-- The word of a trace with every operation kept

mutual

  full : Trace → Word′ upper
  full εᵗ              = []
  full (operation o t) = op o ∷ full t
  full (delay d t⁻)    = st all (fin (∣ d ∣⁺ ∣ᶜ ⁺)) ∷ full⁻ t⁻

  full⁻ : Trace⁻ → Word′ upper
  full⁻ ε⁻ᵗ              = []
  full⁻ (operation⁻ o t) = op o ∷ full t

mutual

  full-⊆ : ∀ t {x} → ⟦ full t ⟧ʷ x → ⟦ up t ⟧ x
  full-⊆ εᵗ              x∈ = x∈
  full-⊆ (operation o t) (x₁ , x₂ , e , x₁∈ , x₂∈) = x₁ , x₂ , e , inj₁ x₁∈ , full-⊆ t x₂∈
  full-⊆ (delay d t⁻)    (x₁ , x₂ , e , x₁∈ , x₂∈) = x₁ , x₂ , e , x₁∈ , full-⊆⁻ t⁻ x₂∈

  full-⊆⁻ : ∀ t⁻ {x} → ⟦ full⁻ t⁻ ⟧ʷ x → ⟦ up⁻ t⁻ ⟧ x
  full-⊆⁻ ε⁻ᵗ              x∈ = x∈
  full-⊆⁻ (operation⁻ o t) (x₁ , x₂ , e , x₁∈ , x₂∈) = x₁ , x₂ , e , inj₁ x₁∈ , full-⊆ t x₂∈

mutual

  validW-full : ∀ t → ValidW (full t)
  validW-full εᵗ              = tt
  validW-full (operation o t) = validW-full t
  validW-full (delay d t⁻)    = ⊏-by-pt (∣∣⁺-pos d) , validW-full⁻ t⁻

  validW-full⁻ : ∀ t⁻ → ValidW (full⁻ t⁻)
  validW-full⁻ ε⁻ᵗ              = tt
  validW-full⁻ (operation⁻ o t) = validW-full t

------------------------------------------------------------------------
-- The words of a translation

mutual

  choices : Trace → List (Word′ upper)
  choices εᵗ              = [] ∷ []
  choices (operation o t) = map (op o ∷_) (choices t) ++ choices t
  choices (delay d t⁻)    = map (st all (fin (∣ d ∣⁺ ∣ᶜ ⁺)) ∷_) (choices⁻ t⁻)

  choices⁻ : Trace⁻ → List (Word′ upper)
  choices⁻ ε⁻ᵗ              = [] ∷ []
  choices⁻ (operation⁻ o t) = map (op o ∷_) (choices t) ++ choices t

-- a word of the bound: some operations kept, every delay a budget

data Choice : Trace → Word′ upper → Set where
  nilᶜ  : Choice εᵗ []
  keepᶜ : ∀ {o t v} → Choice t v → Choice (operation o t) (op o ∷ v)
  dropᶜ : ∀ {o t v} → Choice t v → Choice (operation o t) v
  delᶜ  : ∀ {d t⁻ v} → Choice (inj⁻ t⁻) v → Choice (delay d t⁻) (st all (fin (∣ d ∣⁺ ∣ᶜ ⁺)) ∷ v)

mutual

  choices-cover : ∀ t {y} → ⟦ up t ⟧ y → Any (λ v → ⟦ v ⟧ʷ y) (choices t)
  choices-cover εᵗ refl = here refl
  choices-cover (operation o t) (y₁ , y₂ , refl , inj₁ y₁∈ , y₂∈) =
    ++⁺ˡ (map⁺ (Any.map (λ v∈ → y₁ , y₂ , refl , y₁∈ , v∈) (choices-cover t y₂∈)))
  choices-cover (operation o t) (_ , y₂ , refl , inj₂ refl , y₂∈) =
    ++⁺ʳ (map (op o ∷_) (choices t)) (choices-cover t y₂∈)
  choices-cover (delay d t⁻) (y₁ , y₂ , refl , y₁∈ , y₂∈) =
    map⁺ (Any.map (λ v∈ → y₁ , y₂ , refl , y₁∈ , v∈) (choices-cover⁻ t⁻ y₂∈))

  choices-cover⁻ : ∀ t⁻ {y} → ⟦ up⁻ t⁻ ⟧ y → Any (λ v → ⟦ v ⟧ʷ y) (choices⁻ t⁻)
  choices-cover⁻ ε⁻ᵗ refl = here refl
  choices-cover⁻ (operation⁻ o t) (y₁ , y₂ , refl , inj₁ y₁∈ , y₂∈) =
    ++⁺ˡ (map⁺ (Any.map (λ v∈ → y₁ , y₂ , refl , y₁∈ , v∈) (choices-cover t y₂∈)))
  choices-cover⁻ (operation⁻ o t) (_ , y₂ , refl , inj₂ refl , y₂∈) =
    ++⁺ʳ (map (op o ∷_) (choices t)) (choices-cover t y₂∈)

mutual

  choices-choice : ∀ t {v} → v ∈ˡ choices t → Choice t v
  choices-choice εᵗ (here refl) = nilᶜ
  choices-choice (operation o t) m = choice-op o t m
  choices-choice (delay d t⁻) m with ∈-map⁻ (st all (fin (∣ d ∣⁺ ∣ᶜ ⁺)) ∷_) m
  ... | v′ , m′ , refl = delᶜ (choices-choice⁻ t⁻ m′)

  choices-choice⁻ : ∀ t⁻ {v} → v ∈ˡ choices⁻ t⁻ → Choice (inj⁻ t⁻) v
  choices-choice⁻ ε⁻ᵗ (here refl) = nilᶜ
  choices-choice⁻ (operation⁻ o t) m = choice-op o t m

  choice-op : ∀ o t {v} → v ∈ˡ map (op o ∷_) (choices t) ++ choices t → Choice (operation o t) v
  choice-op o t m with ∈-++⁻ (map (op o ∷_) (choices t)) m
  ... | inj₂ m′ = dropᶜ (choices-choice t m′)
  ... | inj₁ m′ with ∈-map⁻ (op o ∷_) m′
  ...   | v′ , m″ , refl = keepᶜ (choices-choice t m″)

------------------------------------------------------------------------
-- Reading a run of the reader as an allowance

-- the pieces of the word of a trace

data Pcs : Trace → List Ph → Set where
  []ᵖ  : Pcs εᵗ []
  opᵖ  : ∀ {o s ps} → Pcs s ps → Pcs (operation o s) ((opk o , hi (rt o)) ∷ ps)
  delᵖ : ∀ {d s⁻ ps} → Pcs (inj⁻ s⁻) ps
       → Pcs (delay d s⁻) ((stk all , fin (∣ d ∣⁺ ∣ᶜ ⁺)) ∷ ps)

mutual

  pcs-full : ∀ s → Pcs s (map symᵁ (full s))
  pcs-full εᵗ              = []ᵖ
  pcs-full (operation o s) = opᵖ (pcs-full s)
  pcs-full (delay d s⁻)    = delᵖ (pcs-full⁻ s⁻)

  pcs-full⁻ : ∀ s⁻ → Pcs (inj⁻ s⁻) (map symᵁ (full⁻ s⁻))
  pcs-full⁻ ε⁻ᵗ              = []ᵖ
  pcs-full⁻ (operation⁻ o s) = opᵖ (pcs-full s)

-- finite upper ends and their points

private
  IsFin : Hi → Set
  IsFin (fin _) = ⊤
  IsFin ∞       = ⊥

  AllFin : List Hi → Set
  AllFin []       = ⊤
  AllFin (h ∷ hs) = IsFin h × AllFin hs

  ptʰ : Hi → Carrier
  ptʰ (fin c) = pt c
  ptʰ ∞       = 0ᴰ

  Σʰ : List Hi → Carrier
  Σʰ []       = 0ᴰ
  Σʰ (h ∷ hs) = ptʰ h +ᴰ Σʰ hs

  wts : List Ph → List Hi
  wts = map proj₂

  sum-fin : ∀ hs → AllFin hs → Σ[ c ∈ Cut ] sumʰ hs ≡ fin c × pt c ≡ Σʰ hs
  sum-fin []                  _       = 0⁺ , refl , refl
  sum-fin (fin (p ∣ᶜ s) ∷ hs) (_ , a) with sum-fin hs a
  ... | (q ∣ᶜ t) , e , e′ =
    (p +ᴰ q) ∣ᶜ (s ∧ˢ t) , cong (fin (p ∣ᶜ s) +ʰ_) e , cong (p +ᴰ_) e′

  fits-pt : ∀ xs ys → AllFin xs → AllFin ys → sumʰ xs ⊑ʰ sumʰ ys → Σʰ xs ≤ᴰ Σʰ ys
  fits-pt xs ys ax ay f with sum-fin xs ax | sum-fin ys ay
  ... | c , e , e′ | c′ , d , d′ = subst₂ _≤ᴰ_ e′ d′ (⊑⇒≤ (subst₂ _⊑ʰ_ e d f))

  Σʰ-∷ʳ : ∀ hs h → Σʰ (hs ∷ʳ h) ≡ Σʰ hs +ᴰ ptʰ h
  Σʰ-∷ʳ []       h = trans (+ᴰ-identityʳ _) (sym (+ᴰ-identityˡ _))
  Σʰ-∷ʳ (x ∷ hs) h = trans (cong (ptʰ x +ᴰ_) (Σʰ-∷ʳ hs h)) (sym (+ᴰ-assoc (ptʰ x) (Σʰ hs) (ptʰ h)))

  allFin-∷ʳ : ∀ hs {h} → AllFin hs → IsFin h → AllFin (hs ∷ʳ h)
  allFin-∷ʳ []       _        f = f , tt
  allFin-∷ʳ (x ∷ hs) (fx , a) f = fx , allFin-∷ʳ hs a f

  wts-∷ʳ : ∀ (pre : List Ph) p → wts (pre ∷ʳ p) ≡ wts pre ∷ʳ proj₂ p
  wts-∷ʳ pre p = map-++ proj₂ pre [ p ]

  op-fin : ∀ o → IsFin (hi (rt o)) × ptʰ (hi (rt o)) ≡ costʰⁱ o
  op-fin o with hi (rt o) | rt-bounded o
  ... | fin c | RunningTimes.fin .c = tt , sym (sup-dense dense c)

  -- the budget arithmetic of a chain

  pay : ∀ {W C k c} → W +ᴰ c ≤ᴰ C → C ∸ᴰ W ≤ᴰ k → c ≤ᴰ k × C ∸ᴰ (W +ᴰ c) ≤ᴰ k ∸ᴰ c
  pay {W} {C} {k} {c} h b =
    ≤ᴰ-trans (+-≤-∸ (≤ᴰ-trans (≤ᴰ-+ W c) h) h) b ,
    subst (_≤ᴰ k ∸ᴰ c) (∸-+-assoc C W c) (∸-monoˡ-≤ c b)

  bank : ∀ {W C k d} → C ∸ᴰ W ≤ᴰ k → (C +ᴰ d) ∸ᴰ W ≤ᴰ k +ᴰ d
  bank {W} {C} {k} {d} b =
    ≤ᴰ-trans (∸-≤-+ (≤ᴰ-trans (+ᴰ-monoˡ-≤ d (≤-+-∸ C W))
                               (≤ᴰ-reflexive (+ᴰ-assoc W (C ∸ᴰ W) d))))
             (+ᴰ-monoˡ-≤ d b)

  loosen : ∀ {W C k d} → C ∸ᴰ W ≤ᴰ k → C ∸ᴰ W ≤ᴰ k +ᴰ d
  loosen {k = k} {d} b = ≤ᴰ-trans b (≤ᴰ-+ k d)

  -- a piece poured into a chain is paid out of its budget

  pour-step : ∀ pre cs p {k} → AllFin (wts pre) → AllFin cs → IsFin (proj₂ p)
            → Fitsᵁ (pre ∷ʳ p) cs → Σʰ cs ∸ᴰ Σʰ (wts pre) ≤ᴰ k
            → AllFin (wts (pre ∷ʳ p)) × ptʰ (proj₂ p) ≤ᴰ k
              × Σʰ cs ∸ᴰ Σʰ (wts (pre ∷ʳ p)) ≤ᴰ k ∸ᴰ ptʰ (proj₂ p)
  pour-step pre cs p fw fc fp f b = fw′ , proj₁ res , subst (λ z → Σʰ cs ∸ᴰ z ≤ᴰ _) (sym eq) (proj₂ res)
    where
      fw′ : AllFin (wts (pre ∷ʳ p))
      fw′ = subst AllFin (sym (wts-∷ʳ pre p)) (allFin-∷ʳ (wts pre) fw fp)
      eq : Σʰ (wts (pre ∷ʳ p)) ≡ Σʰ (wts pre) +ᴰ ptʰ (proj₂ p)
      eq = trans (cong Σʰ (wts-∷ʳ pre p)) (Σʰ-∷ʳ (wts pre) (proj₂ p))
      res = pay (subst (_≤ᴰ Σʰ cs) eq (fits-pt (wts (pre ∷ʳ p)) cs fw′ fc f)) b

mutual

  runU⇒ : ∀ {ps v s t} → RunU ps v → Pcs s ps → Choice t v → ∀ k → s ≼ᵃ[ k ] t
  runU⇒ _ []ᵖ _ k = nil
  runU⇒ r pc (dropᶜ c) k = skip-op (runU⇒ r pc c k)
  runU⇒ (match refl r) (opᵖ pc) (keepᶜ c) k = keep (runU⇒ r pc c 0ᴰ)
  runU⇒ (match () r) (delᵖ pc) (keepᶜ c) k
  runU⇒ (start h) pc (delᶜ {d = d} c) k =
    bank-delay (chU⇒ h pc c tt (tt , tt)
      (subst (_≤ᴰ k +ᴰ ∣ d ∣⁺) (sym (trans (∸-0 _) (+ᴰ-identityʳ _))) (≤ᴰ-+ˡ ∣ d ∣⁺ k)))
  runU⇒ () (opᵖ _) nilᶜ _
  runU⇒ () (delᵖ _) nilᶜ _

  chU⇒ : ∀ {S pre cs m ps v s t k} → ChU S pre cs m ps v → Pcs s ps → Choice t v
       → AllFin (wts pre) → AllFin cs → Σʰ cs ∸ᴰ Σʰ (wts pre) ≤ᴰ k → s ≼ᵃ[ k ] t
  chU⇒ h pc (dropᶜ c) fw fc b = skip-op (chU⇒ h pc c fw fc b)
  chU⇒ (close r) pc c fw fc b = runU⇒ r pc c _
  chU⇒ {pre = pre} {cs} {k = k} (pour {p = p} a f h) (opᵖ {o = o} pc) c fw fc b
    with pour-step pre cs p fw fc (proj₁ (op-fin o)) f b
  ... | fw′ , c≤ , b′ =
    use-op (subst (_≤ᴰ _) (proj₂ (op-fin o)) c≤)
           (chU⇒ h pc c fw′ fc (subst (λ z → Σʰ cs ∸ᴰ Σʰ (wts (pre ∷ʳ p)) ≤ᴰ k ∸ᴰ z) (proj₂ (op-fin o)) b′))
  chU⇒ {pre = pre} {cs} (pour {p = p} a f h) (delᵖ pc) c fw fc b
    with pour-step pre cs p fw fc tt f b
  ... | fw′ , d≤ , b′ = use-delay d≤ (chU⇒ h pc c fw′ fc b′)
  chU⇒ (over a ¬f o) pc c fw fc b = overU⇒ o pc c fw fc b

  overU⇒ : ∀ {pre cs p ps v s t k} → OverU pre cs p ps v → Pcs s (p ∷ ps) → Choice t v
         → AllFin (wts pre) → AllFin cs → Σʰ cs ∸ᴰ Σʰ (wts pre) ≤ᴰ k → s ≼ᵃ[ k ] t
  overU⇒ o pc (dropᶜ c) fw fc b = skip-op (overU⇒ o pc c fw fc b)
  overU⇒ {pre = pre} {cs} (enter h) pc (delᶜ {d = d} c) fw fc b =
    bank-delay (chU⇒ h pc c fw (allFin-∷ʳ cs fc tt)
      (subst (λ z → z ∸ᴰ Σʰ (wts pre) ≤ᴰ _) (sym (Σʰ-∷ʳ cs _)) (bank b)))
  overU⇒ (pass o) pc (delᶜ c) fw fc b = bank-delay (overU⇒ o pc c fw fc (loosen b))
  overU⇒ () pc nilᶜ fw fc b
  overU⇒ () pc (keepᶜ c) fw fc b

------------------------------------------------------------------------
-- Reflection

-- the words of several translations

allChoices : List Trace → List (Word′ upper)
allChoices []       = []
allChoices (t ∷ ts) = choices t ++ allChoices ts

private
  all⁻ : ∀ {P : Word′ upper → Set} ts → Any P (allChoices ts) → Any (λ t → Any P (choices t)) ts
  all⁻ (t ∷ ts) a with ++⁻ (choices t) a
  ... | inj₁ a′ = here a′
  ... | inj₂ a′ = there (all⁻ ts a′)

  all⁺ : ∀ {P : Word′ upper → Set} ts → Any (λ t → Any P (choices t)) ts → Any P (allChoices ts)
  all⁺ (t ∷ ts) (here a)  = ++⁺ˡ a
  all⁺ (t ∷ ts) (there a) = ++⁺ʳ (choices t) (all⁺ ts a)

-- below a union of translations, below one of them

reflect : ∀ s ts → ⟦ up s ⟧ ≾ᴸ (λ y → Any (λ t → ⟦ up t ⟧ y) ts) → Any (λ t → s ≼ᵃ t) ts
reflect s ts f =
  Any.map read (all⁻ ts (completeᵁ (full s) (validW-full s) (allChoices ts) g))
  where
    g : ⟦ full s ⟧ʷ ≾ᴸ UnionL (allChoices ts)
    g x x∈ with f x (full-⊆ s x∈)
    ... | y , y∈ , fit = y , all⁺ ts (Any.map (λ {t} y∈t → choices-cover t y∈t) y∈) , fit
    read : ∀ {t} → Any (λ v → RunU (map symᵁ (full s)) v) (choices t) → s ≼ᵃ t
    read {t} a with find a
    ... | v , v∈ , r = runU⇒ r (pcs-full s) (choices-choice t v∈) 0ᴰ

-- the allowance order is the order of the translations

≼ᵃ⇔ : ∀ s t → s ≼ᵃ t ⇔ ⟦ up s ⟧ ≾ᴸ ⟦ up t ⟧
≼ᵃ⇔ s t = mk⇔ sound from
  where
    from : ⟦ up s ⟧ ≾ᴸ ⟦ up t ⟧ → s ≼ᵃ t
    from f with reflect s (t ∷ []) (λ x x∈ → let (y , y∈ , fit) = f x x∈ in y , here y∈ , fit)
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

up-prepend : ∀ d t → ⟦ up (prepend d t) ⟧ ≈ᴸ (⟦ ≤ᵇ d ⟧ ·ᴸ ⟦ up t ⟧)
up-prepend d εᵗ              = ≈-refl
up-prepend d (operation o t) = ≈-refl
up-prepend d (delay e t⁻)    =
  ≈-trans (·-cong (budget-split all ∣ d ∣⁺ ∣ e ∣⁺) ≈-refl)
          (·-assoc ⟦ ≤ᵇ d ⟧ ⟦ ≤ᵇ e ⟧ ⟦ up⁻ t⁻ ⟧)

up-∙ : ∀ s t → ⟦ up (s ∙ᵗ t) ⟧ ≈ᴸ (⟦ up s ⟧ ·ᴸ ⟦ up t ⟧)
up-∙ εᵗ t = ≈-sym (·-identityˡ ⟦ up t ⟧)
up-∙ (operation o s) t =
  ≈-trans (·-cong ≈-refl (up-∙ s t)) (≈-sym (·-assoc ⟦ _？ {upper} o ⟧ ⟦ up s ⟧ ⟦ up t ⟧))
up-∙ (delay d ε⁻ᵗ) t =
  ≈-trans (up-prepend d t)
          (·-cong (≈-sym (·-identityʳ ⟦ ≤ᵇ d ⟧)) ≈-refl)
up-∙ (delay d (operation⁻ o s)) t =
  ≈-trans (·-cong ≈-refl (≈-trans (·-cong ≈-refl (up-∙ s t))
                                   (≈-sym (·-assoc ⟦ _？ {upper} o ⟧ ⟦ up s ⟧ ⟦ up t ⟧))))
          (≈-sym (·-assoc ⟦ ≤ᵇ d ⟧ (⟦ _？ {upper} o ⟧ ·ᴸ ⟦ up s ⟧) ⟦ up t ⟧))

------------------------------------------------------------------------
-- A run of a translation lasts at most the bound's span, operations
-- counted at their costs

mutual

  span : Trace → Carrier
  span εᵗ              = 0ᴰ
  span (operation o t) = costʰⁱ o +ᴰ span t
  span (delay d t⁻)    = ∣ d ∣⁺ +ᴰ span⁻ t⁻

  span⁻ : Trace⁻ → Carrier
  span⁻ ε⁻ᵗ              = 0ᴰ
  span⁻ (operation⁻ o t) = costʰⁱ o +ᴰ span t

mutual

  up-dur : ∀ t {x} → ⟦ up t ⟧ x → dur x ≤ᴰ span t
  up-dur εᵗ refl = ≤ᴰ-refl
  up-dur (operation o t) x∈ = op-dur o t x∈
  up-dur (delay d t⁻) (_ , x₂ , refl , (τ , r , refl) , x₂∈) =
    subst (_≤ᴰ _) (sym (trans (dur-++ (stretch all τ) x₂) (cong (_+ᴰ dur x₂) (dur-stretch all τ))))
          (+ᴰ-mono-≤ (⊑⇒≤ r) (up-dur⁻ t⁻ x₂∈))

  up-dur⁻ : ∀ t⁻ {x} → ⟦ up⁻ t⁻ ⟧ x → dur x ≤ᴰ span⁻ t⁻
  up-dur⁻ ε⁻ᵗ refl = ≤ᴰ-refl
  up-dur⁻ (operation⁻ o t) x∈ = op-dur o t x∈

  op-dur : ∀ o t {x} → ⟦ o ？ · up t ⟧ x → dur x ≤ᴰ costʰⁱ o +ᴰ span t
  op-dur o t (_ , x₂ , refl , inj₁ (o′ , dd , c , r , refl) , x₂∈)
    with code-injective (x∈⁅y⁆⇒x≡y (code o) c)
  ... | refl =
    +ᴰ-mono-≤ (rt-≤ o r) (up-dur t x₂∈)
  op-dur o t (_ , x₂ , refl , inj₂ refl , x₂∈) = ≤ᴰ-trans (up-dur t x₂∈) (≤ᴰ-+ˡ (span t) (costʰⁱ o))
