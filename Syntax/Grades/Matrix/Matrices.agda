------------------------------------------------------------------------
-- Matrices over the modes, with entries in a dioid.                  --
--                                                                    --
-- A matrix gives each pair of modes an entry of the dioid. It names  --
-- finitely many modes and treats all the others alike: its entries   --
-- are those between two named modes, from a named mode to one not    --
-- named and back, from a mode not named to itself and to another,    --
-- and into `stuck`. The row of `stuck` is that of the unit: `𝟙` into --
-- `stuck` and `𝟘` elsewhere, so that `stuck` is absorbing.           --
--                                                                    --
-- The entries of a matrix are invariant under exchanging two modes   --
-- it does not name (`entry-swap`), and a matrix is given by its      --
-- entries at the representatives (`tabulate`, `tab-entry`). The      --
-- product is the matrix product, the entry from `x` to `y` the join  --
-- over the modes `q` of the entry from `x` to `q` followed by that   --
-- from `q` to `y`: the join over the named modes, `x`, `y`, `stuck`  --
-- and one fresh mode is the least upper bound over all modes         --
-- (`⊗ᴹ-ub`, `⊗ᴹ-lub`), the others all alike. The join, the order and --
-- `⊤ᴹ` are entrywise, the order decided at the representatives       --
-- (`≤ᴹ⇒pointwise`). The product is associative, has the unit `Iᴹ`,   --
-- is monotone and distributes over the join, entrywise.              --
------------------------------------------------------------------------

open import Syntax.Grades.Indexed using (Names)
open import Syntax.Grades.Matrix.Dioid using (Dioid)

module Syntax.Grades.Matrix.Matrices (𝒩 : Names) (S : Dioid) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_; map′)

open import Function.Base using (_$_)

open import Util.Equality

open Dioid S
open import Syntax.Grades.Matrix.Modes 𝒩

------------------------------------------------------------------------
-- Matrices

record Matrix : Set where
  constructor matrix
  field
    modes        : List Name
    within       : Name → Name → Carrier   -- between named modes
    leaving      : Name → Carrier          -- from a named mode to one not named
    entering     : Name → Carrier          -- from a mode not named to a named one
    toStuck      : Name → Carrier          -- from a named mode into `stuck`
    staying      : Carrier                 -- from a mode not named to itself
    moving       : Carrier                 -- from a mode not named to another
    otherToStuck : Carrier                 -- from a mode not named into `stuck`

open Matrix public

entry : Matrix → Mode → Mode → Carrier
entry M stuck   stuck   = 𝟙
entry M stuck   ⌜ _ ⌝ = 𝟘
entry M ⌜ p ⌝ stuck with p ∈? modes M
... | yes _ = toStuck M p
... | no _  = otherToStuck M
entry M ⌜ p ⌝ ⌜ q ⌝ with p ∈? modes M | q ∈? modes M
... | yes _ | yes _ = within M p q
... | yes _ | no _  = leaving M p
... | no _  | yes _ = entering M q
... | no _  | no _ with p ≟ᴺ q
...   | yes _ = staying M
...   | no _  = moving M

-- the entries by the kind of the modes

module _ (M : Matrix) where

  private F = modes M

  entry-yy : ∀ {p q} → p ∈ F → q ∈ F → entry M ⌜ p ⌝ ⌜ q ⌝ ≡ within M p q
  entry-yy {p} {q} p∈ q∈ with p ∈? F | q ∈? F
  ... | yes _ | yes _ = refl
  ... | no p∉ | _     = ⊥-elim (p∉ p∈)
  ... | yes _ | no q∉ = ⊥-elim (q∉ q∈)

  entry-yn : ∀ {p q} → p ∈ F → q ∉ F → entry M ⌜ p ⌝ ⌜ q ⌝ ≡ leaving M p
  entry-yn {p} {q} p∈ q∉ with p ∈? F | q ∈? F
  ... | yes _ | no _  = refl
  ... | no p∉ | _     = ⊥-elim (p∉ p∈)
  ... | yes _ | yes q∈ = ⊥-elim (q∉ q∈)

  entry-ny : ∀ {p q} → p ∉ F → q ∈ F → entry M ⌜ p ⌝ ⌜ q ⌝ ≡ entering M q
  entry-ny {p} {q} p∉ q∈ with p ∈? F | q ∈? F
  ... | no _   | yes _ = refl
  ... | yes p∈ | _     = ⊥-elim (p∉ p∈)
  ... | no _   | no q∉ = ⊥-elim (q∉ q∈)

  entry-nn-≡ : ∀ {p} → p ∉ F → entry M ⌜ p ⌝ ⌜ p ⌝ ≡ staying M
  entry-nn-≡ {p} p∉ with p ∈? F
  ... | yes p∈ = ⊥-elim (p∉ p∈)
  ... | no _ with p ≟ᴺ p
  ...   | yes _ = refl
  ...   | no ¬e = ⊥-elim (¬e refl)

  entry-nn-≢ : ∀ {p q} → p ∉ F → q ∉ F → ¬ p ≡ q → entry M ⌜ p ⌝ ⌜ q ⌝ ≡ moving M
  entry-nn-≢ {p} {q} p∉ q∉ p≢q with p ∈? F | q ∈? F
  ... | yes p∈ | _      = ⊥-elim (p∉ p∈)
  ... | no _   | yes q∈ = ⊥-elim (q∉ q∈)
  ... | no _   | no _ with p ≟ᴺ q
  ...   | yes e = ⊥-elim (p≢q e)
  ...   | no _  = refl

  entry-ys : ∀ {p} → p ∈ F → entry M ⌜ p ⌝ stuck ≡ toStuck M p
  entry-ys {p} p∈ with p ∈? F
  ... | yes _  = refl
  ... | no p∉  = ⊥-elim (p∉ p∈)

  entry-ns : ∀ {p} → p ∉ F → entry M ⌜ p ⌝ stuck ≡ otherToStuck M
  entry-ns {p} p∉ with p ∈? F
  ... | yes p∈ = ⊥-elim (p∉ p∈)
  ... | no _   = refl

  -- exchanging two modes not named keeps the entries

  entry-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ x y
             → entry M (swapᴹ a b x) (swapᴹ a b y) ≡ entry M x y
  entry-swap a∉ b∉ stuck stuck   = refl
  entry-swap a∉ b∉ stuck ⌜ q ⌝ = refl
  entry-swap {a} {b} a∉ b∉ ⌜ p ⌝ stuck = ps (p ∈? F)
    where
      ps : Dec (p ∈ F) → entry M ⌜ swap a b p ⌝ stuck ≡ entry M ⌜ p ⌝ stuck
      ps (yes p∈) = trans (entry-ys (subst (_∈ F) (sym (swap-∈ a∉ b∉ p∈)) p∈))
                          (trans (cong (toStuck M) (swap-∈ a∉ b∉ p∈)) (sym (entry-ys p∈)))
      ps (no p∉)  = trans (entry-ns (swap-∉ a∉ b∉ p∉)) (sym (entry-ns p∉))
  entry-swap {a} {b} a∉ b∉ ⌜ p ⌝ ⌜ q ⌝ = pq (p ∈? F) (q ∈? F) (p ≟ᴺ q)
    where
      pq : Dec (p ∈ F) → Dec (q ∈ F) → Dec (p ≡ q)
         → entry M ⌜ swap a b p ⌝ ⌜ swap a b q ⌝ ≡ entry M ⌜ p ⌝ ⌜ q ⌝
      pq (yes p∈) (yes q∈) _ =
        trans (cong₂ (λ m n → entry M ⌜ m ⌝ ⌜ n ⌝) (swap-∈ a∉ b∉ p∈) (swap-∈ a∉ b∉ q∈)) refl
      pq (yes p∈) (no q∉) _ =
        trans (cong (λ m → entry M ⌜ m ⌝ ⌜ swap a b q ⌝) (swap-∈ a∉ b∉ p∈))
              (trans (entry-yn p∈ (swap-∉ a∉ b∉ q∉)) (sym (entry-yn p∈ q∉)))
      pq (no p∉) (yes q∈) _ =
        trans (cong (λ n → entry M ⌜ swap a b p ⌝ ⌜ n ⌝) (swap-∈ a∉ b∉ q∈))
              (trans (entry-ny (swap-∉ a∉ b∉ p∉) q∈) (sym (entry-ny p∉ q∈)))
      pq (no p∉) (no q∉) (yes refl) =
        trans (entry-nn-≡ (swap-∉ a∉ b∉ p∉)) (sym (entry-nn-≡ p∉))
      pq (no p∉) (no q∉) (no p≢q) =
        trans (entry-nn-≢ (swap-∉ a∉ b∉ p∉) (swap-∉ a∉ b∉ q∉) (λ e → p≢q (swap-injective e)))
              (sym (entry-nn-≢ p∉ q∉ p≢q))

------------------------------------------------------------------------
-- Functions on pairs of modes alike outside a finite set of names

Uniform : List Name → (Mode → Mode → Carrier) → Set
Uniform F f = ∀ {a b} → a ∉ F → b ∉ F → ∀ x y → f (swapᴹ a b x) (swapᴹ a b y) ≈ f x y

-- with the row of `stuck` that of the unit

StuckRow : (Mode → Mode → Carrier) → Set
StuckRow f = (f stuck stuck ≈ 𝟙) × (∀ n → f stuck ⌜ n ⌝ ≈ 𝟘)

entry-uniform : ∀ {F} M → (∀ {n} → n ∈ modes M → n ∈ F) → Uniform F (entry M)
entry-uniform M sub a∉ b∉ x y =
  ≈-reflexive (entry-swap M (λ a∈ → a∉ (sub a∈)) (λ b∈ → b∉ (sub b∈)) x y)

entry-stuckRow : ∀ M → StuckRow (entry M)
entry-stuckRow M = ≈-refl , λ _ → ≈-refl

-- the matrix with the entries of `f` at the representatives

tabulate : List Name → (Mode → Mode → Carrier) → Matrix
tabulate F f = matrix F
  (λ p q → f ⌜ p ⌝ ⌜ q ⌝) (λ p → f ⌜ p ⌝ ⌜ o ⌝) (λ q → f ⌜ o ⌝ ⌜ q ⌝) (λ p → f ⌜ p ⌝ stuck)
  (f ⌜ o ⌝ ⌜ o ⌝) (f ⌜ o ⌝ ⌜ o' ⌝) (f ⌜ o ⌝ stuck)
  where open Representatives F

tab-entry : ∀ {F f} → Uniform F f → StuckRow f → ∀ x y → entry (tabulate F f) x y ≈ f x y
tab-entry {F} {f} uf (s₀ , s₁) stuck stuck   = ≈-sym s₀
tab-entry {F} {f} uf (s₀ , s₁) stuck ⌜ n ⌝ = ≈-sym (s₁ n)
tab-entry {F} {f} uf sr ⌜ p ⌝ y =
  via-representatives (λ x y → entry T x y ≈ f x y)
    (λ {a} {b} {x} {y} a∉ b∉ e →
       ≈-trans (≈-reflexive (entry-swap T a∉ b∉ x y)) (≈-trans e (≈-sym (uf a∉ b∉ x y))))
    (λ p∈ q∈ → ≈-reflexive (entry-yy T p∈ q∈))
    (λ p∈ → ≈-reflexive (entry-yn T p∈ o∉))
    (λ q∈ → ≈-reflexive (entry-ny T o∉ q∈))
    (≈-reflexive (entry-nn-≡ T o∉))
    (≈-reflexive (entry-nn-≢ T o∉ o'∉ o≢o'))
    (λ p∈ → ≈-reflexive (entry-ys T p∈))
    (≈-reflexive (entry-ns T o∉))
    p y
  where
    open Representatives F
    T = tabulate F f

------------------------------------------------------------------------
-- The order, decided at the representatives

record AtRepresentatives (F : List Name) (R : Mode → Mode → Set) : Set where
  constructor at-reps
  open Representatives F
  field
    yy : All (λ p → All (λ q → R ⌜ p ⌝ ⌜ q ⌝) F) F
    yo : All (λ p → R ⌜ p ⌝ ⌜ o ⌝) F
    oy : All (λ q → R ⌜ o ⌝ ⌜ q ⌝) F
    oo : R ⌜ o ⌝ ⌜ o ⌝
    oo' : R ⌜ o ⌝ ⌜ o' ⌝
    ys : All (λ p → R ⌜ p ⌝ stuck) F
    os : R ⌜ o ⌝ stuck

infix 4 _≤ᴹ_ _≤ᵖ_

_≤ᵖ_ : Matrix → Matrix → Set
M ≤ᵖ N = ∀ x y → entry M x y ≤ entry N x y

record _≤ᴹ_ (M N : Matrix) : Set where
  constructor ≤ᴹ-at
  field
    representatives : AtRepresentatives (modes M ++ modes N) (λ x y → entry M x y ≤ entry N x y)

pointwise⇒≤ᴹ : ∀ {M N} → M ≤ᵖ N → M ≤ᴹ N
pointwise⇒≤ᴹ {M} {N} f = ≤ᴹ-at $ at-reps
  (All.tabulate λ {p} _ → All.tabulate λ {q} _ → f ⌜ p ⌝ ⌜ q ⌝)
  (All.tabulate λ {p} _ → f ⌜ p ⌝ ⌜ o ⌝)
  (All.tabulate λ {q} _ → f ⌜ o ⌝ ⌜ q ⌝)
  (f ⌜ o ⌝ ⌜ o ⌝) (f ⌜ o ⌝ ⌜ o' ⌝)
  (All.tabulate λ {p} _ → f ⌜ p ⌝ stuck)
  (f ⌜ o ⌝ stuck)
  where open Representatives (modes M ++ modes N)

≤ᴹ⇒pointwise : ∀ {M N} → M ≤ᴹ N → M ≤ᵖ N
≤ᴹ⇒pointwise {M} {N} r stuck stuck   = ≤-refl
≤ᴹ⇒pointwise {M} {N} r stuck ⌜ _ ⌝ = ≤-refl
≤ᴹ⇒pointwise {M} {N} (≤ᴹ-at (at-reps yy yo oy oo oo' ys os)) ⌜ p ⌝ y =
  via-representatives (λ x y → entry M x y ≤ entry N x y)
    (λ {a} {b} {x} {y} a∉ b∉ e →
       subst₂ _≤_ (sym (entry-swap M (λ a∈ → a∉ (∈-++⁺ˡ a∈)) (λ b∈ → b∉ (∈-++⁺ˡ b∈)) x y))
                  (sym (entry-swap N (λ a∈ → a∉ (∈-++⁺ʳ (modes M) a∈))
                                     (λ b∈ → b∉ (∈-++⁺ʳ (modes M) b∈)) x y)) e)
    (λ p∈ q∈ → All.lookup (All.lookup yy p∈) q∈)
    (All.lookup yo) (All.lookup oy) oo oo' (All.lookup ys) os
    p y
  where open Representatives (modes M ++ modes N)

_≤ᴹ?_ : ∀ M N → Dec (M ≤ᴹ N)
M ≤ᴹ? N =
  map′ (λ (a , b , c , d , e , f , g) → ≤ᴹ-at (at-reps a b c d e f g))
       (λ (≤ᴹ-at (at-reps a b c d e f g)) → a , b , c , d , e , f , g)
       (All.all? (λ p → All.all? (λ q → entry M ⌜ p ⌝ ⌜ q ⌝ ≤? entry N ⌜ p ⌝ ⌜ q ⌝) F) F
        ×-dec All.all? (λ p → entry M ⌜ p ⌝ ⌜ o ⌝ ≤? entry N ⌜ p ⌝ ⌜ o ⌝) F
        ×-dec All.all? (λ q → entry M ⌜ o ⌝ ⌜ q ⌝ ≤? entry N ⌜ o ⌝ ⌜ q ⌝) F
        ×-dec (entry M ⌜ o ⌝ ⌜ o ⌝ ≤? entry N ⌜ o ⌝ ⌜ o ⌝)
        ×-dec (entry M ⌜ o ⌝ ⌜ o' ⌝ ≤? entry N ⌜ o ⌝ ⌜ o' ⌝)
        ×-dec All.all? (λ p → entry M ⌜ p ⌝ stuck ≤? entry N ⌜ p ⌝ stuck) F
        ×-dec (entry M ⌜ o ⌝ stuck ≤? entry N ⌜ o ⌝ stuck))
  where
    F = modes M ++ modes N
    open Representatives F

≤ᴹ-irrelevant : ∀ {M N} (r r' : M ≤ᴹ N) → r ≡ r'
≤ᴹ-irrelevant (≤ᴹ-at (at-reps a b c d e f g)) (≤ᴹ-at (at-reps a' b' c' d' e' f' g')) =
  cong ≤ᴹ-at $ cong₇ at-reps (All.irrelevant (All.irrelevant ≤-irrelevant) a a')
                (All.irrelevant ≤-irrelevant b b') (All.irrelevant ≤-irrelevant c c')
                (≤-irrelevant d d') (≤-irrelevant e e')
                (All.irrelevant ≤-irrelevant f f') (≤-irrelevant g g')
  where
    cong₇ : ∀ {A B C D E G H X : Set} (h : A → B → C → D → E → G → H → X)
          → ∀ {a a' b b' c c' d d' e e' g g' k k'}
          → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → g ≡ g' → k ≡ k'
          → h a b c d e g k ≡ h a' b' c' d' e' g' k'
    cong₇ h refl refl refl refl refl refl refl = refl

------------------------------------------------------------------------
-- The unit, the greatest matrix and the join

Iᴹ : Matrix
Iᴹ = matrix [] (λ _ _ → 𝟘) (λ _ → 𝟘) (λ _ → 𝟘) (λ _ → 𝟘) 𝟙 𝟘 𝟘

Iᴹ-diag : ∀ x → entry Iᴹ x x ≡ 𝟙
Iᴹ-diag stuck   = refl
Iᴹ-diag ⌜ p ⌝ = entry-nn-≡ Iᴹ {p} (λ ())

Iᴹ-off : ∀ {x y} → ¬ x ≡ y → entry Iᴹ x y ≡ 𝟘
Iᴹ-off {stuck}   {stuck}   ne = ⊥-elim (ne refl)
Iᴹ-off {stuck}   {⌜ _ ⌝} ne = refl
Iᴹ-off {⌜ p ⌝} {stuck}   ne = entry-ns Iᴹ {p} (λ ())
Iᴹ-off {⌜ p ⌝} {⌜ q ⌝} ne = entry-nn-≢ Iᴹ (λ ()) (λ ()) (λ e → ne (cong ⌜_⌝ e))

-- every mode `stuck` or a name: decide equality of modes

_≟ᴹ_ : (x y : Mode) → Dec (x ≡ y)
stuck   ≟ᴹ stuck   = yes refl
stuck   ≟ᴹ ⌜ _ ⌝ = no λ ()
⌜ _ ⌝ ≟ᴹ stuck   = no λ ()
⌜ p ⌝ ≟ᴹ ⌜ q ⌝ with p ≟ᴺ q
... | yes refl = yes refl
... | no ne    = no λ e → ne (⌜⌝-injective e)

⊤ᴹ : Matrix
⊤ᴹ = matrix [] (λ _ _ → ⊤) (λ _ → ⊤) (λ _ → ⊤) (λ _ → ⊤) ⊤ ⊤ ⊤

⊤ᴹ-entry : ∀ p y → entry ⊤ᴹ ⌜ p ⌝ y ≡ ⊤
⊤ᴹ-entry p stuck = entry-ns ⊤ᴹ {p} (λ ())
⊤ᴹ-entry p ⌜ q ⌝ = case (p ≟ᴺ q)
  where
    case : Dec (p ≡ q) → entry ⊤ᴹ ⌜ p ⌝ ⌜ q ⌝ ≡ ⊤
    case (yes refl) = entry-nn-≡ ⊤ᴹ {p} (λ ())
    case (no ne)    = entry-nn-≢ ⊤ᴹ (λ ()) (λ ()) ne

infixl 6 _⊕ᴹ_
infixl 7 _⊗ᴹ_

private
  joinᶠ : Matrix → Matrix → Mode → Mode → Carrier
  joinᶠ M N x y = entry M x y ⊕ entry N x y

  joinᶠ-uniform : ∀ M N → Uniform (modes M ++ modes N) (joinᶠ M N)
  joinᶠ-uniform M N a∉ b∉ x y =
    ⊕-mono (proj₁ (u₁ x y)) (proj₁ (u₂ x y)) , ⊕-mono (proj₂ (u₁ x y)) (proj₂ (u₂ x y))
    where
      u₁ = entry-uniform M ∈-++⁺ˡ a∉ b∉
      u₂ = entry-uniform N (∈-++⁺ʳ (modes M)) a∉ b∉

  joinᶠ-stuckRow : ∀ M N → StuckRow (joinᶠ M N)
  joinᶠ-stuckRow M N = (⊕-lub ≤-refl ≤-refl , ⊕-ubˡ 𝟙 𝟙) , λ _ → ⊕-lub ≤-refl ≤-refl , 𝟘-≤ _

_⊕ᴹ_ : Matrix → Matrix → Matrix
M ⊕ᴹ N = tabulate (modes M ++ modes N) (joinᶠ M N)

⊕ᴹ-entry : ∀ M N x y → entry (M ⊕ᴹ N) x y ≈ entry M x y ⊕ entry N x y
⊕ᴹ-entry M N = tab-entry (joinᶠ-uniform M N) (joinᶠ-stuckRow M N)

------------------------------------------------------------------------
-- The product

module Product (M N : Matrix) where

  F : List Name
  F = modes M ++ modes N

  names : Mode → List Name
  names stuck   = []
  names ⌜ n ⌝ = n ∷ []

  -- the modes the join runs over: those named, `x`, `y`, `stuck` and a
  -- fresh one

  fresh-for : Mode → Mode → Name
  fresh-for x y = fresh (names x ++ names y ++ F)

  candidates : Mode → Mode → List Mode
  candidates x y = stuck ∷ x ∷ y ∷ ⌜ fresh-for x y ⌝ ∷ mapᴸ ⌜_⌝ F

  term : Mode → Mode → Mode → Carrier
  term x y q = entry M x q ⊗ entry N q y

  prod : Mode → Mode → Carrier
  prod x y = ⨁ (mapᴸ (term x y) (candidates x y))

  private
    fresh-∉F : ∀ x y → fresh-for x y ∉ F
    fresh-∉F x y p = fresh-∉ _ (∈-++⁺ʳ (names x) (∈-++⁺ʳ (names y) p))

    fresh-≢ˡ : ∀ x y → ¬ x ≡ ⌜ fresh-for x y ⌝
    fresh-≢ˡ ⌜ n ⌝ y e = fresh-∉ _ (here (sym (⌜⌝-injective e)))

    fresh-≢ʳ : ∀ x y → ¬ y ≡ ⌜ fresh-for x y ⌝
    fresh-≢ʳ x ⌜ n ⌝ e = fresh-∉ _ (∈-++⁺ʳ (names x) (here (sym (⌜⌝-injective e))))

    swap-fixᴹ : ∀ {a b x} → ¬ x ≡ ⌜ a ⌝ → ¬ x ≡ ⌜ b ⌝ → swapᴹ a b x ≡ x
    swap-fixᴹ {x = stuck}   _  _  = refl
    swap-fixᴹ {x = ⌜ n ⌝} na nb = cong ⌜_⌝ (swap-fix (λ e → na (cong ⌜_⌝ e)) (λ e → nb (cong ⌜_⌝ e)))

    ∉M : ∀ {n} → n ∉ F → n ∉ modes M
    ∉M n∉ n∈ = n∉ (∈-++⁺ˡ n∈)

    ∉N : ∀ {n} → n ∉ F → n ∉ modes N
    ∉N n∉ n∈ = n∉ (∈-++⁺ʳ (modes M) n∈)

  prod-ub : ∀ x y q → term x y q ≤ prod x y
  prod-ub x y stuck = ⨁-ub (mapᴸ (term x y) (candidates x y)) (here refl)
  prod-ub x y ⌜ n ⌝ with ⌜ n ⌝ ≟ᴹ x | ⌜ n ⌝ ≟ᴹ y | n ∈? F
  ... | yes refl | _ | _ = ⨁-ub (mapᴸ (term x y) (candidates x y)) (there (here refl))
  ... | no _ | yes refl | _ = ⨁-ub (mapᴸ (term x y) (candidates x y)) (there (there (here refl)))
  ... | no _ | no _ | yes n∈ = ⨁-ub (mapᴸ (term x y) (candidates x y)) (there (there (there (there (∈-map⁺ (term x y) (∈-map⁺ ⌜_⌝ n∈))))))
  ... | no nx | no ny | no n∉ =
    subst (_≤ prod x y) (sym same) (⨁-ub (mapᴸ (term x y) (candidates x y)) (there (there (there (here refl)))))
    where
      f = fresh-for x y
      f∉ = fresh-∉F x y
      -- exchanging `n` and the fresh mode fixes `x` and `y`
      fx : swapᴹ n f x ≡ x
      fx = swap-fixᴹ (λ e → nx (sym e)) (fresh-≢ˡ x y)
      fy : swapᴹ n f y ≡ y
      fy = swap-fixᴹ (λ e → ny (sym e)) (fresh-≢ʳ x y)
      same : term x y ⌜ n ⌝ ≡ term x y ⌜ f ⌝
      same = cong₂ _⊗_
        (trans (sym (cong₂ (entry M) fx (cong ⌜_⌝ (swap-b n f))))
               (entry-swap M (∉M n∉) (∉M f∉) x ⌜ f ⌝))
        (trans (sym (cong₂ (entry N) (cong ⌜_⌝ (swap-b n f)) fy))
               (entry-swap N (∉N n∉) (∉N f∉) ⌜ f ⌝ y))

  prod-lub : ∀ x y {t} → (∀ q → term x y q ≤ t) → prod x y ≤ t
  prod-lub x y f = ⨁-lub (mapᴸ (term x y) (candidates x y)) λ a∈ → case (∈-map⁻ (term x y) a∈)
    where
      case : ∀ {a} → (∃ λ q → q ∈ candidates x y × a ≡ term x y q) → a ≤ _
      case (q , _ , refl) = f q

  prod-lub-⊗ʳ : ∀ x y {c t} → (∀ q → term x y q ⊗ c ≤ t) → prod x y ⊗ c ≤ t
  prod-lub-⊗ʳ x y f = ⨁-lub-⊗ʳ (mapᴸ (term x y) (candidates x y)) λ a∈ → case (∈-map⁻ (term x y) a∈)
    where
      case : ∀ {a} → (∃ λ q → q ∈ candidates x y × a ≡ term x y q) → a ⊗ _ ≤ _
      case (q , _ , refl) = f q

  prod-lub-⊗ˡ : ∀ x y {c t} → (∀ q → c ⊗ term x y q ≤ t) → c ⊗ prod x y ≤ t
  prod-lub-⊗ˡ x y f = ⨁-lub-⊗ˡ (mapᴸ (term x y) (candidates x y)) λ a∈ → case (∈-map⁻ (term x y) a∈)
    where
      case : ∀ {a} → (∃ λ q → q ∈ candidates x y × a ≡ term x y q) → _ ⊗ a ≤ _
      case (q , _ , refl) = f q

  prod-uniform : Uniform F prod
  prod-uniform {a} {b} a∉ b∉ x y =
      prod-lub (swapᴹ a b x) (swapᴹ a b y) (λ q → subst (_≤ prod x y) (sym (back q)) (prod-ub x y (swapᴹ a b q)))
    , prod-lub x y (λ q → subst (_≤ prod (swapᴹ a b x) (swapᴹ a b y)) (forth q)
                         (prod-ub (swapᴹ a b x) (swapᴹ a b y) (swapᴹ a b q)))
    where
      back : ∀ q → term (swapᴹ a b x) (swapᴹ a b y) q ≡ term x y (swapᴹ a b q)
      back q = cong₂ _⊗_
        (trans (cong (entry M (swapᴹ a b x)) (sym (swapᴹ-inv a b q)))
               (entry-swap M (∉M a∉) (∉M b∉) x (swapᴹ a b q)))
        (trans (cong (λ z → entry N z (swapᴹ a b y)) (sym (swapᴹ-inv a b q)))
               (entry-swap N (∉N a∉) (∉N b∉) (swapᴹ a b q) y))
      forth : ∀ q → term (swapᴹ a b x) (swapᴹ a b y) (swapᴹ a b q) ≡ term x y q
      forth q = cong₂ _⊗_ (entry-swap M (∉M a∉) (∉M b∉) x q) (entry-swap N (∉N a∉) (∉N b∉) q y)

  prod-stuckRow : StuckRow prod
  prod-stuckRow =
      ( prod-lub stuck stuck (λ { stuck → proj₁ (⊗-identityˡ 𝟙)
                 ; ⌜ n ⌝ → ≤-trans (⊗-zeroˡ _) (𝟘-≤ 𝟙) })
      , ≤-trans (proj₂ (⊗-identityˡ 𝟙)) (prod-ub stuck stuck stuck) )
    , λ n → prod-lub stuck ⌜ n ⌝ (λ { stuck → ⊗-zeroʳ 𝟙
                     ; ⌜ m ⌝ → ⊗-zeroˡ _ })
          , 𝟘-≤ _

_⊗ᴹ_ : Matrix → Matrix → Matrix
M ⊗ᴹ N = tabulate (Product.F M N) (Product.prod M N)

-- the entries of a product are the least upper bounds of the terms

⊗ᴹ-entry : ∀ M N x y → entry (M ⊗ᴹ N) x y ≈ Product.prod M N x y
⊗ᴹ-entry M N = tab-entry (Product.prod-uniform M N) (Product.prod-stuckRow M N)

⊗ᴹ-ub : ∀ M N x y q → entry M x q ⊗ entry N q y ≤ entry (M ⊗ᴹ N) x y
⊗ᴹ-ub M N x y q = ≤-trans (Product.prod-ub M N x y q) (proj₂ (⊗ᴹ-entry M N x y))

⊗ᴹ-lub : ∀ M N x y {t} → (∀ q → entry M x q ⊗ entry N q y ≤ t) → entry (M ⊗ᴹ N) x y ≤ t
⊗ᴹ-lub M N x y f = ≤-trans (proj₁ (⊗ᴹ-entry M N x y)) (Product.prod-lub M N x y f)

⊗ᴹ-lub-⊗ʳ : ∀ M N x y {c t} → (∀ q → (entry M x q ⊗ entry N q y) ⊗ c ≤ t)
          → entry (M ⊗ᴹ N) x y ⊗ c ≤ t
⊗ᴹ-lub-⊗ʳ M N x y f =
  ≤-trans (⊗-mono (proj₁ (⊗ᴹ-entry M N x y)) ≤-refl) (Product.prod-lub-⊗ʳ M N x y f)

⊗ᴹ-lub-⊗ˡ : ∀ M N x y {c t} → (∀ q → c ⊗ (entry M x q ⊗ entry N q y) ≤ t)
          → c ⊗ entry (M ⊗ᴹ N) x y ≤ t
⊗ᴹ-lub-⊗ˡ M N x y f =
  ≤-trans (⊗-mono ≤-refl (proj₁ (⊗ᴹ-entry M N x y))) (Product.prod-lub-⊗ˡ M N x y f)

------------------------------------------------------------------------
-- The laws, entrywise

⊗ᴹ-assoc : ∀ M N P → (M ⊗ᴹ N) ⊗ᴹ P ≤ᵖ M ⊗ᴹ (N ⊗ᴹ P)
⊗ᴹ-assoc M N P x z = ⊗ᴹ-lub (M ⊗ᴹ N) P x z λ r → ⊗ᴹ-lub-⊗ʳ M N x r λ q →
  ≤-trans (proj₁ (⊗-assoc _ _ _))
    (≤-trans (⊗-mono ≤-refl (⊗ᴹ-ub N P q z r)) (⊗ᴹ-ub M (N ⊗ᴹ P) x z q))

⊗ᴹ-assoc⁻ : ∀ M N P → M ⊗ᴹ (N ⊗ᴹ P) ≤ᵖ (M ⊗ᴹ N) ⊗ᴹ P
⊗ᴹ-assoc⁻ M N P x z = ⊗ᴹ-lub M (N ⊗ᴹ P) x z λ q → ⊗ᴹ-lub-⊗ˡ N P q z λ r →
  ≤-trans (proj₂ (⊗-assoc _ _ _))
    (≤-trans (⊗-mono (⊗ᴹ-ub M N x r q) ≤-refl) (⊗ᴹ-ub (M ⊗ᴹ N) P x z r))

⊗ᴹ-identityˡ : ∀ M → Iᴹ ⊗ᴹ M ≤ᵖ M
⊗ᴹ-identityˡ M x y = ⊗ᴹ-lub Iᴹ M x y λ q → case q (x ≟ᴹ q)
  where
    case : ∀ q → Dec (x ≡ q) → entry Iᴹ x q ⊗ entry M q y ≤ entry M x y
    case q (yes refl) =
      subst (λ c → c ⊗ entry M x y ≤ entry M x y) (sym (Iᴹ-diag x)) (proj₁ (⊗-identityˡ _))
    case q (no ne) =
      subst (λ c → c ⊗ entry M q y ≤ entry M x y) (sym (Iᴹ-off ne)) (≤-trans (⊗-zeroˡ _) (𝟘-≤ _))

⊗ᴹ-identityˡ⁻ : ∀ M → M ≤ᵖ Iᴹ ⊗ᴹ M
⊗ᴹ-identityˡ⁻ M x y =
  ≤-trans (proj₂ (⊗-identityˡ _))
    (subst (λ c → c ⊗ entry M x y ≤ entry (Iᴹ ⊗ᴹ M) x y) (Iᴹ-diag x) (⊗ᴹ-ub Iᴹ M x y x))

⊗ᴹ-identityʳ : ∀ M → M ⊗ᴹ Iᴹ ≤ᵖ M
⊗ᴹ-identityʳ M x y = ⊗ᴹ-lub M Iᴹ x y λ q → case q (q ≟ᴹ y)
  where
    case : ∀ q → Dec (q ≡ y) → entry M x q ⊗ entry Iᴹ q y ≤ entry M x y
    case q (yes refl) =
      subst (λ c → entry M x q ⊗ c ≤ entry M x q) (sym (Iᴹ-diag q)) (proj₁ (⊗-identityʳ _))
    case q (no ne) =
      subst (λ c → entry M x q ⊗ c ≤ entry M x y) (sym (Iᴹ-off ne)) (≤-trans (⊗-zeroʳ _) (𝟘-≤ _))

⊗ᴹ-identityʳ⁻ : ∀ M → M ≤ᵖ M ⊗ᴹ Iᴹ
⊗ᴹ-identityʳ⁻ M x y =
  ≤-trans (proj₂ (⊗-identityʳ _))
    (subst (λ c → entry M x y ⊗ c ≤ entry (M ⊗ᴹ Iᴹ) x y) (Iᴹ-diag y) (⊗ᴹ-ub M Iᴹ x y y))

⊗ᴹ-mono : ∀ {M M' N N'} → M ≤ᵖ M' → N ≤ᵖ N' → M ⊗ᴹ N ≤ᵖ M' ⊗ᴹ N'
⊗ᴹ-mono {M} {M'} {N} {N'} p q x y =
  ⊗ᴹ-lub M N x y λ r → ≤-trans (⊗-mono (p x r) (q r y)) (⊗ᴹ-ub M' N' x y r)

⊗ᴹ-distribˡ : ∀ M N P → M ⊗ᴹ (N ⊕ᴹ P) ≤ᵖ (M ⊗ᴹ N) ⊕ᴹ (M ⊗ᴹ P)
⊗ᴹ-distribˡ M N P x y =
  ≤-trans
    (⊗ᴹ-lub M (N ⊕ᴹ P) x y λ q →
      ≤-trans (⊗-mono ≤-refl (proj₁ (⊕ᴹ-entry N P q y)))
        (≤-trans (⊗-distribˡ _ _ _) (⊕-mono (⊗ᴹ-ub M N x y q) (⊗ᴹ-ub M P x y q))))
    (proj₂ (⊕ᴹ-entry (M ⊗ᴹ N) (M ⊗ᴹ P) x y))

⊗ᴹ-distribʳ : ∀ M N P → (N ⊕ᴹ P) ⊗ᴹ M ≤ᵖ (N ⊗ᴹ M) ⊕ᴹ (P ⊗ᴹ M)
⊗ᴹ-distribʳ M N P x y =
  ≤-trans
    (⊗ᴹ-lub (N ⊕ᴹ P) M x y λ q →
      ≤-trans (⊗-mono (proj₁ (⊕ᴹ-entry N P x q)) ≤-refl)
        (≤-trans (⊗-distribʳ _ _ _) (⊕-mono (⊗ᴹ-ub N M x y q) (⊗ᴹ-ub P M x y q))))
    (proj₂ (⊕ᴹ-entry (N ⊗ᴹ M) (P ⊗ᴹ M) x y))

⊕ᴹ-ubˡ : ∀ M N → M ≤ᵖ M ⊕ᴹ N
⊕ᴹ-ubˡ M N x y = ≤-trans (⊕-ubˡ _ _) (proj₂ (⊕ᴹ-entry M N x y))

⊕ᴹ-ubʳ : ∀ M N → N ≤ᵖ M ⊕ᴹ N
⊕ᴹ-ubʳ M N x y = ≤-trans (⊕-ubʳ _ _) (proj₂ (⊕ᴹ-entry M N x y))

⊕ᴹ-lub : ∀ {M N P} → M ≤ᵖ P → N ≤ᵖ P → M ⊕ᴹ N ≤ᵖ P
⊕ᴹ-lub {M} {N} p q x y = ≤-trans (proj₁ (⊕ᴹ-entry M N x y)) (⊕-lub (p x y) (q x y))
