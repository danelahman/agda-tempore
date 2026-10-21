------------------------------------------------------------------------
-- Matrices over the modes, with entries in an equivariant dioid.     --
--                                                                    --
-- A matrix gives each pair of modes an entry of the dioid, and names --
-- finitely many modes `F`: exchanging two modes it does not name     --
-- acts on its entries as on the dioid, the entry from `σ x` to `σ y` --
-- being `σ` applied to the entry from `x` to `y` (equivariance). The --
-- row of `stuck` is that of the unit, `𝟙` into `stuck` and `𝟘`       --
-- elsewhere, so that `stuck` is absorbing.                           --
--                                                                    --
-- The product is the matrix product: the entry from `x` to `y` is    --
-- the join over all modes `q` of the entry from `x` to `q` followed  --
-- by that from `q` to `y`. The modes not named, other than `x` and   --
-- `y`, form one orbit under the permutations fixing the named modes, --
-- `x` and `y`, so the join is the orbit join of the finite join over --
-- the named modes, `x`, `y`, `stuck` and one fresh mode (`⊗ᴹ-ub`,    --
-- `⊗ᴹ-lub`). The join, the order and `⊤ᴹ` are entrywise, the order   --
-- decided at the representatives (`≤ᴹ⇒pointwise`). The product is    --
-- associative, has the unit `Iᴹ`, is monotone and distributes over   --
-- the join, entrywise.                                               --
------------------------------------------------------------------------

open import Syntax.Grades.Indexed using (Names)
open import Syntax.Grades.Matrix.Dioid using (Dioid)
open import Syntax.Grades.Matrix.Nominal using (Equivariant)

module Syntax.Grades.Matrix.Matrices (𝒩 : Names) (S : Dioid) (Eq : Equivariant 𝒩 S) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Function.Base using (_$_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_; map′)

open import Util.Equality

open Dioid S
open Equivariant Eq
open import Syntax.Grades.Matrix.Modes 𝒩
open import Syntax.Grades.Matrix.Nominal 𝒩 using (Perm; Fixes; along)

------------------------------------------------------------------------
-- Equivariant functions on pairs of modes

Equivariantᶠ : List Name → (Mode → Mode → Carrier) → Set
Equivariantᶠ F f =
  ∀ {a b} → a ∉ F → b ∉ F → ∀ x y → f (swapᴹ a b x) (swapᴹ a b y) ≈ act a b (f x y)

Equivariantᶠ-⊆ : ∀ {F F' f} → (∀ {n} → n ∈ F → n ∈ F') → Equivariantᶠ F f → Equivariantᶠ F' f
Equivariantᶠ-⊆ sub e a∉ b∉ = e (λ a∈ → a∉ (sub a∈)) (λ b∈ → b∉ (sub b∈))

------------------------------------------------------------------------
-- Matrices

record Matrix : Set where
  no-eta-equality
  constructor matrix
  field
    modes       : List Name
    row         : Name → Mode → Carrier
    equivariant : ∀ {a b} → a ∉ modes → b ∉ modes → ∀ p y
                → row (swap a b p) (swapᴹ a b y) ≈ act a b (row p y)

open Matrix public

entry : Matrix → Mode → Mode → Carrier
entry M stuck   stuck   = 𝟙
entry M stuck   ⌜ _ ⌝ = 𝟘
entry M ⌜ p ⌝ y       = row M p y

entry-equivariant : ∀ M → Equivariantᶠ (modes M) (entry M)
entry-equivariant M {a} {b} a∉ b∉ stuck stuck   = ≈-sym (act-𝟙 a b)
entry-equivariant M {a} {b} a∉ b∉ stuck ⌜ _ ⌝ = ≈-sym (act-𝟘 a b)
entry-equivariant M a∉ b∉ ⌜ p ⌝ y       = equivariant M a∉ b∉ p y

entry-equivariant-⊆ : ∀ {F} M → (∀ {n} → n ∈ modes M → n ∈ F) → Equivariantᶠ F (entry M)
entry-equivariant-⊆ M sub = Equivariantᶠ-⊆ sub (entry-equivariant M)

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
       ≤-trans (proj₁ (entry-equivariant-⊆ M ∈-++⁺ˡ a∉ b∉ x y))
         (≤-trans (act-mono e) (proj₂ (entry-equivariant-⊆ N (∈-++⁺ʳ (modes M)) a∉ b∉ x y))))
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

_≟ᴹ_ : (x y : Mode) → Dec (x ≡ y)
stuck   ≟ᴹ stuck   = yes refl
stuck   ≟ᴹ ⌜ _ ⌝ = no λ ()
⌜ _ ⌝ ≟ᴹ stuck   = no λ ()
⌜ p ⌝ ≟ᴹ ⌜ q ⌝ with p ≟ᴺ q
... | yes refl = yes refl
... | no ne    = no λ e → ne (⌜⌝-injective e)

private
  -- the entry of the unit
  diag : Mode → Mode → Carrier
  diag x y with x ≟ᴹ y
  ... | yes _ = 𝟙
  ... | no _  = 𝟘

  diag-≡ : ∀ x → diag x x ≡ 𝟙
  diag-≡ x with x ≟ᴹ x
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  diag-≢ : ∀ {x y} → ¬ x ≡ y → diag x y ≡ 𝟘
  diag-≢ {x} {y} ne with x ≟ᴹ y
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

  swapᴹ-injective : ∀ {a b x y} → swapᴹ a b x ≡ swapᴹ a b y → x ≡ y
  swapᴹ-injective {a} {b} {x} {y} e =
    trans (sym (swapᴹ-inv a b x)) (trans (cong (swapᴹ a b) e) (swapᴹ-inv a b y))

  diag-swap : ∀ a b x y → diag (swapᴹ a b x) (swapᴹ a b y) ≈ act a b (diag x y)
  diag-swap a b x y with x ≟ᴹ y
  ... | yes refl = ≈-trans (≈-reflexive (diag-≡ (swapᴹ a b x))) (≈-sym (act-𝟙 a b))
  ... | no ne    = ≈-trans (≈-reflexive (diag-≢ (λ e → ne (swapᴹ-injective e)))) (≈-sym (act-𝟘 a b))

-- the operations are given by copatterns, so that a matrix term is
-- unfolded only when its entries are asked for

Iᴹ : Matrix
modes Iᴹ = []
row Iᴹ p y = diag ⌜ p ⌝ y
equivariant Iᴹ _ _ p y = diag-swap _ _ ⌜ p ⌝ y

Iᴹ-diag : ∀ x → entry Iᴹ x x ≡ 𝟙
Iᴹ-diag stuck   = refl
Iᴹ-diag ⌜ p ⌝ = diag-≡ ⌜ p ⌝

Iᴹ-off : ∀ {x y} → ¬ x ≡ y → entry Iᴹ x y ≡ 𝟘
Iᴹ-off {stuck}   {stuck}   ne = ⊥-elim (ne refl)
Iᴹ-off {stuck}   {⌜ _ ⌝} ne = refl
Iᴹ-off {⌜ p ⌝} {y}       ne = diag-≢ ne

⊤ᴹ : Matrix
modes ⊤ᴹ = []
row ⊤ᴹ _ _ = ⊤
equivariant ⊤ᴹ {a} {b} _ _ _ _ = ≈-sym (act-⊤ a b)

⊤ᴹ-entry : ∀ p y → entry ⊤ᴹ ⌜ p ⌝ y ≡ ⊤
⊤ᴹ-entry p y = refl

infixl 6 _⊕ᴹ_
infixl 7 _⊗ᴹ_

private
  ⊕-cong : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → a ⊕ b ≈ a' ⊕ b'
  ⊕-cong (p , p') (q , q') = ⊕-mono p q , ⊕-mono p' q'

_⊕ᴹ_ : Matrix → Matrix → Matrix
modes (M ⊕ᴹ N) = modes M ++ modes N
row (M ⊕ᴹ N) p y = row M p y ⊕ row N p y
equivariant (M ⊕ᴹ N) {a} {b} a∉ b∉ p y =
  ≈-trans (⊕-cong (equivariant M (λ a∈ → a∉ (∈-++⁺ˡ a∈)) (λ b∈ → b∉ (∈-++⁺ˡ b∈)) p y)
                  (equivariant N (λ a∈ → a∉ (∈-++⁺ʳ (modes M) a∈))
                                 (λ b∈ → b∉ (∈-++⁺ʳ (modes M) b∈)) p y))
          (≈-sym (act-⊕ a b _ _))

⊕ᴹ-entry : ∀ M N x y → entry (M ⊕ᴹ N) x y ≈ entry M x y ⊕ entry N x y
⊕ᴹ-entry M N stuck stuck   = ⊕-ubˡ 𝟙 𝟙 , ⊕-lub ≤-refl ≤-refl
⊕ᴹ-entry M N stuck ⌜ _ ⌝ = 𝟘-≤ _ , ⊕-lub ≤-refl ≤-refl
⊕ᴹ-entry M N ⌜ p ⌝ y     = ≈-refl

------------------------------------------------------------------------
-- The action of permutations

private
  actᴾ-mono : ∀ π {x y} → x ≤ y → actᴾ π x ≤ actᴾ π y
  actᴾ-mono []            p = p
  actᴾ-mono ((a , b) ∷ π) p = act-mono (actᴾ-mono π p)

  actᴾ-𝟘 : ∀ π → actᴾ π 𝟘 ≤ 𝟘
  actᴾ-𝟘 []            = ≤-refl
  actᴾ-𝟘 ((a , b) ∷ π) = ≤-trans (act-mono (actᴾ-𝟘 π)) (proj₁ (act-𝟘 a b))

  actᴾ-⊕ : ∀ π x y → actᴾ π (x ⊕ y) ≤ actᴾ π x ⊕ actᴾ π y
  actᴾ-⊕ []            x y = ≤-refl
  actᴾ-⊕ ((a , b) ∷ π) x y = ≤-trans (act-mono (actᴾ-⊕ π x y)) (proj₁ (act-⊕ a b _ _))

  actᴾ-⨁ : ∀ π as → actᴾ π (⨁ as) ≤ ⨁ (mapᴸ (actᴾ π) as)
  actᴾ-⨁ π []       = actᴾ-𝟘 π
  actᴾ-⨁ π (a ∷ as) = ≤-trans (actᴾ-⊕ π a (⨁ as)) (⊕-mono ≤-refl (actᴾ-⨁ π as))

  swapsᴹ : Perm → Mode → Mode
  swapsᴹ = along swapᴹ

------------------------------------------------------------------------
-- The product

module Product (M N : Matrix) where

  F : List Name
  F = modes M ++ modes N

  names : Mode → List Name
  names stuck   = []
  names ⌜ n ⌝ = n ∷ []

  -- the named modes, `x` and `y`, which the permutations of the orbit
  -- of the modes not named fix
  around : Mode → Mode → List Name
  around x y = names x ++ names y ++ F

  fresh-for : Mode → Mode → Name
  fresh-for x y = fresh (around x y)

  candidates : Mode → Mode → List Mode
  candidates x y = stuck ∷ x ∷ y ∷ ⌜ fresh-for x y ⌝ ∷ mapᴸ ⌜_⌝ F

  term : Mode → Mode → Mode → Carrier
  term x y q = entry M x q ⊗ entry N q y

  terms : Mode → Mode → List Carrier
  terms x y = mapᴸ (term x y) (candidates x y)

  joined : Mode → Mode → Carrier
  joined x y = ⨁ (terms x y)

  prod : Mode → Mode → Carrier
  prod x y = ⟨ joined x y ⟩ around x y

  private
    ∉M : ∀ {n} → n ∉ F → n ∉ modes M
    ∉M n∉ n∈ = n∉ (∈-++⁺ˡ n∈)

    ∉N : ∀ {n} → n ∉ F → n ∉ modes N
    ∉N n∉ n∈ = n∉ (∈-++⁺ʳ (modes M) n∈)

    ∉F : ∀ {n x y} → n ∉ around x y → n ∉ F
    ∉F {x = x} {y} n∉ n∈ = n∉ (∈-++⁺ʳ (names x) (∈-++⁺ʳ (names y) n∈))

    fresh-≢ˡ : ∀ x y → ¬ x ≡ ⌜ fresh-for x y ⌝
    fresh-≢ˡ ⌜ n ⌝ y e = fresh-∉ _ (here (sym (⌜⌝-injective e)))

    fresh-≢ʳ : ∀ x y → ¬ y ≡ ⌜ fresh-for x y ⌝
    fresh-≢ʳ x ⌜ n ⌝ e = fresh-∉ _ (∈-++⁺ʳ (names x) (here (sym (⌜⌝-injective e))))

    named-mode : ∀ x {n} → n ∈ names x → ⌜ n ⌝ ≡ x
    named-mode ⌜ m ⌝ (here refl) = refl

    swap-fixᴹ : ∀ {a b x} → ¬ x ≡ ⌜ a ⌝ → ¬ x ≡ ⌜ b ⌝ → swapᴹ a b x ≡ x
    swap-fixᴹ {x = stuck}   _  _  = refl
    swap-fixᴹ {x = ⌜ n ⌝} na nb = cong ⌜_⌝ (swap-fix (λ e → na (cong ⌜_⌝ e)) (λ e → nb (cong ⌜_⌝ e)))

    -- a mode whose name is in a set is fixed by the swaps of names
    -- outside it
    fixed : ∀ {a b} x {A} → (∀ {n} → n ∈ names x → n ∈ A) → a ∉ A → b ∉ A → swapᴹ a b x ≡ x
    fixed stuck   sub a∉ b∉ = refl
    fixed ⌜ n ⌝ sub a∉ b∉ =
      swap-fixᴹ (λ e → a∉ (subst (_∈ _) (⌜⌝-injective e) (sub (here refl))))
                (λ e → b∉ (subst (_∈ _) (⌜⌝-injective e) (sub (here refl))))

  -- a swap of modes not named acts on the terms through the modes

  term-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ x y q
            → act a b (term x y q) ≈ term (swapᴹ a b x) (swapᴹ a b y) (swapᴹ a b q)
  term-swap {a} {b} a∉ b∉ x y q =
    ≈-trans (act-⊗ a b _ _)
      (⊗-cong (≈-sym (entry-equivariant-⊆ M ∈-++⁺ˡ a∉ b∉ x q))
              (≈-sym (entry-equivariant-⊆ N (∈-++⁺ʳ (modes M)) a∉ b∉ q y)))

  -- and the permutations fixing `around x y` keep `x` and `y`

  term-perm : ∀ x y π → Fixes (around x y) π → ∀ q
            → actᴾ π (term x y q) ≈ term x y (swapsᴹ π q)
  term-perm x y []                    []               q = ≈-refl
  term-perm x y ((a , b) ∷ π) ((a∉ , b∉) ∷ fix) q =
    ≈-trans (act-cong (term-perm x y π fix q))
      (subst₂ (λ x' y' → act a b (term x y (swapsᴹ π q)) ≈ term x' y' (swapᴹ a b (swapsᴹ π q)))
              (fixed x ∈-++⁺ˡ a∉ b∉) (fixed y (λ n∈ → ∈-++⁺ʳ (names x) (∈-++⁺ˡ n∈)) a∉ b∉)
              (term-swap (∉F {x = x} {y} a∉) (∉F {x = x} {y} b∉) x y (swapsᴹ π q)))

  joined-ub : ∀ x y {q} → q ∈ candidates x y → term x y q ≤ joined x y
  joined-ub x y q∈ = ⨁-ub (mapᴸ (term x y) (candidates x y)) (∈-map⁺ (term x y) q∈)

  prod-ub : ∀ x y q → term x y q ≤ prod x y
  prod-ub x y q = ub q
    where
      ub-generic : ∀ n → n ∉ F → ¬ ⌜ n ⌝ ≡ x → ¬ ⌜ n ⌝ ≡ y → term x y ⌜ n ⌝ ≤ prod x y
      ub-generic n n∉ nx ny =
        ≤-trans (≤-reflexive (cong (term x y) (sym (cong ⌜_⌝ (swap-b n f)))))
          (≤-trans (≤-reflexive (cong₂ (λ x' y' → term x' y' (swapᴹ n f ⌜ f ⌝)) (sym fx) (sym fy)))
            (≤-trans (proj₂ (term-swap n∉ f∉F x y ⌜ f ⌝))
              (≤-trans (act-mono (joined-ub x y (there (there (there (here refl))))))
                       (orbit-ub ((n , f) ∷ []) ((n∉A , f∉A) ∷ [])))))
        where
          f = fresh-for x y
          f∉A : f ∉ around x y
          f∉A = fresh-∉ _
          f∉F : f ∉ F
          f∉F = ∉F {x = x} {y} f∉A
          fx : swapᴹ n f x ≡ x
          fx = swap-fixᴹ (λ e → nx (sym e)) (fresh-≢ˡ x y)
          fy : swapᴹ n f y ≡ y
          fy = swap-fixᴹ (λ e → ny (sym e)) (fresh-≢ʳ x y)
          n∉A : n ∉ around x y
          n∉A n∈ with ∈-++⁻ (names x) n∈
          ... | inj₁ n∈x = nx (named-mode x n∈x)
          ... | inj₂ n∈' with ∈-++⁻ (names y) n∈'
          ...   | inj₁ n∈y = ny (named-mode y n∈y)
          ...   | inj₂ n∈F = n∉ n∈F
      ub : ∀ q → term x y q ≤ prod x y
      ub stuck = ≤-trans (joined-ub x y (here refl)) (⟨⟩-ub (joined x y))
      ub ⌜ n ⌝ with ⌜ n ⌝ ≟ᴹ x | ⌜ n ⌝ ≟ᴹ y | n ∈? F
      ... | yes refl | _ | _ = ≤-trans (joined-ub x y (there (here refl))) (⟨⟩-ub (joined x y))
      ... | no _ | yes refl | _ = ≤-trans (joined-ub x y (there (there (here refl)))) (⟨⟩-ub (joined x y))
      ... | no _ | no _ | yes n∈ =
        ≤-trans (joined-ub x y (there (there (there (there (∈-map⁺ ⌜_⌝ n∈)))))) (⟨⟩-ub (joined x y))
      ... | no nx | no ny | no n∉ = ub-generic n n∉ nx ny

  -- the joined terms, permuted, are terms

  private
    perm-joined : ∀ x y π → Fixes (around x y) π → ∀ {a}
                → a ∈ mapᴸ (actᴾ π) (mapᴸ (term x y) (candidates x y))
                → ∃ λ q → a ≈ term x y q
    perm-joined x y π fix a∈ with ∈-map⁻ (actᴾ π) a∈
    ... | b , b∈ , refl with ∈-map⁻ (term x y) b∈
    ...   | q , _ , refl = swapsᴹ π q , term-perm x y π fix q

  prod-lub : ∀ x y {t} → (∀ q → term x y q ≤ t) → prod x y ≤ t
  prod-lub x y f = orbit-lub λ π fix →
    ≤-trans (actᴾ-⨁ π (terms x y))
      (⨁-lub (mapᴸ (actᴾ π) (terms x y)) λ a∈ → let (q , e) = perm-joined x y π fix a∈ in ≤-trans (proj₁ e) (f q))

  prod-lub-⊗ʳ : ∀ x y {c t} → (∀ q → term x y q ⊗ c ≤ t) → prod x y ⊗ c ≤ t
  prod-lub-⊗ʳ x y f = orbit-⊗ʳ λ π fix →
    ≤-trans (⊗-mono (actᴾ-⨁ π (terms x y)) ≤-refl)
      (⨁-lub-⊗ʳ (mapᴸ (actᴾ π) (terms x y)) λ a∈ → let (q , e) = perm-joined x y π fix a∈ in
                          ≤-trans (⊗-mono (proj₁ e) ≤-refl) (f q))

  prod-lub-⊗ˡ : ∀ x y {c t} → (∀ q → c ⊗ term x y q ≤ t) → c ⊗ prod x y ≤ t
  prod-lub-⊗ˡ x y f = orbit-⊗ˡ λ π fix →
    ≤-trans (⊗-mono ≤-refl (actᴾ-⨁ π (terms x y)))
      (⨁-lub-⊗ˡ (mapᴸ (actᴾ π) (terms x y)) λ a∈ → let (q , e) = perm-joined x y π fix a∈ in
                          ≤-trans (⊗-mono ≤-refl (proj₁ e)) (f q))

  -- the product is equivariant

  private
    prod-swap-≤ : ∀ {a b} → a ∉ F → b ∉ F → ∀ x y
                → prod (swapᴹ a b x) (swapᴹ a b y) ≤ act a b (prod x y)
    prod-swap-≤ {a} {b} a∉ b∉ x y = prod-lub (swapᴹ a b x) (swapᴹ a b y) λ q →
      ≤-trans (≤-reflexive (cong (term (swapᴹ a b x) (swapᴹ a b y)) (sym (swapᴹ-inv a b q))))
        (≤-trans (proj₂ (term-swap a∉ b∉ x y (swapᴹ a b q)))
                 (act-mono (prod-ub x y (swapᴹ a b q))))

  prod-equivariant : Equivariantᶠ F prod
  prod-equivariant {a} {b} a∉ b∉ x y =
      prod-swap-≤ a∉ b∉ x y
    , ≤-trans (act-mono (≤-trans (≤-reflexive (cong₂ prod (sym (swapᴹ-inv a b x)) (sym (swapᴹ-inv a b y))))
                                 (prod-swap-≤ a∉ b∉ (swapᴹ a b x) (swapᴹ a b y))))
              (proj₁ (act-inv a b _))

_⊗ᴹ_ : Matrix → Matrix → Matrix
modes (M ⊗ᴹ N) = Product.F M N
row (M ⊗ᴹ N) p y = Product.prod M N ⌜ p ⌝ y
equivariant (M ⊗ᴹ N) a∉ b∉ p y = Product.prod-equivariant M N a∉ b∉ ⌜ p ⌝ y

-- the entries of a product are the least upper bounds of the terms

⊗ᴹ-ub : ∀ M N x y q → entry M x q ⊗ entry N q y ≤ entry (M ⊗ᴹ N) x y
⊗ᴹ-ub M N ⌜ p ⌝ y     q       = Product.prod-ub M N ⌜ p ⌝ y q
⊗ᴹ-ub M N stuck stuck   stuck   = proj₁ (⊗-identityˡ 𝟙)
⊗ᴹ-ub M N stuck ⌜ _ ⌝ stuck   = proj₁ (⊗-identityˡ 𝟘)
⊗ᴹ-ub M N stuck y       ⌜ _ ⌝ = ≤-trans (⊗-zeroˡ _) (𝟘-≤ _)

⊗ᴹ-lub : ∀ M N x y {t} → (∀ q → entry M x q ⊗ entry N q y ≤ t) → entry (M ⊗ᴹ N) x y ≤ t
⊗ᴹ-lub M N ⌜ p ⌝ y     f = Product.prod-lub M N ⌜ p ⌝ y f
⊗ᴹ-lub M N stuck stuck   f = ≤-trans (proj₂ (⊗-identityˡ 𝟙)) (f stuck)
⊗ᴹ-lub M N stuck ⌜ _ ⌝ f = 𝟘-≤ _

⊗ᴹ-lub-⊗ʳ : ∀ M N x y {c t} → (∀ q → (entry M x q ⊗ entry N q y) ⊗ c ≤ t)
          → entry (M ⊗ᴹ N) x y ⊗ c ≤ t
⊗ᴹ-lub-⊗ʳ M N ⌜ p ⌝ y     f = Product.prod-lub-⊗ʳ M N ⌜ p ⌝ y f
⊗ᴹ-lub-⊗ʳ M N stuck stuck   f = ≤-trans (⊗-mono (proj₂ (⊗-identityˡ 𝟙)) ≤-refl) (f stuck)
⊗ᴹ-lub-⊗ʳ M N stuck ⌜ _ ⌝ f = ≤-trans (⊗-zeroˡ _) (𝟘-≤ _)

⊗ᴹ-lub-⊗ˡ : ∀ M N x y {c t} → (∀ q → c ⊗ (entry M x q ⊗ entry N q y) ≤ t)
          → c ⊗ entry (M ⊗ᴹ N) x y ≤ t
⊗ᴹ-lub-⊗ˡ M N ⌜ p ⌝ y     f = Product.prod-lub-⊗ˡ M N ⌜ p ⌝ y f
⊗ᴹ-lub-⊗ˡ M N stuck stuck   f = ≤-trans (⊗-mono ≤-refl (proj₂ (⊗-identityˡ 𝟙))) (f stuck)
⊗ᴹ-lub-⊗ˡ M N stuck ⌜ _ ⌝ f = ≤-trans (⊗-zeroʳ _) (𝟘-≤ _)

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
