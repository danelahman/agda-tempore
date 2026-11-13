------------------------------------------------------------------------
-- Mode matrices over an equivariant dioid as a grade.                --
--                                                                    --
-- A grade is a matrix over the modes that is total, having an entry  --
-- other than `𝟘` from every mode, and whose entries between two      --
-- distinct ordinary modes are changes (`Change`), the entries a      --
-- change of mode may have; the row of `stuck` is that of the unit.   --
-- The product, the join and the order are those of the matrices, the --
-- unit is `Iᴹ`, and `⊤` is `⊤ᴹ`. These matrices are closed under the --
-- product and the join, and satisfy the unit-product law: if         --
-- `x · y ≾ 𝟏`, then `x` changes no mode and gets stuck from none,    --
-- for a change followed by a nonzero entry is not below `𝟙` and      --
-- `stuck` is never left, hence `x ≾ 𝟏` and `y ≾ 𝟏`. The dioid is to  --
-- have no zero divisors, `𝟙` not below `𝟘`, and products of nonzero  --
-- entries below `𝟙` only from factors below `𝟙`, the changes being   --
-- kept by the action and by orbit joins (`ModeEntries`). Delays are  --
-- a monoid morphism from the durations (`Delays`), the unit when     --
-- they keep the mode and spend nothing (`mode-grade`).               --
--                                                                    --
-- From a star on the entries, `Closures` builds for each grade a     --
-- candidate closure that satisfies every law of a closure but        --
-- iteration; where iteration, decided, holds too, it is the closure  --
-- (`plus?`). For a Kleene star over the trivial action, iteration    --
-- holds with enough powers (`Matrix.ModeClosure`), and so it does    --
-- for a dioid with coordinates in such a dioid                       --
-- (`Matrix.ModeCoordinates`). A dioid with closures has a star       --
-- (`stars-from`).                                                    --
------------------------------------------------------------------------

open import Grades.Indexed using (Names)
open import Grades.Matrix.Dioid using (Dioid)
open import Grades.Matrix.Nominal using (Equivariant)

module Grades.Matrix.ModeGrade (𝒩 : Names) (S : Dioid) (Eq : Equivariant 𝒩 S) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (_×-dec_; map′; True; toWitness)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any using (Any; any?)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Unit using () renaming (⊤ to ⊤′; tt to tt′)

open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)

open import Grades.Durations using (Duration)
open import Grades.Base using (Grade; Plus; plus)

open import Util.Equality

open Dioid S
open import Grades.Matrix.Modes 𝒩
open Equivariant Eq
open import Grades.Matrix.Matrices 𝒩 S Eq

------------------------------------------------------------------------
-- What the entries are to satisfy

record ModeEntries : Set₁ where
  field
    nontrivial       : ¬ (𝟙 ≤ 𝟘)
    no-zero-divisors : ∀ {a b} → a ⊗ b ≤ 𝟘 → (a ≤ 𝟘) ⊎ (b ≤ 𝟘)
    unit-reflects    : ∀ {a b} → a ⊗ b ≤ 𝟙 → ¬ (a ≤ 𝟘) → ¬ (b ≤ 𝟘) → (a ≤ 𝟙) × (b ≤ 𝟙)

    -- the entries a change of mode may have
    Change          : Carrier → Set
    change-𝟘        : ∀ {a} → a ≤ 𝟘 → Change a
    change-⊤        : Change ⊤
    change-≈        : ∀ {a b} → a ≈ b → Change a → Change b
    change-⊕        : ∀ {a b} → Change a → Change b → Change (a ⊕ b)
    change-⊗ˡ       : ∀ {a b} → Change a → Change (a ⊗ b)
    change-⊗ʳ       : ∀ {a b} → Change b → Change (a ⊗ b)
    -- a change followed by a nonzero entry is not below the unit
    change-not-unit : ∀ {a b} → Change a → ¬ (a ≤ 𝟘) → ¬ (b ≤ 𝟘) → ¬ (a ⊗ b ≤ 𝟙)
    -- kept by the action and by orbit joins
    change-act      : ∀ {a b x} → Change x → Change (act a b x)
    change-orbit    : ∀ {A x} → Change x → Change (⟨ x ⟩ A)

------------------------------------------------------------------------
-- A star on the entries, for closures (`Closures`): above the unit,
-- below the unit joined with any element above its argument and closed
-- under the product, with the two induction laws, and kept by the
-- equivalence and the action

record Stars : Set where
  field
    star       : Carrier → Carrier
    star-unit  : ∀ a → 𝟙 ≤ star a
    star-least : ∀ {a v} → a ≤ v → v ⊗ v ≤ v → star a ≤ 𝟙 ⊕ v
    star-indˡ  : ∀ {a d} → a ⊗ d ≤ d → star a ⊗ d ≤ d
    star-indʳ  : ∀ {a d} → d ⊗ a ≤ d → d ⊗ star a ≤ d
    star-cong  : ∀ {a b} → a ≈ b → star a ≈ star b
    star-act   : ∀ p q a → act p q (star a) ≈ star (act p q a)

-- the star of a dioid with closures: the unit joined with the closure

stars-from : ((a : Carrier) → Plus _⊗_ _≤_ a) → Stars
stars-from pl = record
  { star       = star
  ; star-unit  = λ a → ⊕-ubˡ 𝟙 (⁺ a)
  ; star-least = λ {a} h hv → ⊕-mono ≤-refl (Plus.c⁺-least (pl a) h hv)
  ; star-indˡ  = λ {a} {d} h →
      ≤-trans (⊗-distribʳ d 𝟙 (⁺ a)) (⊕-lub (proj₁ (⊗-identityˡ d)) (Plus.⁺-indˡ (pl a) h))
  ; star-indʳ  = λ {a} {d} h →
      ≤-trans (⊗-distribˡ d 𝟙 (⁺ a)) (⊕-lub (proj₁ (⊗-identityʳ d)) (Plus.⁺-indʳ (pl a) h))
  ; star-cong  = λ (p , q) → ⊕-mono ≤-refl (⁺-mono p) , ⊕-mono ≤-refl (⁺-mono q)
  ; star-act   = λ p q a →
        ≤-trans (proj₁ (act-⊕ p q 𝟙 (⁺ a)))
          (⊕-mono (proj₁ (act-𝟙 p q)) (act-⁺ p q a))
      , ≤-trans (⊕-mono (proj₂ (act-𝟙 p q)) (⁺-act p q a))
          (proj₂ (act-⊕ p q 𝟙 (⁺ a)))
  }
  where
    ⁺ : Carrier → Carrier
    ⁺ a = Plus.c⁺ (pl a)

    star : Carrier → Carrier
    star a = 𝟙 ⊕ ⁺ a

    ⁺-mono : ∀ {a b} → a ≤ b → ⁺ a ≤ ⁺ b
    ⁺-mono {a} {b} p = Plus.c⁺-least (pl a) (≤-trans p (Plus.≾-c⁺ (pl b))) (Plus.c⁺-iter (pl b))

    -- the action of the closure is the closure of the action
    ⁺-act : ∀ p q a → ⁺ (act p q a) ≤ act p q (⁺ a)
    ⁺-act p q a =
      Plus.c⁺-least (pl (act p q a)) (act-mono (Plus.≾-c⁺ (pl a)))
        (≤-trans (proj₂ (act-⊗ p q (⁺ a) (⁺ a))) (act-mono (Plus.c⁺-iter (pl a))))

    act-⁺ : ∀ p q a → act p q (⁺ a) ≤ ⁺ (act p q a)
    act-⁺ p q a =
      ≤-trans (act-mono {p} {q} least) (proj₁ (act-inv p q (⁺ (act p q a))))
      where
        w = act p q (⁺ (act p q a))
        least : ⁺ a ≤ w
        least = Plus.c⁺-least (pl a)
          (≤-trans (proj₂ (act-inv p q a)) (act-mono (Plus.≾-c⁺ (pl (act p q a)))))
          (≤-trans (proj₂ (act-⊗ p q (⁺ (act p q a)) (⁺ (act p q a))))
                   (act-mono (Plus.c⁺-iter (pl (act p q a)))))

------------------------------------------------------------------------
-- The diagonal matrix of the stars of the diagonal entries of a matrix

module StarMatrices (St : Stars) where

  open Stars St

  private
    swapᴹ-inj : ∀ {a b x y} → swapᴹ a b x ≡ swapᴹ a b y → x ≡ y
    swapᴹ-inj {a} {b} {x} {y} eq =
      trans (sym (swapᴹ-inv a b x)) (trans (cong (swapᴹ a b) eq) (swapᴹ-inv a b y))

    -- the entry of the diagonal matrix of stars
    ds : Matrix → (p : Name) (y : Mode) → Dec (y ≡ ⌜ p ⌝) → Carrier
    ds M p y (yes _) = star (row M p ⌜ p ⌝)
    ds M p y (no _)  = 𝟘

    ds-swap : ∀ M {a b} → a ∉ modes M → b ∉ modes M → ∀ p y
            → (d : Dec (swapᴹ a b y ≡ ⌜ swap a b p ⌝)) (d' : Dec (y ≡ ⌜ p ⌝))
            → ds M (swap a b p) (swapᴹ a b y) d ≈ act a b (ds M p y d')
    ds-swap M {a} {b} a∉ b∉ p y (yes _) (yes _) =
      ≈-trans (star-cong (equivariant M a∉ b∉ p ⌜ p ⌝)) (≈-sym (star-act a b _))
    ds-swap M {a} {b} a∉ b∉ p y (yes e) (no ne) = ⊥-elim (ne (swapᴹ-inj e))
    ds-swap M {a} {b} a∉ b∉ p y (no ne) (yes e) = ⊥-elim (ne (cong (swapᴹ a b) e))
    ds-swap M {a} {b} a∉ b∉ p y (no _)  (no _)  = ≈-sym (act-𝟘 a b)

  -- the diagonal matrix of the stars of the diagonal entries

  starsᴹ : Matrix → Matrix
  modes (starsᴹ M) = modes M
  row (starsᴹ M) p y = ds M p y (y ≟ᴹ ⌜ p ⌝)
  equivariant (starsᴹ M) a∉ b∉ p y =
    ds-swap M a∉ b∉ p y (_ ≟ᴹ _) (y ≟ᴹ ⌜ p ⌝)

  stars-diag : ∀ M p → entry (starsᴹ M) ⌜ p ⌝ ⌜ p ⌝ ≡ star (row M p ⌜ p ⌝)
  stars-diag M p with ⌜ p ⌝ ≟ᴹ ⌜ p ⌝
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  stars-off : ∀ M p {y} → ¬ y ≡ ⌜ p ⌝ → entry (starsᴹ M) ⌜ p ⌝ y ≡ 𝟘
  stars-off M p {y} ne with y ≟ᴹ ⌜ p ⌝
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

module _ (E : ModeEntries) where

  open ModeEntries E

  record ModeMatrix : Set where
    no-eta-equality
    constructor mode-matrix
    field
      mat     : Matrix
      total   : ∀ n → ∃ λ y → ¬ (entry mat ⌜ n ⌝ y ≤ 𝟘)
      changes : ∀ {p q} → ¬ p ≡ q → Change (entry mat ⌜ p ⌝ ⌜ q ⌝)

  open ModeMatrix public

  private
    e : ModeMatrix → Mode → Mode → Carrier
    e x = entry (mat x)

    total′ : ∀ x z → ∃ λ y → ¬ (e x z y ≤ 𝟘)
    total′ x stuck   = stuck , nontrivial
    total′ x ⌜ n ⌝ = total x n

    𝟙≰𝟘 = nontrivial

    ⊤≰𝟘 : ¬ (⊤ ≤ 𝟘)
    ⊤≰𝟘 p = nontrivial (≤-trans (≤-⊤ 𝟙) p)

    -- a nonzero entry below another
    nonzero-≤ : ∀ {a b} → a ≤ b → ¬ (a ≤ 𝟘) → ¬ (b ≤ 𝟘)
    nonzero-≤ p a≰ b≤ = a≰ (≤-trans p b≤)

    -- the product of two nonzero entries is nonzero
    nonzero-⊗ : ∀ {a b} → ¬ (a ≤ 𝟘) → ¬ (b ≤ 𝟘) → ¬ (a ⊗ b ≤ 𝟘)
    nonzero-⊗ a≰ b≰ ab with no-zero-divisors ab
    ... | inj₁ a≤ = a≰ a≤
    ... | inj₂ b≤ = b≰ b≤

    change-⨁ : ∀ as → (∀ {a} → a ∈ᴸ as → Change a) → Change (⨁ as)
    change-⨁ []       f = change-𝟘 ≤-refl
    change-⨁ (a ∷ as) f = change-⊕ (f (here refl)) (change-⨁ as (λ p → f (there p)))

  ----------------------------------------------------------------------
  -- The operations

  -- given by copatterns, unfolded only when a field is asked for

  𝟏ᵐ : ModeMatrix
  mat 𝟏ᵐ = Iᴹ
  total 𝟏ᵐ n = ⌜ n ⌝ , subst (λ c → ¬ (c ≤ 𝟘)) (sym (Iᴹ-diag ⌜ n ⌝)) 𝟙≰𝟘
  changes 𝟏ᵐ ne = change-𝟘 (≤-reflexive (Iᴹ-off (λ e → ne (⌜⌝-injective e))))

  ⊤ᵐ : ModeMatrix
  mat ⊤ᵐ = ⊤ᴹ
  total ⊤ᵐ n = stuck , subst (λ c → ¬ (c ≤ 𝟘)) (sym (⊤ᴹ-entry n stuck)) ⊤≰𝟘
  changes ⊤ᵐ {p} {q} _ = subst Change (sym (⊤ᴹ-entry p ⌜ q ⌝)) change-⊤

  infixl 7 _·ᵐ_
  infixl 6 _⊔ᵐ_

  _⊔ᵐ_ : ModeMatrix → ModeMatrix → ModeMatrix
  mat (x ⊔ᵐ y) = mat x ⊕ᴹ mat y
  total (x ⊔ᵐ y) n =
    proj₁ (total x n) , nonzero-≤ (⊕ᴹ-ubˡ (mat x) (mat y) ⌜ n ⌝ (proj₁ (total x n))) (proj₂ (total x n))
  changes (x ⊔ᵐ y) ne = change-⊕ (changes x ne) (changes y ne)

  private
    product-total : ∀ x y n → ∃ λ r → ¬ (entry (mat x ⊗ᴹ mat y) ⌜ n ⌝ r ≤ 𝟘)
    product-total x y n = tot n
      where
      tot : ∀ n → ∃ λ r → ¬ (entry (mat x ⊗ᴹ mat y) ⌜ n ⌝ r ≤ 𝟘)
      tot n with total x n
      ... | q , xq with total′ y q
      ...   | r , yr = r , nonzero-≤ (⊗ᴹ-ub (mat x) (mat y) ⌜ n ⌝ r q) (nonzero-⊗ xq yr)

    product-changes : ∀ x y {p r} → ¬ p ≡ r → Change (entry (mat x ⊗ᴹ mat y) ⌜ p ⌝ ⌜ r ⌝)
    product-changes x y {p} {r} ne = chg ne
      where
      chg : ∀ {p r} → ¬ p ≡ r → Change (entry (mat x ⊗ᴹ mat y) ⌜ p ⌝ ⌜ r ⌝)
      chg {p} {r} ne =
        change-orbit
          (change-⨁ (mapᴸ (P.term ⌜ p ⌝ ⌜ r ⌝) (P.candidates ⌜ p ⌝ ⌜ r ⌝))
            (λ a∈ → case (∈-map⁻ (P.term ⌜ p ⌝ ⌜ r ⌝) a∈)))
        where
          module P = Product (mat x) (mat y)
          term-change : ∀ q → Change (P.term ⌜ p ⌝ ⌜ r ⌝ q)
          term-change stuck = change-𝟘 (⊗-zeroʳ _)
          term-change ⌜ m ⌝ with p ≟ᴺ m
          ... | yes refl = change-⊗ʳ (changes y ne)
          ... | no pm    = change-⊗ˡ (changes x pm)
          case : ∀ {a} → (∃ λ q → q ∈ᴸ P.candidates ⌜ p ⌝ ⌜ r ⌝ × a ≡ P.term ⌜ p ⌝ ⌜ r ⌝ q) → Change a
          case (q , _ , refl) = term-change q

  _·ᵐ_ : ModeMatrix → ModeMatrix → ModeMatrix
  mat (x ·ᵐ y) = mat x ⊗ᴹ mat y
  total (x ·ᵐ y) = product-total x y
  changes (x ·ᵐ y) = product-changes x y

  ----------------------------------------------------------------------
  -- The order

  infix 4 _≾ᵐ_

  _≾ᵐ_ : ModeMatrix → ModeMatrix → Set
  x ≾ᵐ y = mat x ≤ᴹ mat y

  private
    pw : ∀ {M N} → M ≤ᵖ N → M ≤ᴹ N
    pw = pointwise⇒≤ᴹ

    at : ∀ {x y} → x ≾ᵐ y → mat x ≤ᵖ mat y
    at {x} {y} = ≤ᴹ⇒pointwise {mat x} {mat y}

    -- the rows of `stuck` agree
    stuck-row : ∀ M N y → entry M stuck y ≤ entry N stuck y
    stuck-row M N stuck   = ≤-refl
    stuck-row M N ⌜ _ ⌝ = ≤-refl

  ----------------------------------------------------------------------
  -- The unit-product law

  module _ (x y : ModeMatrix) (h : x ·ᵐ y ≾ᵐ 𝟏ᵐ) where

    private
      hp : ∀ a c → e x a stuck ⊗ e y stuck c ≤ entry Iᴹ a c
      hp a c = ≤-trans (⊗ᴹ-ub (mat x) (mat y) a c stuck) (at {x ·ᵐ y} {𝟏ᵐ} h a c)

      ht : ∀ a b c → e x a b ⊗ e y b c ≤ entry Iᴹ a c
      ht a b c = ≤-trans (⊗ᴹ-ub (mat x) (mat y) a c b) (at {x ·ᵐ y} {𝟏ᵐ} h a c)

      ≤off : ∀ a c {t} → ¬ a ≡ c → t ≤ entry Iᴹ a c → t ≤ 𝟘
      ≤off a c ne p = ≤-trans p (≤-reflexive (Iᴹ-off ne))

      ≤diag : ∀ a {t} → t ≤ entry Iᴹ a a → t ≤ 𝟙
      ≤diag a p = ≤-trans p (≤-reflexive (Iᴹ-diag a))

    private
      -- a change of `x` followed by a nonzero entry of `y` is not below
      -- the unit, and `y` does not leave `stuck`
      refute : ∀ p b → ¬ b ≡ ⌜ p ⌝ → ¬ (e x ⌜ p ⌝ b ≤ 𝟘) → ¬ (e y b ⌜ p ⌝ ≤ 𝟘)
             → ¬ (e x ⌜ p ⌝ b ⊗ e y b ⌜ p ⌝ ≤ 𝟙)
      refute p stuck   _  _  yr _ = yr ≤-refl
      refute p ⌜ m ⌝ b≢ x≰ yr = change-not-unit (changes x (λ e → b≢ (cong ⌜_⌝ (sym e)))) x≰ yr

    zero-productˡ′ : mat x ≤ᵖ mat 𝟏ᵐ
    zero-productˡ′ stuck b = stuck-row (mat x) Iᴹ b
    zero-productˡ′ ⌜ p ⌝ b with b ≟ᴹ ⌜ p ⌝
    ... | yes refl with e x ⌜ p ⌝ ⌜ p ⌝ ≤? 𝟘
    ...   | yes x≤ = ≤-trans x≤ (𝟘-≤ _)
    ...   | no x≰ with total′ y ⌜ p ⌝
    ...     | r , yr with r ≟ᴹ ⌜ p ⌝
    ...       | yes refl =
      ≤-trans (proj₁ (unit-reflects (≤diag ⌜ p ⌝ (ht ⌜ p ⌝ ⌜ p ⌝ ⌜ p ⌝)) x≰ yr))
              (≤-reflexive (sym (Iᴹ-diag ⌜ p ⌝)))
    ...       | no ne = ⊥-elim (nonzero-⊗ x≰ yr (≤off ⌜ p ⌝ r (λ e → ne (sym e)) (ht ⌜ p ⌝ ⌜ p ⌝ r)))
    zero-productˡ′ ⌜ p ⌝ b | no b≢ with e x ⌜ p ⌝ b ≤? 𝟘
    ...   | yes x≤ = ≤-trans x≤ (𝟘-≤ _)
    ...   | no x≰ with total′ y b
    ...     | r , yr with r ≟ᴹ ⌜ p ⌝
    ...       | no ne = ⊥-elim (nonzero-⊗ x≰ yr (≤off ⌜ p ⌝ r (λ e → ne (sym e)) (ht ⌜ p ⌝ b r)))
    ...       | yes refl = ⊥-elim (refute p b b≢ x≰ yr (≤diag ⌜ p ⌝ (ht ⌜ p ⌝ b ⌜ p ⌝)))

    zero-productʳ′ : mat y ≤ᵖ mat 𝟏ᵐ
    zero-productʳ′ stuck c = stuck-row (mat y) Iᴹ c
    zero-productʳ′ ⌜ q ⌝ c with total x q
    ... | s , xs with s ≟ᴹ ⌜ q ⌝
    ...   | no ne = ⊥-elim (xs (≤off ⌜ q ⌝ s (λ e → ne (sym e)) (zero-productˡ′ ⌜ q ⌝ s)))
    ...   | yes refl with c ≟ᴹ ⌜ q ⌝
    ...     | yes refl with e y ⌜ q ⌝ ⌜ q ⌝ ≤? 𝟘
    ...       | yes y≤ = ≤-trans y≤ (𝟘-≤ _)
    ...       | no y≰ =
      ≤-trans (proj₂ (unit-reflects (≤diag ⌜ q ⌝ (ht ⌜ q ⌝ ⌜ q ⌝ ⌜ q ⌝)) xs y≰))
              (≤-reflexive (sym (Iᴹ-diag ⌜ q ⌝)))
    zero-productʳ′ ⌜ q ⌝ c | s , xs | yes refl | no c≢ with no-zero-divisors (≤off ⌜ q ⌝ c (λ e → c≢ (sym e)) (ht ⌜ q ⌝ ⌜ q ⌝ c))
    ... | inj₁ x≤ = ⊥-elim (xs x≤)
    ... | inj₂ y≤ = ≤-trans y≤ (𝟘-≤ _)

  ----------------------------------------------------------------------
  -- The grade

  -- with delays given by a monoid morphism from the durations

  record Delays (D : Duration) : Set where
    private module D = Duration D
    field
      delay      : D.Carrier → ModeMatrix
      delay-zero : (delay D.0ᴰ ≾ᵐ 𝟏ᵐ) × (𝟏ᵐ ≾ᵐ delay D.0ᴰ)
      delay-plus : ∀ τ τ' → (delay (τ D.+ᴰ τ') ≾ᵐ delay τ ·ᵐ delay τ')
                          × (delay τ ·ᵐ delay τ' ≾ᵐ delay (τ D.+ᴰ τ'))

  -- delays keeping the mode at the unit

  unit-delays : ∀ {D} → Delays D
  unit-delays = record
    { delay      = λ _ → 𝟏ᵐ
    ; delay-zero = pw (λ _ _ → ≤-refl) , pw (λ _ _ → ≤-refl)
    ; delay-plus = λ _ _ → pw (⊗ᴹ-identityˡ⁻ Iᴹ) , pw (⊗ᴹ-identityˡ Iᴹ)
    }

  mode-grade-with : {D : Duration} → Delays D → Grade D
  mode-grade-with Δ = record
    { Carrier         = ModeMatrix
    ; _·_             = _·ᵐ_
    ; 𝟏               = 𝟏ᵐ
    ; _≾_             = _≾ᵐ_
    ; ⊤               = ⊤ᵐ
    ; _⊔_             = _⊔ᵐ_
    ; ι               = Delays.delay Δ
    ; ·-identityˡ     = λ x → pw (⊗ᴹ-identityˡ (mat x)) , pw (⊗ᴹ-identityˡ⁻ (mat x))
    ; ·-identityʳ     = λ x → pw (⊗ᴹ-identityʳ (mat x)) , pw (⊗ᴹ-identityʳ⁻ (mat x))
    ; ·-assoc         = λ x y z → pw (⊗ᴹ-assoc (mat x) (mat y) (mat z))
                                , pw (⊗ᴹ-assoc⁻ (mat x) (mat y) (mat z))
    ; ≾-refl          = pw (λ _ _ → ≤-refl)
    ; ≾-trans         = λ {x} {y} {z} p q → pw (λ a b → ≤-trans (at {x} {y} p a b) (at {y} {z} q a b))
    ; ≾-irrelevant    = ≤ᴹ-irrelevant
    ; _≾?_            = λ x y → mat x ≤ᴹ? mat y
    ; ≾-⊤             = λ x → pw (λ { stuck b → stuck-row (mat x) ⊤ᴹ b
                                    ; ⌜ p ⌝ b → ≤-trans (≤-⊤ _) (≤-reflexive (sym (⊤ᴹ-entry p b))) })
    ; ⊔-ubˡ           = λ x y → pw (⊕ᴹ-ubˡ (mat x) (mat y))
    ; ⊔-ubʳ           = λ x y → pw (⊕ᴹ-ubʳ (mat x) (mat y))
    ; ⊔-lub           = λ {x} {y} {z} p q → pw (⊕ᴹ-lub {mat x} {mat y} {mat z} (at {x} {z} p) (at {y} {z} q))
    ; ·-monoˡ-≾       = λ {z} {x} {y} p → pw (⊗ᴹ-mono {mat x} {mat y} {mat z} {mat z} (at {x} {y} p) (λ _ _ → ≤-refl))
    ; ·-monoʳ-≾       = λ {z} {x} {y} p → pw (⊗ᴹ-mono {mat z} {mat z} {mat x} {mat y} (λ _ _ → ≤-refl) (at {x} {y} p))
    ; ·-distribˡ-⊔-≾  = λ x y z → pw (⊗ᴹ-distribˡ (mat x) (mat y) (mat z))
    ; ·-distribʳ-⊔-≾  = λ x y z → pw (⊗ᴹ-distribʳ (mat x) (mat y) (mat z))
    ; ≾-zero-productˡ = λ {x} {y} h → pw (zero-productˡ′ x y h)
    ; ≾-zero-productʳ = λ {x} {y} h → pw (zero-productʳ′ x y h)
    ; ι-zero          = Delays.delay-zero Δ
    ; ι-plus          = λ {τ} {τ'} → Delays.delay-plus Δ τ τ'
    }

  ----------------------------------------------------------------------
  -- Matrices whose conditions are decided at the representatives

  module Decided (change? : ∀ a → Dec (Change a)) where

    private
      module R (M : Matrix) = Representatives (modes M)

      rowModes : Matrix → Mode → List Mode
      rowModes M x = stuck ∷ ⌜ R.o M ⌝ ∷ mapᴸ ⌜_⌝ (modes M)

      NonzeroIn : Matrix → Mode → Set
      NonzeroIn M x = Any (λ y → ¬ (entry M x y ≤ 𝟘)) (rowModes M x)

      nonzero? : ∀ M x → Dec (NonzeroIn M x)
      nonzero? M x = any? (λ y → ¬? (entry M x y ≤? 𝟘)) (rowModes M x)

    -- totality at the representatives: each named mode and a fresh one

    Total : Matrix → Set
    Total M = All (λ p → NonzeroIn M ⌜ p ⌝) (modes M) × NonzeroIn M ⌜ R.o M ⌝

    total? : ∀ M → Dec (Total M)
    total? M = all? (λ p → nonzero? M ⌜ p ⌝) (modes M) ×-dec nonzero? M ⌜ R.o M ⌝

    -- the changes at the representatives

    ChangeAt : Matrix → Mode → Mode → Set
    ChangeAt M ⌜ p ⌝ ⌜ q ⌝ = ¬ p ≡ q → Change (entry M ⌜ p ⌝ ⌜ q ⌝)
    ChangeAt M _       _       = ⊤′

    changeAt? : ∀ M x y → Dec (ChangeAt M x y)
    changeAt? M ⌜ p ⌝ ⌜ q ⌝ with p ≟ᴺ q
    ... | yes refl = yes (λ ne → ⊥-elim (ne refl))
    ... | no pq with change? (entry M ⌜ p ⌝ ⌜ q ⌝)
    ...   | yes c = yes (λ _ → c)
    ...   | no ¬c = no (λ f → ¬c (f pq))
    changeAt? M stuck   _       = yes tt′
    changeAt? M ⌜ _ ⌝ stuck   = yes tt′

    Changes : Matrix → Set
    Changes M = AtRepresentatives (modes M) (ChangeAt M)

    changes? : ∀ M → Dec (Changes M)
    changes? M =
      map′ (λ (a , b , c , d , e , f , g) → at-reps a b c d e f g)
           (λ (at-reps a b c d e f g) → a , b , c , d , e , f , g)
           (all? (λ p → all? (λ q → changeAt? M ⌜ p ⌝ ⌜ q ⌝) F) F
            ×-dec all? (λ p → changeAt? M ⌜ p ⌝ ⌜ o ⌝) F
            ×-dec all? (λ q → changeAt? M ⌜ o ⌝ ⌜ q ⌝) F
            ×-dec changeAt? M ⌜ o ⌝ ⌜ o ⌝
            ×-dec changeAt? M ⌜ o ⌝ ⌜ o' ⌝
            ×-dec all? (λ p → changeAt? M ⌜ p ⌝ stuck) F
            ×-dec changeAt? M ⌜ o ⌝ stuck)
      where
        F = modes M
        open Representatives F

    private
      total-from : ∀ M → Total M → ∀ n → ∃ λ y → ¬ (entry M ⌜ n ⌝ y ≤ 𝟘)
      total-from M (named , other) n with n ∈? modes M
      ... | yes n∈ = witness ⌜ n ⌝ (All.lookup named n∈)
        where
          witness : ∀ x → Any (λ y → ¬ (entry M x y ≤ 𝟘)) (rowModes M x) → ∃ λ y → ¬ (entry M x y ≤ 𝟘)
          witness x a = let (y , _ , h) = find a in y , h
      ... | no n∉ with find other
      ...   | y , _ , h =
        swapᴹ o n y ,
        (λ z → h (act-≤𝟘⁻ (≤-trans (proj₂ (equivariant M o∉ n∉ o y))
                                   (≤-trans (≤-reflexive (cong (λ m → row M m (swapᴹ o n y)) (swap-a o n))) z))))
        where open Representatives (modes M)

      changes-from : ∀ M → Changes M → ∀ {p q} → ¬ p ≡ q → Change (entry M ⌜ p ⌝ ⌜ q ⌝)
      changes-from M (at-reps yy yo oy oo oo' ys os) {p} {q} =
        via-representatives (ChangeAt M)
          (λ {a} {b} {x} {y} a∉ b∉ c → closed a∉ b∉ x y c)
          (λ p∈ q∈ → All.lookup (All.lookup yy p∈) q∈)
          (All.lookup yo) (All.lookup oy) oo oo' (All.lookup ys) os
          p ⌜ q ⌝
        where
          open Representatives (modes M)
          closed : ∀ {a b} → a ∉ modes M → b ∉ modes M → ∀ x y
                 → ChangeAt M x y → ChangeAt M (swapᴹ a b x) (swapᴹ a b y)
          closed a∉ b∉ ⌜ p' ⌝ ⌜ q' ⌝ c ne =
            change-≈ (≈-sym (equivariant M a∉ b∉ p' ⌜ q' ⌝)) (change-act (c (λ e → ne (cong (swap _ _) e))))
          closed a∉ b∉ stuck   y       c = tt′
          closed a∉ b∉ ⌜ _ ⌝ stuck   c = tt′

    -- a matrix with its conditions decided

    decided : (M : Matrix) {t : True (total? M)} {c : True (changes? M)} → ModeMatrix
    mat (decided M) = M
    total (decided M {t}) = total-from M (toWitness t)
    changes (decided M {c = c}) = changes-from M (toWitness c)

  mode-grade : {D : Duration} → Grade D
  mode-grade = mode-grade-with unit-delays

  ----------------------------------------------------------------------
  -- Closures from a star on the entries
  --
  -- For a grade `A`, `B = A ⊔ A · A ⊔ … ⊔ Aᵏ⁺¹` and `S` the diagonal
  -- matrix of the stars of the diagonal entries of `B`, the matrix
  --
  --   X  =  (𝟏 ⊔ B) · S · B
  --
  -- is above `A`, below every grade above `A` closed under the
  -- product, and satisfies both induction laws (`candidate-plus`).
  -- Where also `X · X ≾ X`, which is decided, `X` is the closure of
  -- `A` (`plus?`), taking `k` from the number of modes `A` names. For
  -- a Kleene star over the trivial action, `X · X ≾ X` holds with `k`
  -- four more than that number (`Matrix.ModeClosure`), and through
  -- coordinates in such a dioid with `k` larger by a bound on the
  -- names at a coordinate (`Matrix.ModeCoordinates`).

  module Closures (St : Stars) where

    open Stars St

    private
      infixr 4 _⟫_

      _⟫_ : ∀ {M N P} → M ≤ᵖ N → N ≤ᵖ P → M ≤ᵖ P
      (p ⟫ q) x y = ≤-trans (p x y) (q x y)

      ≤ᵖ-refl : ∀ {M} → M ≤ᵖ M
      ≤ᵖ-refl _ _ = ≤-refl

    open StarMatrices St public

    starsᵐ : ModeMatrix → ModeMatrix
    mat (starsᵐ x) = starsᴹ (mat x)
    total (starsᵐ x) n =
      ⌜ n ⌝ , λ le → 𝟙≰𝟘 (≤-trans (star-unit _)
                           (≤-trans (≤-reflexive (sym (stars-diag (mat x) n))) le))
    changes (starsᵐ x) {p} ne =
      change-𝟘 (≤-reflexive (stars-off (mat x) p (λ e → ne (sym (⌜⌝-injective e)))))

    ----------------------------------------------------------------------
    -- The laws of the stars, entrywise

    private
      -- the unit is below the stars
      I≤S : ∀ M → Iᴹ ≤ᵖ starsᴹ M
      I≤S M stuck   y = stuck-row Iᴹ (starsᴹ M) y
      I≤S M ⌜ p ⌝ y with y ≟ᴹ ⌜ p ⌝
      ... | yes refl =
        ≤-trans (≤-reflexive (Iᴹ-diag ⌜ p ⌝)) (star-unit _)
      ... | no ne =
        ≤-trans (≤-reflexive (Iᴹ-off (λ e → ne (sym e)))) (𝟘-≤ _)

      -- below the unit joined with any matrix above and closed
      S-least : ∀ {M V} → M ≤ᵖ V → V ⊗ᴹ V ≤ᵖ V → starsᴹ M ≤ᵖ Iᴹ ⊕ᴹ V
      S-least {M} {V} hM hV stuck   y = stuck-row (starsᴹ M) (Iᴹ ⊕ᴹ V) y
      S-least {M} {V} hM hV ⌜ p ⌝ y with y ≟ᴹ ⌜ p ⌝
      ... | yes refl =
        ≤-trans (star-least (hM ⌜ p ⌝ ⌜ p ⌝)
                  (≤-trans (⊗ᴹ-ub V V ⌜ p ⌝ ⌜ p ⌝ ⌜ p ⌝) (hV ⌜ p ⌝ ⌜ p ⌝)))
          (≤-trans (⊕-mono (≤-reflexive (sym (Iᴹ-diag ⌜ p ⌝))) ≤-refl)
                   (proj₂ (⊕ᴹ-entry Iᴹ V ⌜ p ⌝ ⌜ p ⌝)))
      ... | no ne = 𝟘-≤ _

      S-indˡ : ∀ {M D} → M ⊗ᴹ D ≤ᵖ D → starsᴹ M ⊗ᴹ D ≤ᵖ D
      S-indˡ {M} {D} h x y = ⊗ᴹ-lub (starsᴹ M) D x y (term x)
        where
          term : ∀ x q → entry (starsᴹ M) x q ⊗ entry D q y ≤ entry D x y
          term stuck stuck   = proj₁ (⊗-identityˡ _)
          term stuck ⌜ _ ⌝ = ≤-trans (⊗-zeroˡ _) (𝟘-≤ _)
          term ⌜ p ⌝ q with q ≟ᴹ ⌜ p ⌝
          ... | yes refl = star-indˡ (≤-trans (⊗ᴹ-ub M D ⌜ p ⌝ y ⌜ p ⌝) (h ⌜ p ⌝ y))
          ... | no _     = ≤-trans (⊗-zeroˡ _) (𝟘-≤ _)

      S-indʳ : ∀ {M D} → D ⊗ᴹ M ≤ᵖ D → D ⊗ᴹ starsᴹ M ≤ᵖ D
      S-indʳ {M} {D} h x y = ⊗ᴹ-lub D (starsᴹ M) x y (term y)
        where
          term : ∀ y q → entry D x q ⊗ entry (starsᴹ M) q y ≤ entry D x y
          term stuck   stuck = proj₁ (⊗-identityʳ _)
          term ⌜ _ ⌝ stuck = ≤-trans (⊗-zeroʳ _) (𝟘-≤ _)
          term y ⌜ m ⌝ with y ≟ᴹ ⌜ m ⌝
          ... | yes refl = star-indʳ (≤-trans (⊗ᴹ-ub D M x ⌜ m ⌝ ⌜ m ⌝) (h x ⌜ m ⌝))
          ... | no _     = ≤-trans (⊗-zeroʳ _) (𝟘-≤ _)

    ----------------------------------------------------------------------
    -- Joins of powers

    powers : ModeMatrix → ℕ → ModeMatrix
    powers A zero    = A
    powers A (suc k) = A ⊔ᵐ (A ·ᵐ powers A k)

    private
      A≤P : ∀ A k → mat A ≤ᵖ mat (powers A k)
      A≤P A zero    = ≤ᵖ-refl
      A≤P A (suc k) = ⊕ᴹ-ubˡ (mat A) _

      P-least : ∀ A k {V} → mat A ≤ᵖ V → V ⊗ᴹ V ≤ᵖ V → mat (powers A k) ≤ᵖ V
      P-least A zero    hA hV = hA
      P-least A (suc k) hA hV =
        ⊕ᴹ-lub {mat A} {mat A ⊗ᴹ mat (powers A k)} hA
          (⊗ᴹ-mono {mat A} {_} {mat (powers A k)} hA (P-least A k hA hV) ⟫ hV)

      P-indˡ : ∀ A k {D} → mat A ⊗ᴹ D ≤ᵖ D → mat (powers A k) ⊗ᴹ D ≤ᵖ D
      P-indˡ A zero    h = h
      P-indˡ A (suc k) {D} h =
        ⊗ᴹ-distribʳ D (mat A) (mat A ⊗ᴹ mat (powers A k))
        ⟫ ⊕ᴹ-lub {mat A ⊗ᴹ D} {(mat A ⊗ᴹ mat (powers A k)) ⊗ᴹ D} h
            (⊗ᴹ-assoc (mat A) (mat (powers A k)) D
             ⟫ ⊗ᴹ-mono {mat A} {mat A} {mat (powers A k) ⊗ᴹ D} {D}
                 ≤ᵖ-refl (P-indˡ A k h)
             ⟫ h)

      P-indʳ : ∀ A k {D} → D ⊗ᴹ mat A ≤ᵖ D → D ⊗ᴹ mat (powers A k) ≤ᵖ D
      P-indʳ A zero    h = h
      P-indʳ A (suc k) {D} h =
        ⊗ᴹ-distribˡ D (mat A) (mat A ⊗ᴹ mat (powers A k))
        ⟫ ⊕ᴹ-lub {D ⊗ᴹ mat A} {D ⊗ᴹ (mat A ⊗ᴹ mat (powers A k))} h
            (⊗ᴹ-assoc⁻ D (mat A) (mat (powers A k))
             ⟫ ⊗ᴹ-mono {D ⊗ᴹ mat A} {D} {mat (powers A k)} {mat (powers A k)}
                 h ≤ᵖ-refl
             ⟫ P-indʳ A k h)

    ----------------------------------------------------------------------
    -- The candidate

    candidate : ℕ → ModeMatrix → ModeMatrix
    candidate k A = ((𝟏ᵐ ⊔ᵐ powers A k) ·ᵐ starsᵐ (powers A k)) ·ᵐ powers A k

    private
      module _ (A : ModeMatrix) (k : ℕ) where

        Bᴬ = mat (powers A k)
        Sᴮ = starsᴹ Bᴬ
        Jᴮ = Iᴹ ⊕ᴹ Bᴬ

        A≤X : mat A ≤ᵖ mat (candidate k A)
        A≤X = A≤P A k
            ⟫ ⊗ᴹ-identityˡ⁻ Bᴬ
            ⟫ ⊗ᴹ-mono {Iᴹ} {Iᴹ ⊗ᴹ Iᴹ} {Bᴬ} {Bᴬ} (⊗ᴹ-identityˡ⁻ Iᴹ) ≤ᵖ-refl
            ⟫ ⊗ᴹ-mono {Iᴹ ⊗ᴹ Iᴹ} {Jᴮ ⊗ᴹ Sᴮ} {Bᴬ} {Bᴬ}
                (⊗ᴹ-mono {Iᴹ} {Jᴮ} {Iᴹ} {Sᴮ} (⊕ᴹ-ubˡ Iᴹ Bᴬ) (I≤S Bᴬ)) ≤ᵖ-refl

        X-least : ∀ {V} → mat A ≤ᵖ V → V ⊗ᴹ V ≤ᵖ V → mat (candidate k A) ≤ᵖ V
        X-least {V} hA hV =
            ⊗ᴹ-mono {Jᴮ ⊗ᴹ Sᴮ} {(Iᴹ ⊕ᴹ V) ⊗ᴹ (Iᴹ ⊕ᴹ V)} {Bᴬ} {V}
              (⊗ᴹ-mono {Jᴮ} {Iᴹ ⊕ᴹ V} {Sᴮ} {Iᴹ ⊕ᴹ V}
                 (⊕ᴹ-lub {Iᴹ} {Bᴬ} (⊕ᴹ-ubˡ Iᴹ V) (hB ⟫ ⊕ᴹ-ubʳ Iᴹ V))
                 (S-least hB hV))
              hB
          ⟫ ⊗ᴹ-assoc (Iᴹ ⊕ᴹ V) (Iᴹ ⊕ᴹ V) V
          ⟫ ⊗ᴹ-mono {Iᴹ ⊕ᴹ V} {Iᴹ ⊕ᴹ V} {(Iᴹ ⊕ᴹ V) ⊗ᴹ V} {V} ≤ᵖ-refl JV
          ⟫ JV
          where
            hB : Bᴬ ≤ᵖ V
            hB = P-least A k hA hV
            JV : (Iᴹ ⊕ᴹ V) ⊗ᴹ V ≤ᵖ V
            JV = ⊗ᴹ-distribʳ V Iᴹ V ⟫ ⊕ᴹ-lub {Iᴹ ⊗ᴹ V} {V ⊗ᴹ V} (⊗ᴹ-identityˡ V) hV

        X-indˡ : ∀ {D} → mat A ⊗ᴹ D ≤ᵖ D → mat (candidate k A) ⊗ᴹ D ≤ᵖ D
        X-indˡ {D} h =
            ⊗ᴹ-assoc (Jᴮ ⊗ᴹ Sᴮ) Bᴬ D
          ⟫ ⊗ᴹ-mono {Jᴮ ⊗ᴹ Sᴮ} {Jᴮ ⊗ᴹ Sᴮ} {Bᴬ ⊗ᴹ D} {D} ≤ᵖ-refl hB
          ⟫ ⊗ᴹ-assoc Jᴮ Sᴮ D
          ⟫ ⊗ᴹ-mono {Jᴮ} {Jᴮ} {Sᴮ ⊗ᴹ D} {D} ≤ᵖ-refl (S-indˡ hB)
          ⟫ ⊗ᴹ-distribʳ D Iᴹ Bᴬ
          ⟫ ⊕ᴹ-lub {Iᴹ ⊗ᴹ D} {Bᴬ ⊗ᴹ D} (⊗ᴹ-identityˡ D) hB
          where
            hB : Bᴬ ⊗ᴹ D ≤ᵖ D
            hB = P-indˡ A k h

        X-indʳ : ∀ {D} → D ⊗ᴹ mat A ≤ᵖ D → D ⊗ᴹ mat (candidate k A) ≤ᵖ D
        X-indʳ {D} h =
            ⊗ᴹ-assoc⁻ D (Jᴮ ⊗ᴹ Sᴮ) Bᴬ
          ⟫ ⊗ᴹ-mono {D ⊗ᴹ (Jᴮ ⊗ᴹ Sᴮ)} {D} {Bᴬ} {Bᴬ}
              (⊗ᴹ-assoc⁻ D Jᴮ Sᴮ
               ⟫ ⊗ᴹ-mono {D ⊗ᴹ Jᴮ} {D} {Sᴮ} {Sᴮ}
                   (⊗ᴹ-distribˡ D Iᴹ Bᴬ ⟫ ⊕ᴹ-lub {D ⊗ᴹ Iᴹ} {D ⊗ᴹ Bᴬ} (⊗ᴹ-identityʳ D) hB)
                   ≤ᵖ-refl
               ⟫ S-indʳ hB)
              ≤ᵖ-refl
          ⟫ hB
          where
            hB : D ⊗ᴹ Bᴬ ≤ᵖ D
            hB = P-indʳ A k h

    -- the right induction law of the candidate, entrywise

    candidate-indʳ : ∀ k A {D} → D ⊗ᴹ mat A ≤ᵖ D → D ⊗ᴹ mat (candidate k A) ≤ᵖ D
    candidate-indʳ k A = X-indʳ A k

    -- the candidate is the closure where it is closed under the product

    candidate-plus : ∀ k A → candidate k A ·ᵐ candidate k A ≾ᵐ candidate k A
                   → Plus _·ᵐ_ _≾ᵐ_ A
    candidate-plus k A it = plus (candidate k A) (pw (A≤X A k)) it
      (λ {v} hA hv → pw (X-least A k {mat v} (at {A} {v} hA) (at {v ·ᵐ v} {v} hv)))
      (λ {d} h → pw (X-indˡ A k {mat d} (at {A ·ᵐ d} {d} h)))
      (λ {d} h → pw (X-indʳ A k {mat d} (at {d ·ᵐ A} {d} h)))

    -- the closure, where the candidate is closed under the product,
    -- with powers up to the number of modes named and four more; the
    -- decision recomputes the entries of every power, and its cost by
    -- reduction is exponential in that number

    private
      plus-at : ∀ k A → Dec (candidate k A ·ᵐ candidate k A ≾ᵐ candidate k A)
              → Maybe (Plus _·ᵐ_ _≾ᵐ_ A)
      plus-at k A (yes it) = just (candidate-plus k A it)
      plus-at k A (no _)   = nothing

      decide : ∀ k A → Dec (candidate k A ·ᵐ candidate k A ≾ᵐ candidate k A)
      decide k A = mat (candidate k A ·ᵐ candidate k A) ≤ᴹ? mat (candidate k A)

    plus? : (A : ModeMatrix) → Maybe (Plus _·ᵐ_ _≾ᵐ_ A)
    plus? A = plus-at k A (decide k A)
      where k = suc (suc (suc (length (modes (mat A)))))

