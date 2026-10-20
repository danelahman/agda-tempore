------------------------------------------------------------------------
-- Mode matrices as a grade.                                          --
--                                                                    --
-- A grade is a matrix over the modes that is total, having an entry  --
-- other than `𝟘` from every mode, and whose entries between two      --
-- distinct ordinary modes are changes (`Change`), the entries a      --
-- change of mode may have; the row of `stuck` is that of the unit.   --
-- The product, the join and the order are those of the matrices, the --
-- unit is `Iᴹ`, and `⊤` is `⊤ᴹ`. These matrices are closed under the --
-- product and the join, and the unit is the only one below the unit: --
-- if `x · y ≾ u`, then `x` changes no mode and gets stuck from none, --
-- for a change followed by a nonzero entry is not below `𝟙` and      --
-- `stuck` is never left, hence `x ≾ u` and `y ≾ u`. Delays keep the  --
-- mode at the unit. The dioid is to have no zero divisors, `𝟙` above --
-- `𝟘`, and products of nonzero entries below `𝟙` only from factors   --
-- below `𝟙` (`ModeEntries`).                                         --
------------------------------------------------------------------------

open import Syntax.Grades.Indexed using (Names)
open import Syntax.Grades.Matrix.Dioid using (Dioid)

module Syntax.Grades.Matrix.ModeGrade (𝒩 : Names) (S : Dioid) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (_×-dec_; map′; True; toWitness)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any using (Any; any?)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Unit using () renaming (⊤ to ⊤′; tt to tt′)

open import Syntax.Durations using (Duration)
open import Syntax.Grades using (Grade)

open import Util.Equality

open Dioid S
open import Syntax.Grades.Matrix.Modes 𝒩
open import Syntax.Grades.Matrix.Matrices 𝒩 S

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

module _ (E : ModeEntries) where

  open ModeEntries E

  record ModeMatrix : Set where
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

  uᵐ : ModeMatrix
  uᵐ = mode-matrix Iᴹ
    (λ n → ⌜ n ⌝ , subst (λ c → ¬ (c ≤ 𝟘)) (sym (Iᴹ-diag ⌜ n ⌝)) 𝟙≰𝟘)
    (λ {p} {q} ne → change-𝟘 (≤-reflexive (Iᴹ-off (λ e → ne (⌜⌝-injective e)))))

  ⊤ᵐ : ModeMatrix
  ⊤ᵐ = mode-matrix ⊤ᴹ
    (λ n → stuck , subst (λ c → ¬ (c ≤ 𝟘)) (sym (⊤ᴹ-entry n stuck)) ⊤≰𝟘)
    (λ {p} {q} _ → subst Change (sym (⊤ᴹ-entry p ⌜ q ⌝)) change-⊤)

  infixl 7 _·ᵐ_
  infixl 6 _⊔ᵐ_

  _⊔ᵐ_ : ModeMatrix → ModeMatrix → ModeMatrix
  x ⊔ᵐ y = mode-matrix (mat x ⊕ᴹ mat y)
    (λ n → proj₁ (total x n) ,
           nonzero-≤ (⊕ᴹ-ubˡ (mat x) (mat y) ⌜ n ⌝ (proj₁ (total x n))) (proj₂ (total x n)))
    (λ {p} {q} ne → change-≈ (≈-sym (⊕ᴹ-entry (mat x) (mat y) ⌜ p ⌝ ⌜ q ⌝))
                             (change-⊕ (changes x ne) (changes y ne)))

  _·ᵐ_ : ModeMatrix → ModeMatrix → ModeMatrix
  x ·ᵐ y = mode-matrix (mat x ⊗ᴹ mat y) tot chg
    where
      tot : ∀ n → ∃ λ r → ¬ (entry (mat x ⊗ᴹ mat y) ⌜ n ⌝ r ≤ 𝟘)
      tot n with total x n
      ... | q , xq with total′ y q
      ...   | r , yr = r , nonzero-≤ (⊗ᴹ-ub (mat x) (mat y) ⌜ n ⌝ r q) (nonzero-⊗ xq yr)

      chg : ∀ {p r} → ¬ p ≡ r → Change (entry (mat x ⊗ᴹ mat y) ⌜ p ⌝ ⌜ r ⌝)
      chg {p} {r} ne =
        change-≈ (≈-sym (⊗ᴹ-entry (mat x) (mat y) ⌜ p ⌝ ⌜ r ⌝))
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
  -- The zero-product law

  module _ (x y : ModeMatrix) (h : x ·ᵐ y ≾ᵐ uᵐ) where

    private
      hp : ∀ a c → e x a stuck ⊗ e y stuck c ≤ entry Iᴹ a c
      hp a c = ≤-trans (⊗ᴹ-ub (mat x) (mat y) a c stuck) (at {x ·ᵐ y} {uᵐ} h a c)

      ht : ∀ a b c → e x a b ⊗ e y b c ≤ entry Iᴹ a c
      ht a b c = ≤-trans (⊗ᴹ-ub (mat x) (mat y) a c b) (at {x ·ᵐ y} {uᵐ} h a c)

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

    zero-productˡ′ : mat x ≤ᵖ mat uᵐ
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

    zero-productʳ′ : mat y ≤ᵖ mat uᵐ
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

  mode-grade : {D : Duration} → Grade D
  mode-grade = record
    { Carrier         = ModeMatrix
    ; _·_             = _·ᵐ_
    ; u               = uᵐ
    ; _≾_             = _≾ᵐ_
    ; ⊤               = ⊤ᵐ
    ; _⊔_             = _⊔ᵐ_
    ; of-dur          = λ _ → uᵐ
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
    ; of-dur-zero     = pw (λ _ _ → ≤-refl) , pw (λ _ _ → ≤-refl)
    ; of-dur-plus     = pw (⊗ᴹ-identityˡ⁻ Iᴹ) , pw (⊗ᴹ-identityˡ Iᴹ)
    ; antisym?        = nothing
    ; u-least?        = nothing
    ; ·-comm?         = nothing
    ; plus?           = λ _ → nothing
    }

  ----------------------------------------------------------------------
  -- Matrices whose conditions are decided at the representatives

  module Decided (change? : ∀ a → Dec (Change a)) where

    private
      module R (M : Matrix) = Representatives (modes M)

      row : Matrix → Mode → List Mode
      row M x = stuck ∷ ⌜ R.o M ⌝ ∷ mapᴸ ⌜_⌝ (modes M)

      NonzeroIn : Matrix → Mode → Set
      NonzeroIn M x = Any (λ y → ¬ (entry M x y ≤ 𝟘)) (row M x)

      nonzero? : ∀ M x → Dec (NonzeroIn M x)
      nonzero? M x = any? (λ y → ¬? (entry M x y ≤? 𝟘)) (row M x)

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
          witness : ∀ x → Any (λ y → ¬ (entry M x y ≤ 𝟘)) (row M x) → ∃ λ y → ¬ (entry M x y ≤ 𝟘)
          witness x a = let (y , _ , h) = find a in y , h
      ... | no n∉ with find other
      ...   | y , _ , h =
        swapᴹ o n y ,
        subst (λ c → ¬ (c ≤ 𝟘))
          (trans (sym (entry-swap M o∉ n∉ ⌜ o ⌝ y)) (cong (λ m → entry M ⌜ m ⌝ (swapᴹ o n y)) (swap-a o n)))
          h
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
            subst Change (sym (entry-swap M a∉ b∉ ⌜ p' ⌝ ⌜ q' ⌝))
              (c (λ e → ne (cong (swap _ _) e)))
          closed a∉ b∉ stuck   y       c = tt′
          closed a∉ b∉ ⌜ _ ⌝ stuck   c = tt′

    -- a matrix with its conditions decided

    decided : (M : Matrix) {t : True (total? M)} {c : True (changes? M)} → ModeMatrix
    decided M {t} {c} = mode-matrix M (total-from M (toWitness t)) (changes-from M (toWitness c))
