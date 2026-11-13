------------------------------------------------------------------------
-- Closures of mode grades through coordinates.                       --
--                                                                    --
-- Coordinates of an equivariant dioid `S` in a dioid `T` (with the   --
-- trivial action) are maps `h c` from `S` to `T`, each at finitely   --
-- many names `at c`, that are monotone with right adjoints `g c`,    --
-- preserve the product, the join, `𝟘`, `𝟙` and the star, are kept by --
-- the exchange of two names not at `c`, and together reflect the     --
-- order (`Coordinates`).                                             --
--                                                                    --
-- A coordinate maps a matrix over `S` to one over `T`, naming also   --
-- the names at the coordinate (`Transport.H`), and commutes with the --
-- unit, the join, the product and the diagonal matrix of stars: the  --
-- orbit join in an entry of a product is below the join of the terms --
-- through every mode, by the adjoint, the permutations of the orbit  --
-- carrying terms to terms. So it commutes with the candidate of      --
-- `ModeGrade.Closures`, and where the star of `T` is a Kleene star   --
-- the candidate is closed under the product at every coordinate      --
-- (`ModeClosure.Core`), hence in `S`: with `w` a bound on the number --
-- of names at a coordinate and `n` the number of modes a grade       --
-- names, the candidate with `4 + (w + n)` powers is its closure      --
-- (`closureᶜ`).                                                      --
------------------------------------------------------------------------

open import Grades.Indexed using (Names)
open import Grades.Matrix.Dioid using (Dioid)
open import Grades.Matrix.Nominal using (Equivariant)

module Grades.Matrix.ModeCoordinates (𝒩 : Names) (S : Dioid) (Eq : Equivariant 𝒩 S) (𝕋 : Dioid) where

open import Data.List.Base using (List; []; _∷_; _++_; length) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; suc; _+_) renaming (_≤_ to _≤ⁿ_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Nullary using (Dec; yes; no)

open import Grades.Base using (Plus)
open import Grades.Matrix.Nominal 𝒩 using (Perm; Fixes; trivial)

open import Util.Equality hiding (J)

open Dioid S
open Equivariant Eq
open import Grades.Matrix.Modes 𝒩
open import Grades.Matrix.Matrices 𝒩 S Eq
open import Grades.Matrix.ModeGrade 𝒩 S Eq
open import Grades.Matrix.ModeClosure 𝒩 S Eq using (module Candidates; candidate-mat)
import Grades.Matrix.Matrices
import Grades.Matrix.ModeGrade
import Grades.Matrix.ModeClosure

private
  module T  = Dioid 𝕋
  module MT = Grades.Matrix.Matrices 𝒩 𝕋 (trivial 𝕋)
  module GT = Grades.Matrix.ModeGrade 𝒩 𝕋 (trivial 𝕋)
  module CT = Grades.Matrix.ModeClosure 𝒩 𝕋 (trivial 𝕋)

------------------------------------------------------------------------
-- Coordinates

record Coordinates (St : Stars) (Stᵀ : GT.Stars) : Set₁ where
  private
    module St  = Stars St
    module Stᵀ = GT.Stars Stᵀ
  field
    Coord    : Set
    at       : Coord → List Name
    width    : ℕ
    at-width : ∀ c → length (at c) ≤ⁿ width
    h        : Coord → Carrier → T.Carrier
    g        : Coord → T.Carrier → Carrier
    h-mono   : ∀ c {a b} → a ≤ b → h c a T.≤ h c b
    h-g      : ∀ c {a t} → h c a T.≤ t → a ≤ g c t
    g-h      : ∀ c {a t} → a ≤ g c t → h c a T.≤ t
    h-⊗      : ∀ c a b → h c (a ⊗ b) T.≈ (h c a T.⊗ h c b)
    h-⊕      : ∀ c a b → h c (a ⊕ b) T.≤ (h c a T.⊕ h c b)
    h-𝟘      : ∀ c → h c 𝟘 T.≤ T.𝟘
    h-𝟙      : ∀ c → h c 𝟙 T.≈ T.𝟙
    h-star   : ∀ c a → h c (St.star a) T.≈ Stᵀ.star (h c a)
    h-act    : ∀ c {a b} → a ∉ at c → b ∉ at c → ∀ x → h c (act a b x) T.≈ h c x
    reflect  : ∀ {a b} → (∀ c → h c a T.≤ h c b) → a ≤ b

------------------------------------------------------------------------
-- With a Kleene star on `T`, the star of `S` is a Kleene star

open import Grades.Matrix.ModeClosure 𝒩 S Eq using (KleeneStars)

kleeneᶜ : {St : Stars} {Stᵀ : GT.Stars} → Coordinates St Stᵀ → CT.KleeneStars Stᵀ → KleeneStars St
kleeneᶜ {St} {Stᵀ} C Kᵀ = record
  { star-ext   = λ a → reflect λ c →
      T.≤-trans (Kᵀ.star-ext (h c a)) (proj₂ (h-star c a))
  ; star-idem  = λ a → reflect λ c →
      T.≤-trans (proj₁ (h-⊗ c _ _))
        (T.≤-trans (T.⊗-mono (proj₁ (h-star c a)) (proj₁ (h-star c a)))
          (T.≤-trans (Kᵀ.star-idem (h c a)) (proj₂ (h-star c a))))
  ; star-split = λ a b d → reflect λ c →
      T.≤-trans (proj₁ (h-⊗ c _ _))
        (T.≤-trans (T.⊗-mono (T.≤-trans (proj₁ (h-⊗ c _ _)) (T.⊗-mono (proj₁ (h-star c a)) T.≤-refl))
                             (proj₁ (h-star c d)))
          (T.≤-trans (Kᵀ.star-split (h c a) (h c b) (h c d))
            (T.≤-trans (T.⊕-mono (T.≤-trans (T.⊗-mono (proj₂ (h-star c a)) T.≤-refl) (proj₂ (h-⊗ c _ _)))
                                 (T.≤-trans (T.⊗-mono T.≤-refl (proj₂ (h-star c d))) (proj₂ (h-⊗ c _ _))))
              (T.⊕-lub (h-mono c (⊕-ubˡ _ _)) (h-mono c (⊕-ubʳ _ _))))))
  }
  where
    open Coordinates C
    module Kᵀ = CT.KleeneStars Kᵀ

------------------------------------------------------------------------
-- A coordinate on matrices

module Transport {St : Stars} {Stᵀ : GT.Stars} (C : Coordinates St Stᵀ) where

  open Coordinates C
  private
    module St  = Stars St
    module Stᵀ = GT.Stars Stᵀ

  module _ (c : Coord) where

    private
      h-cong : ∀ {a b} → a ≈ b → h c a T.≈ h c b
      h-cong (p , q) = h-mono c p , h-mono c q

      h-𝟘≈ : h c 𝟘 T.≈ T.𝟘
      h-𝟘≈ = h-𝟘 c , T.𝟘-≤ _

      ∉ˡ : ∀ {a} F → a ∉ at c ++ F → a ∉ at c
      ∉ˡ F a∉ a∈ = a∉ (∈-++⁺ˡ a∈)

      ∉ʳ : ∀ {a} F → a ∉ at c ++ F → a ∉ F
      ∉ʳ F a∉ a∈ = a∉ (∈-++⁺ʳ (at c) a∈)

    -- the matrix of the coordinates of the entries

    H : Matrix → MT.Matrix
    MT.modes (H M) = at c ++ modes M
    MT.row (H M) p y = h c (row M p y)
    MT.equivariant (H M) {a} {b} a∉ b∉ p y =
      T.≈-trans (h-cong (equivariant M (∉ʳ (modes M) a∉) (∉ʳ (modes M) b∉) p y))
                (h-act c (∉ˡ (modes M) a∉) (∉ˡ (modes M) b∉) (row M p y))

    -- a matrix over `T` with the coordinates of the entries of one
    -- over `S`

    Rel : Matrix → MT.Matrix → Set
    Rel M N = ∀ x y → h c (entry M x y) T.≈ MT.entry N x y

    private
      -- the rows of `stuck`
      stuck-rel : ∀ {a b} y → a ≡ entry Iᴹ stuck y → b ≡ MT.entry MT.Iᴹ stuck y → h c a T.≈ b
      stuck-rel stuck   refl refl = h-𝟙 c
      stuck-rel ⌜ _ ⌝ refl refl = h-𝟘≈

    rel-H : ∀ M → Rel M (H M)
    rel-H M stuck   y = stuck-rel y (stuck-entry M y) (stuck-entryᵀ (H M) y)
      where
        stuck-entry : ∀ M y → entry M stuck y ≡ entry Iᴹ stuck y
        stuck-entry M stuck   = refl
        stuck-entry M ⌜ _ ⌝ = refl
        stuck-entryᵀ : ∀ N y → MT.entry N stuck y ≡ MT.entry MT.Iᴹ stuck y
        stuck-entryᵀ N stuck   = refl
        stuck-entryᵀ N ⌜ _ ⌝ = refl
    rel-H M ⌜ p ⌝ y = T.≈-refl

    rel-I : Rel Iᴹ MT.Iᴹ
    rel-I x y with x ≟ᴹ y
    ... | yes refl =
      T.≈-trans (T.≈-reflexive (cong (h c) (Iᴹ-diag x)))
                (T.≈-trans (h-𝟙 c) (T.≈-reflexive (sym (MT.Iᴹ-diag x))))
    ... | no ne =
      T.≈-trans (T.≈-reflexive (cong (h c) (Iᴹ-off ne)))
                (T.≈-trans h-𝟘≈ (T.≈-reflexive (sym (MT.Iᴹ-off ne))))

    rel-⊕ : ∀ {M M' N N'} → Rel M M' → Rel N N' → Rel (M ⊕ᴹ N) (M' MT.⊕ᴹ N')
    rel-⊕ {M} {M'} {N} {N'} r r' x y =
        T.≤-trans (h-mono c (proj₁ (⊕ᴹ-entry M N x y)))
          (T.≤-trans (h-⊕ c _ _)
            (T.≤-trans (T.⊕-mono (proj₁ (r x y)) (proj₁ (r' x y))) (proj₂ (MT.⊕ᴹ-entry M' N' x y))))
      , T.≤-trans (proj₁ (MT.⊕ᴹ-entry M' N' x y))
          (T.≤-trans (T.⊕-lub (T.≤-trans (proj₂ (r x y)) (h-mono c (⊕-ubˡ _ _)))
                              (T.≤-trans (proj₂ (r' x y)) (h-mono c (⊕-ubʳ _ _))))
            (h-mono c (proj₂ (⊕ᴹ-entry M N x y))))

    private
      actᴾ-𝟘 : ∀ π → actᴾ π 𝟘 ≤ 𝟘
      actᴾ-𝟘 []            = ≤-refl
      actᴾ-𝟘 ((a , b) ∷ π) = ≤-trans (act-mono (actᴾ-𝟘 π)) (proj₁ (act-𝟘 a b))

      actᴾ-⊕ : ∀ π x y → actᴾ π (x ⊕ y) ≤ actᴾ π x ⊕ actᴾ π y
      actᴾ-⊕ []            x y = ≤-refl
      actᴾ-⊕ ((a , b) ∷ π) x y = ≤-trans (act-mono (actᴾ-⊕ π x y)) (proj₁ (act-⊕ a b _ _))

      actᴾ-⨁ : ∀ π as → actᴾ π (⨁ as) ≤ ⨁ (mapᴸ (actᴾ π) as)
      actᴾ-⨁ π []       = actᴾ-𝟘 π
      actᴾ-⨁ π (a ∷ as) = ≤-trans (actᴾ-⊕ π a (⨁ as)) (⊕-mono ≤-refl (actᴾ-⨁ π as))

      h-⨁ : ∀ as {t} → (∀ {a} → a ∈ as → h c a T.≤ t) → h c (⨁ as) T.≤ t
      h-⨁ []       f = T.≤-trans (h-𝟘 c) (T.𝟘-≤ _)
      h-⨁ (a ∷ as) f =
        T.≤-trans (h-⊕ c a (⨁ as)) (T.⊕-lub (f (here refl)) (h-⨁ as (λ p → f (there p))))

    rel-⊗ : ∀ {M M' N N'} → Rel M M' → Rel N N' → Rel (M ⊗ᴹ N) (M' MT.⊗ᴹ N')
    rel-⊗ {M} {M'} {N} {N'} r r' x y = upper x y , lower
      where
        upper : ∀ x y → h c (entry (M ⊗ᴹ N) x y) T.≤ MT.entry (M' MT.⊗ᴹ N') x y
        upper stuck stuck   = T.≤-trans (proj₁ (h-𝟙 c)) T.≤-refl
        upper stuck ⌜ _ ⌝ = T.≤-trans (h-𝟘 c) T.≤-refl
        upper ⌜ p ⌝ y = g-h c (orbit-lub λ π fix → h-g c (perm π fix))
          where
            module P = Product M N
            t' = MT.entry (M' MT.⊗ᴹ N') ⌜ p ⌝ y

            term-≤′ : ∀ q → h c (entry M ⌜ p ⌝ q ⊗ entry N q y) T.≤ t'
            term-≤′ q =
              T.≤-trans (proj₁ (h-⊗ c _ _))
                (T.≤-trans (T.⊗-mono (proj₁ (r ⌜ p ⌝ q)) (proj₁ (r' q y))) (MT.⊗ᴹ-ub M' N' ⌜ p ⌝ y q))

            to-term : ∀ {b} q → b ≈ P.term ⌜ p ⌝ y q → h c b T.≤ t'
            to-term q e = T.≤-trans (h-mono c (proj₁ e)) (term-≤′ q)

            perm : ∀ π → Fixes (P.around ⌜ p ⌝ y) π
                 → h c (actᴾ π (P.joined ⌜ p ⌝ y)) T.≤ t'
            perm π fix =
              T.≤-trans (h-mono c (actᴾ-⨁ π (P.terms ⌜ p ⌝ y)))
                (h-⨁ (mapᴸ (actᴾ π) (P.terms ⌜ p ⌝ y)) λ a∈ → case (∈-map⁻ (actᴾ π) a∈))
              where
                case : ∀ {a} → (∃ λ b → b ∈ P.terms ⌜ p ⌝ y × a ≡ actᴾ π b) → h c a T.≤ t'
                case (b , b∈ , refl) with ∈-map⁻ (P.term ⌜ p ⌝ y) b∈
                ... | q , _ , refl = to-term _ (P.term-perm ⌜ p ⌝ y π fix q)

        lower : MT.entry (M' MT.⊗ᴹ N') x y T.≤ h c (entry (M ⊗ᴹ N) x y)
        lower = MT.⊗ᴹ-lub M' N' x y λ q →
          T.≤-trans (T.⊗-mono (proj₂ (r x q)) (proj₂ (r' q y)))
            (T.≤-trans (proj₂ (h-⊗ c _ _)) (h-mono c (⊗ᴹ-ub M N x y q)))

    rel-stars : ∀ {M M'} → Rel M M' → Rel (StarMatrices.starsᴹ St M) (GT.StarMatrices.starsᴹ Stᵀ M')
    rel-stars {M} {M'} r stuck stuck   = h-𝟙 c
    rel-stars {M} {M'} r stuck ⌜ _ ⌝ = h-𝟘≈
    rel-stars {M} {M'} r ⌜ p ⌝ y = by (y ≟ᴹ ⌜ p ⌝)
      where
        by : Dec (y ≡ ⌜ p ⌝)
           → h c (entry (StarMatrices.starsᴹ St M) ⌜ p ⌝ y)
               T.≈ MT.entry (GT.StarMatrices.starsᴹ Stᵀ M') ⌜ p ⌝ y
        by (yes refl) =
          T.≈-trans (T.≈-reflexive (cong (h c) (StarMatrices.stars-diag St M p)))
            (T.≈-trans (h-star c _)
              (T.≈-trans (Stᵀ.star-cong (r ⌜ p ⌝ ⌜ p ⌝))
                (T.≈-reflexive (sym (GT.StarMatrices.stars-diag Stᵀ M' p)))))
        by (no ne) =
          T.≈-trans (T.≈-reflexive (cong (h c) (StarMatrices.stars-off St M p ne)))
            (T.≈-trans h-𝟘≈ (T.≈-reflexive (sym (GT.StarMatrices.stars-off Stᵀ M' p ne))))

    rel-powers : ∀ {M M'} → Rel M M' → ∀ j
               → Rel (Candidates.powersᴹ St M j) (CT.Candidates.powersᴹ Stᵀ M' j)
    rel-powers r zero    = r
    rel-powers r (suc j) = rel-⊕ r (rel-⊗ r (rel-powers r j))

    rel-candidate : ∀ {M M'} → Rel M M' → ∀ k
                  → Rel (Candidates.candidateᴹ St k M) (CT.Candidates.candidateᴹ Stᵀ k M')
    rel-candidate r k =
      rel-⊗ (rel-⊗ (rel-⊕ rel-I (rel-powers r k)) (rel-stars (rel-powers r k))) (rel-powers r k)

------------------------------------------------------------------------
-- The closures

module _ (E : ModeEntries) {St : Stars} {Stᵀ : GT.Stars}
         (Kᵀ : CT.KleeneStars Stᵀ) (C : Coordinates St Stᵀ) where

  open Coordinates C
  open Closures E St
  open Candidates St
  open Transport C

  private
    module CoreT = CT.Core Stᵀ Kᵀ (λ _ _ _ → T.≈-refl)

  -- the candidate with at least `4 + (width + n)` powers, `n` the
  -- number of modes the matrix names, is closed under the product
  candidate-closedᶜ : ∀ M k → 4 + (width + length (modes M)) ≤ⁿ k
                    → candidateᴹ k M ⊗ᴹ M ≤ᵖ candidateᴹ k M
  candidate-closedᶜ M k k≥ x y = reflect λ c →
    T.≤-trans (proj₁ (rel-⊗ c (rel-candidate c (rel-H c M) k) (rel-H c M) x y))
      (T.≤-trans (CoreT.candidate-closedᴹ (H c M) k (width-≤ c) x y)
        (proj₂ (rel-candidate c (rel-H c M) k x y)))
    where
      width-≤ : ∀ c → 4 + length (at c ++ modes M) ≤ⁿ k
      width-≤ c =
        ℕₚ.≤-trans (ℕₚ.+-monoʳ-≤ 4 (ℕₚ.≤-trans (ℕₚ.≤-reflexive (length-++ (at c)))
                                               (ℕₚ.+-monoˡ-≤ (length (modes M)) (at-width c))))
                   k≥

  module _ (A : ModeMatrix E) where

    -- the number of powers
    boundᶜ : ℕ
    boundᶜ = 4 + (width + length (modes (mat A)))

    candidate-iterᶜ : _≾ᵐ_ E (_·ᵐ_ E (candidate boundᶜ A) (candidate boundᶜ A)) (candidate boundᶜ A)
    candidate-iterᶜ =
      pointwise⇒≤ᴹ (candidate-indʳ boundᶜ A
        (subst (λ X → X ⊗ᴹ mat A ≤ᵖ X) (sym (candidate-mat E St boundᶜ A))
               (candidate-closedᶜ (mat A) boundᶜ ℕₚ.≤-refl)))

    -- the closure of a grade

    closureᶜ : Plus (_·ᵐ_ E) (_≾ᵐ_ E) A
    closureᶜ = candidate-plus boundᶜ A candidate-iterᶜ
