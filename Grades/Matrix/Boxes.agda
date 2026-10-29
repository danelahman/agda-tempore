------------------------------------------------------------------------
-- Boxes over a grade: the equivariant dioid of summaries by name.    --
--                                                                    --
-- A box over a grade `G` is a value of `G` for each name, all but    --
-- finitely many names having one default value, together with a      --
-- value of `G` for the whole: for the mode times, an interval of the --
-- time spent in each mode and an interval of the total time. The     --
-- boxes form a grade, by name and as a whole, with the product, the  --
-- join and the order of `G` (`box-grade`). Adjoining an absorbing    --
-- least element, "no trace", makes them a dioid (`adjoin-zero`).     --
--                                                                    --
-- The names act by renaming: `swap a b` exchanges the values of `a`  --
-- and `b`. The orbit join over the permutations fixing a finite set  --
-- `A` keeps the values of the names in `A` and gives every other     --
-- name the join of the values of the names outside `A`: any name     --
-- outside `A` is carried to any other by a swap fixing `A`. The      --
-- product of `G` distributes over its joins, and so over these.      --
------------------------------------------------------------------------

open import Grades.Durations using (Duration)
open import Grades.Base using (Grade)
open import Grades.Indexed using (Names)

module Grades.Matrix.Boxes {D : Duration} (𝒩 : Names) (G : Grade D) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; filter) renaming (map to mapᴸ; foldr to foldrᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻)
import Data.List.Membership.DecPropositional as DecMembership
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit using (tt) renaming (⊤ to 𝟙ᵗ)
open import Data.Empty renaming (⊥ to 𝟘ᵗ) using ()
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Grades.Indexed using (module Maps)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Hints using (GradeHints)
open import Grades.Matrix.Dioid using (Dioid)
open import Grades.Matrix.Nominal 𝒩 using (Equivariant; Perm; Fixes; along)
open import Grades.Matrix.Modes 𝒩 using (swap; swap-inv; swap-a; swap-b; swap-fix; swap-injective)

open import Util.Equality

open Names 𝒩 using (Name; _≟ᴺ_; fresh; fresh-∉)
open DecMembership _≟ᴺ_ using (_∈?_)
open Maps 𝒩
private module G = Grade G
open G using (_≾_; _·_; _⊔_)

------------------------------------------------------------------------
-- Adjoining an absorbing least element to a grade

module _ {D' : Duration} (B : Grade D') where

  private module B = Grade B

  infix 4 _≤⁰_

  _≤⁰_ : Maybe B.Carrier → Maybe B.Carrier → Set
  nothing ≤⁰ _       = 𝟙ᵗ
  just _  ≤⁰ nothing = 𝟘ᵗ
  just b  ≤⁰ just c  = b B.≾ c

  _⊕⁰_ _⊗⁰_ : Maybe B.Carrier → Maybe B.Carrier → Maybe B.Carrier
  nothing ⊕⁰ c       = c
  just b  ⊕⁰ nothing = just b
  just b  ⊕⁰ just c  = just (b B.⊔ c)

  nothing ⊗⁰ _       = nothing
  just _  ⊗⁰ nothing = nothing
  just b  ⊗⁰ just c  = just (b B.· c)

  private
    refl⁰ : ∀ {x} → x ≤⁰ x
    refl⁰ {nothing} = tt
    refl⁰ {just _}  = B.≾-refl

    ≃⁰ : ∀ {b c} → b B.≃ c → (just b ≤⁰ just c) × (just c ≤⁰ just b)
    ≃⁰ e = e

  adjoin-zero : Dioid
  adjoin-zero = record
    { Carrier      = Maybe B.Carrier
    ; _≤_          = _≤⁰_
    ; 𝟘            = nothing
    ; 𝟙            = just B.u
    ; ⊤            = just B.⊤
    ; _⊕_          = _⊕⁰_
    ; _⊗_          = _⊗⁰_
    ; ≤-refl       = λ {x} → refl⁰ {x}
    ; ≤-trans      = λ { {nothing} _ _ → tt
                       ; {just _} {just _} {just _} p q → B.≾-trans p q }
    ; ≤-irrelevant = λ { {nothing} _ _ → refl
                       ; {just _} {just _} p q → B.≾-irrelevant p q }
    ; _≤?_         = λ { nothing _ → yes tt
                       ; (just _) nothing → no λ ()
                       ; (just b) (just c) → b B.≾? c }
    ; 𝟘-≤          = λ _ → tt
    ; ≤-⊤          = λ { nothing → tt ; (just b) → B.≾-⊤ b }
    ; ⊕-ubˡ        = λ { nothing _ → tt ; (just b) nothing → B.≾-refl
                       ; (just b) (just c) → B.⊔-ubˡ b c }
    ; ⊕-ubʳ        = λ { nothing c → refl⁰ {c} ; (just b) nothing → tt
                       ; (just b) (just c) → B.⊔-ubʳ b c }
    ; ⊕-lub        = λ { {nothing} _ q → q
                       ; {just _} {nothing} p _ → p
                       ; {just _} {just _} {just _} p q → B.⊔-lub p q }
    ; ⊗-identityˡ  = λ { nothing → tt , tt ; (just b) → B.·-identityˡ b }
    ; ⊗-identityʳ  = λ { nothing → tt , tt ; (just b) → B.·-identityʳ b }
    ; ⊗-assoc      = λ { nothing _ _ → tt , tt
                       ; (just _) nothing _ → tt , tt
                       ; (just _) (just _) nothing → tt , tt
                       ; (just a) (just b) (just c) → B.·-assoc a b c }
    ; ⊗-mono       = λ { {nothing} _ _ → tt
                       ; {just _} {just _} {nothing} _ _ → tt
                       ; {just _} {just _} {just _} {just _} p q →
                           B.≾-trans (B.·-monoˡ-≾ p) (B.·-monoʳ-≾ q) }
    ; ⊗-zeroˡ      = λ _ → tt
    ; ⊗-zeroʳ      = λ { nothing → tt ; (just _) → tt }
    ; ⊗-distribˡ   = λ { nothing _ _ → tt
                       ; (just a) nothing c → refl⁰ {just a ⊗⁰ c}
                       ; (just a) (just b) nothing → B.≾-refl
                       ; (just a) (just b) (just c) → B.·-distribˡ-⊔-≾ a b c }
    ; ⊗-distribʳ   = λ { nothing nothing nothing → tt
                       ; nothing nothing (just _) → tt
                       ; nothing (just _) nothing → tt
                       ; nothing (just _) (just _) → tt
                       ; (just a) nothing c → refl⁰ {c ⊗⁰ just a}
                       ; (just a) (just b) nothing → B.≾-refl
                       ; (just a) (just b) (just c) → B.·-distribʳ-⊔-≾ a b c }
    }

------------------------------------------------------------------------
-- Boxes

Box : Set
Box = Map G.Carrier × G.Carrier

-- the boxes as a grade: by name and as a whole

box-grade : Grade D
box-grade = Maps.indexedᵍ 𝒩 G ×ᵍ G

box-gradeʰ : GradeHints G → GradeHints box-grade
box-gradeʰ H = Maps.indexedʰ 𝒩 G H ×ʰ H

boxes : Dioid
boxes = adjoin-zero box-grade

open Dioid boxes using () renaming (Carrier to Entry; _≤_ to _≤ᵇ_; _≈_ to _≈ᵇ_)

private
  open Grade box-grade using () renaming (_≾_ to _≾ᴮ_)
  pw = pointwise⁺ _≾_
  at = pointwise⁻ _≾_

------------------------------------------------------------------------
-- Renaming

-- the map whose value at `s` is that of `m` at `σ s`

rename : (Name → Name) → Map G.Carrier → Map G.Carrier
rename σ m = others m ∣ tab (mapᴸ σ (keys m)) (λ s → m ! σ s)

rename-! : ∀ a b m s → rename (swap a b) m ! s ≡ m ! swap a b s
rename-! a b m s with s ∈? mapᴸ (swap a b) (keys m)
... | yes s∈ = lookup-tab-∈ (others m) _ (λ s → m ! swap a b s) s s∈
... | no s∉ =
  trans (lookup-tab-∉ (others m) _ (λ s → m ! swap a b s) s s∉)
        (sym (lookup-∉ (others m) (named m) (swap a b s)
               (λ σs∈ → s∉ (subst (_∈ _) (swap-inv a b s) (∈-map⁺ (swap a b) σs∈)))))

actᵇ : Name → Name → Entry → Entry
actᵇ a b nothing        = nothing
actᵇ a b (just (m , t)) = just (rename (swap a b) m , t)

private
  swap-refl : ∀ a s → swap a a s ≡ s
  swap-refl a s = case (s ≟ᴺ a)
    where
      case : Dec (s ≡ a) → swap a a s ≡ s
      case (yes refl) = swap-a s s
      case (no ne)    = swap-fix ne ne

  -- maps with the same values are equivalent
  same : ∀ {m m'} → (∀ s → m ! s ≡ m' ! s) → (Pointwise _≾_ m m') × (Pointwise _≾_ m' m)
  same e = pw (λ s → G.≾-reflexive (e s)) , pw (λ s → G.≾-reflexive (sym (e s)))

  justˡ : ∀ {m m' t t'} → (Pointwise _≾_ m m' × Pointwise _≾_ m' m) → t G.≃ t'
        → (just (m , t) ≤ᵇ just (m' , t')) × (just (m' , t') ≤ᵇ just (m , t))
  justˡ (p , q) (r , s) = (p , r) , (q , s)

  ≈-nothing : nothing ≈ᵇ nothing
  ≈-nothing = tt , tt

------------------------------------------------------------------------
-- Permutations act by renaming

-- the name whose value a permuted map has at `s`
ρ : Perm → Name → Name
ρ []            s = s
ρ ((a , b) ∷ π) s = ρ π (swap a b s)

renameᴾ : Perm → Map G.Carrier → Map G.Carrier
renameᴾ []            m = m
renameᴾ ((a , b) ∷ π) m = rename (swap a b) (renameᴾ π m)

renameᴾ-! : ∀ π m s → renameᴾ π m ! s ≡ m ! ρ π s
renameᴾ-! []            m s = refl
renameᴾ-! ((a , b) ∷ π) m s = trans (rename-! a b (renameᴾ π m) s) (renameᴾ-! π m (swap a b s))

along-just : ∀ π m t → along actᵇ π (just (m , t)) ≡ just (renameᴾ π m , t)
along-just []            m t = refl
along-just ((a , b) ∷ π) m t = cong (actᵇ a b) (along-just π m t)

ρ-∈ : ∀ {A} π → Fixes A π → ∀ {s} → s ∈ A → ρ π s ≡ s
ρ-∈ []            []                s∈ = refl
ρ-∈ ((a , b) ∷ π) ((a∉ , b∉) ∷ fix) {s} s∈ =
  trans (cong (ρ π) (swap-fix (λ { refl → a∉ s∈ }) (λ { refl → b∉ s∈ }))) (ρ-∈ π fix s∈)

ρ-∉ : ∀ {A} π → Fixes A π → ∀ {s} → s ∉ A → ρ π s ∉ A
ρ-∉ []            []                s∉ = s∉
ρ-∉ ((a , b) ∷ π) ((a∉ , b∉) ∷ fix) {s} s∉ = ρ-∉ π fix (swap∉ s∉)
  where
    swap∉ : ∀ {s} → s ∉ _ → swap a b s ∉ _
    swap∉ {s} s∉' = case (s ≟ᴺ a) (s ≟ᴺ b)
      where
        case : Dec (s ≡ a) → Dec (s ≡ b) → swap a b s ∉ _
        case (yes refl) _ = subst (_∉ _) (sym (swap-a s b)) b∉
        case (no sa) (yes refl) = subst (_∉ _) (sym (swap-b a s)) a∉
        case (no sa) (no sb) = subst (_∉ _) (sym (swap-fix sa sb)) s∉'

------------------------------------------------------------------------
-- The orbit joins

-- the join of the values of the named names outside `A`, and of the
-- default

rest : List Name → Map G.Carrier → G.Carrier
rest A m = foldrᴸ _⊔_ (others m) (mapᴸ (m !_) (filter (λ k → ¬? (k ∈? A)) (keys m)))

orbit : List Name → Map G.Carrier → Map G.Carrier
orbit A m = rest A m ∣ tab A (m !_)

orbit-∈ : ∀ A m {s} → s ∈ A → orbit A m ! s ≡ m ! s
orbit-∈ A m {s} s∈ = lookup-tab-∈ (rest A m) A (m !_) s s∈

orbit-∉ : ∀ A m {s} → s ∉ A → orbit A m ! s ≡ rest A m
orbit-∉ A m {s} s∉ = lookup-tab-∉ (rest A m) A (m !_) s s∉

private
  fold-ub : ∀ {d} xs {x} → x ∈ xs → x ≾ foldrᴸ _⊔_ d xs
  fold-ub (y ∷ ys) (here refl) = G.⊔-ubˡ y _
  fold-ub (y ∷ ys) (there p)   = G.≾-trans (fold-ub ys p) (G.⊔-ubʳ y _)

  fold-ub-d : ∀ d xs → d ≾ foldrᴸ _⊔_ d xs
  fold-ub-d d []       = G.≾-refl
  fold-ub-d d (y ∷ ys) = G.≾-trans (fold-ub-d d ys) (G.⊔-ubʳ y _)

  fold-lub : ∀ {d t} xs → d ≾ t → (∀ {x} → x ∈ xs → x ≾ t) → foldrᴸ _⊔_ d xs ≾ t
  fold-lub []       p f = p
  fold-lub (y ∷ ys) p f = G.⊔-lub (f (here refl)) (fold-lub ys p (λ q → f (there q)))

  fold-⊗ʳ : ∀ {d c t} xs → d · c ≾ t → (∀ {x} → x ∈ xs → x · c ≾ t) → foldrᴸ _⊔_ d xs · c ≾ t
  fold-⊗ʳ []       p f = p
  fold-⊗ʳ (y ∷ ys) p f =
    G.≾-trans (G.·-distribʳ-⊔-≾ _ y _) (G.⊔-lub (f (here refl)) (fold-⊗ʳ ys p (λ q → f (there q))))

  fold-⊗ˡ : ∀ {d c t} xs → c · d ≾ t → (∀ {x} → x ∈ xs → c · x ≾ t) → c · foldrᴸ _⊔_ d xs ≾ t
  fold-⊗ˡ []       p f = p
  fold-⊗ˡ (y ∷ ys) p f =
    G.≾-trans (G.·-distribˡ-⊔-≾ _ y _) (G.⊔-lub (f (here refl)) (fold-⊗ˡ ys p (λ q → f (there q))))

  outside : List Name → Map G.Carrier → List Name
  outside A m = filter (λ k → ¬? (k ∈? A)) (keys m)

  -- a value outside `A` is below `rest`
  rest-ub : ∀ A m {r} → r ∉ A → m ! r ≾ rest A m
  rest-ub A m {r} r∉ with r ∈? keys m
  ... | yes r∈ = fold-ub (mapᴸ (m !_) (outside A m)) (∈-map⁺ (m !_) r∈o)
    where
      r∈o : r ∈ outside A m
      r∈o = ∈-filter⁺ (λ k → ¬? (k ∈? A)) r∈ r∉
  ... | no r∉k =
    G.≾-trans (G.≾-reflexive (lookup-∉ (others m) (named m) r r∉k))
              (fold-ub-d (others m) (mapᴸ (m !_) (outside A m)))

  -- the values `rest` joins, as values at names outside `A`: the
  -- default at a fresh name, and the named names outside `A`
  rest-cases : ∀ A m (P : G.Carrier → Set) → (∀ r → r ∉ A → P (m ! r))
             → P (others m) × (∀ {x} → x ∈ mapᴸ (m !_) (outside A m) → P x)
  rest-cases A m P f =
      subst P (lookup-∉ (others m) (named m) r₀ (λ p → fresh-∉ _ (∈-++ʳ p)))
        (f r₀ (λ p → fresh-∉ _ (∈-++ˡ p)))
    , λ x∈ → case (∈-map⁻ (m !_) x∈)
    where
      open import Data.List.Base using (_++_)
      open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
      r₀ = fresh (A ++ keys m)
      ∈-++ˡ : ∀ {n} → n ∈ A → n ∈ A ++ keys m
      ∈-++ˡ = ∈-++⁺ˡ
      ∈-++ʳ : ∀ {n} → n ∈ keys m → n ∈ A ++ keys m
      ∈-++ʳ = ∈-++⁺ʳ A
      case : ∀ {x} → (∃ λ k → k ∈ outside A m × x ≡ m ! k) → P x
      case (k , k∈ , refl) = f k (proj₂ (∈-filter⁻ (λ k → ¬? (k ∈? A)) {xs = keys m} k∈))

⟨_⟩ᵇ_ : Entry → List Name → Entry
⟨ nothing ⟩ᵇ A      = nothing
⟨ just (m , t) ⟩ᵇ A = just (orbit A m , t)

private
  along-nothing : ∀ π → along actᵇ π nothing ≡ nothing
  along-nothing []            = refl
  along-nothing ((a , b) ∷ π) = cong (actᵇ a b) (along-nothing π)

  -- a permuted box below an entry, at a name
  permuted : ∀ π m t₀ {n t₁} → along actᵇ π (just (m , t₀)) ≤ᵇ just (n , t₁)
           → ∀ s → m ! ρ π s ≾ n ! s
  permuted π m t₀ le s =
    G.≾-trans (G.≾-reflexive (sym (renameᴾ-! π m s)))
      (at (proj₁ (subst (_≤ᵇ _) (along-just π m t₀) le)) s)

  -- and with a product on the right
  permuted-⊗ʳ : ∀ π m t₀ mc tc {n t₁}
              → Dioid._⊗_ boxes (along actᵇ π (just (m , t₀))) (just (mc , tc)) ≤ᵇ just (n , t₁)
              → ∀ s → (m ! ρ π s) · (mc ! s) ≾ n ! s
  permuted-⊗ʳ π m t₀ mc tc le s =
    G.≾-trans (G.≾-reflexive (sym (trans (!-map₂ _·_ (renameᴾ π m) mc s)
                                          (cong (_· (mc ! s)) (renameᴾ-! π m s)))))
      (at (proj₁ (subst (λ e → Dioid._⊗_ boxes e (just (mc , tc)) ≤ᵇ _) (along-just π m t₀) le)) s)

  permuted-⊗ˡ : ∀ π m t₀ mc tc {n t₁}
              → Dioid._⊗_ boxes (just (mc , tc)) (along actᵇ π (just (m , t₀))) ≤ᵇ just (n , t₁)
              → ∀ s → (mc ! s) · (m ! ρ π s) ≾ n ! s
  permuted-⊗ˡ π m t₀ mc tc le s =
    G.≾-trans (G.≾-reflexive (sym (trans (!-map₂ _·_ mc (renameᴾ π m) s)
                                          (cong ((mc ! s) ·_) (renameᴾ-! π m s)))))
      (at (proj₁ (subst (λ e → Dioid._⊗_ boxes (just (mc , tc)) e ≤ᵇ _) (along-just π m t₀) le)) s)

  -- the swap carrying `r` to `s`, both outside `A`
  carry : ∀ {A r s} → r ∉ A → s ∉ A → Fixes A ((r , s) ∷ [])
  carry r∉ s∉ = (r∉ , s∉) ∷ []

  ρ-carry : ∀ r s → ρ ((r , s) ∷ []) s ≡ r
  ρ-carry r s = swap-b r s

equivariant-boxes : Equivariant boxes
equivariant-boxes = record
  { act       = actᵇ
  ; act-mono  = λ {a} {b} {x} {y} → mono {a} {b} {x} {y}
  ; act-inv   = λ { a b nothing → ≈-nothing
                  ; a b (just (m , t)) → justˡ (same {rename (swap a b) (rename (swap a b) m)} {m} λ s →
                      trans (rename-! a b (rename (swap a b) m) s)
                            (trans (rename-! a b m (swap a b s)) (cong (m !_) (swap-inv a b s))))
                      G.≃-refl }
  ; act-refl  = λ { a nothing → ≈-nothing
                  ; a (just (m , t)) → justˡ (same {rename (swap a a) m} {m} λ s →
                      trans (rename-! a a m s) (cong (m !_) (swap-refl a s))) G.≃-refl }
  ; act-𝟘     = λ _ _ → ≈-nothing
  ; act-𝟙     = λ a b → justˡ (same {rename (swap a b) (everywhere G.u)} {everywhere G.u} λ s → rename-! a b (everywhere G.u) s) G.≃-refl
  ; act-⊕     = λ { a b nothing y → Dioid.≈-refl boxes {actᵇ a b y}
                  ; a b (just z) nothing → Dioid.≈-refl boxes {actᵇ a b (just z)}
                  ; a b (just (m , t)) (just (m' , t')) →
                      justˡ (same {rename (swap a b) (map₂ _⊔_ m m')} {map₂ _⊔_ (rename (swap a b) m) (rename (swap a b) m')}
                                  λ s → pointwise-op _⊔_ a b m m' s) G.≃-refl }
  ; act-⊗     = λ { a b nothing y → ≈-nothing
                  ; a b (just _) nothing → ≈-nothing
                  ; a b (just (m , t)) (just (m' , t')) →
                      justˡ (same {rename (swap a b) (map₂ _·_ m m')} {map₂ _·_ (rename (swap a b) m) (rename (swap a b) m')}
                                  λ s → pointwise-op _·_ a b m m' s) G.≃-refl }
  ; ⟨_⟩_      = ⟨_⟩ᵇ_
  ; orbit-ub  = λ {A} {x} → ub {A} {x}
  ; orbit-lub = λ {A} {x} {t} → lub {A} {x} {t}
  ; orbit-⊗ʳ  = λ {A} {x} {c} {t} → lub-⊗ʳ {A} {x} {c} {t}
  ; orbit-⊗ˡ  = λ {A} {x} {c} {t} → lub-⊗ˡ {A} {x} {c} {t}
  }
  where
    mono : ∀ {a b x y} → x ≤ᵇ y → actᵇ a b x ≤ᵇ actᵇ a b y
    mono {x = nothing} _ = tt
    mono {a} {b} {just (m , t)} {just (m' , t')} (p , q) =
      pw (λ s → subst₂ _≾_ (sym (rename-! a b m s)) (sym (rename-! a b m' s)) (at p (swap a b s))) , q

    pointwise-op : (f : G.Carrier → G.Carrier → G.Carrier) → ∀ a b m m' s
                 → rename (swap a b) (map₂ f m m') ! s ≡ map₂ f (rename (swap a b) m) (rename (swap a b) m') ! s
    pointwise-op f a b m m' s =
      trans (rename-! a b (map₂ f m m') s)
        (trans (!-map₂ f m m' (swap a b s))
          (sym (trans (!-map₂ f (rename (swap a b) m) (rename (swap a b) m') s) (cong₂ f (rename-! a b m s) (rename-! a b m' s)))))

    ub : ∀ {A x} π → Fixes A π → along actᵇ π x ≤ᵇ ⟨ x ⟩ᵇ A
    ub {A} {nothing} π fix = subst (_≤ᵇ nothing) (sym (along-nothing π)) tt
    ub {A} {just (m , t)} π fix =
      subst (_≤ᵇ _) (sym (along-just π m t))
        ( pw (λ s → G.≾-trans (G.≾-reflexive (renameᴾ-! π m s)) (at-s s (s ∈? A)))
        , G.≾-refl )
      where
        at-s : ∀ s → Dec (s ∈ A) → m ! ρ π s ≾ orbit A m ! s
        at-s s (yes s∈) = G.≾-reflexive (trans (cong (m !_) (ρ-∈ π fix s∈)) (sym (orbit-∈ A m s∈)))
        at-s s (no s∉)  = G.≾-trans (rest-ub A m (ρ-∉ π fix s∉)) (G.≾-reflexive (sym (orbit-∉ A m s∉)))

    lub : ∀ {A x t} → (∀ π → Fixes A π → along actᵇ π x ≤ᵇ t) → ⟨ x ⟩ᵇ A ≤ᵇ t
    lub {A} {nothing} f = tt
    lub {A} {just (m , t₀)} {nothing} f = ⊥-elim (f [] [])
    lub {A} {just (m , t₀)} {just (n , t₁)} f =
      pw (λ s → at-s s (s ∈? A)) , proj₂ (f [] [])
      where
        at-s : ∀ s → Dec (s ∈ A) → orbit A m ! s ≾ n ! s
        at-s s (yes s∈) = G.≾-trans (G.≾-reflexive (orbit-∈ A m s∈)) (permuted [] m t₀ (f [] []) s)
        at-s s (no s∉) =
          G.≾-trans (G.≾-reflexive (orbit-∉ A m s∉))
            (fold-lub (mapᴸ (m !_) (outside A m)) (proj₁ cases) (proj₂ cases))
          where
            g : ∀ r → r ∉ A → m ! r ≾ n ! s
            g r r∉ = subst (λ k → m ! k ≾ n ! s) (ρ-carry r s)
                       (permuted ((r , s) ∷ []) m t₀ (f _ (carry r∉ s∉)) s)
            cases = rest-cases A m (λ x → x ≾ n ! s) g

    lub-⊗ʳ : ∀ {A x c t} → (∀ π → Fixes A π → Dioid._⊗_ boxes (along actᵇ π x) c ≤ᵇ t)
           → Dioid._⊗_ boxes (⟨ x ⟩ᵇ A) c ≤ᵇ t
    lub-⊗ʳ {A} {nothing} f = tt
    lub-⊗ʳ {A} {just _} {nothing} f = tt
    lub-⊗ʳ {A} {just (m , t₀)} {just (mc , tc)} {nothing} f = ⊥-elim (f [] [])
    lub-⊗ʳ {A} {just (m , t₀)} {just (mc , tc)} {just (n , t₁)} f =
      pw (λ s → G.≾-trans (G.≾-reflexive (!-map₂ _·_ (orbit A m) mc s)) (at-s s (s ∈? A))) , proj₂ (f [] [])
      where
        at-s : ∀ s → Dec (s ∈ A) → (orbit A m ! s) · (mc ! s) ≾ n ! s
        at-s s (yes s∈) =
          G.≾-trans (G.≾-reflexive (cong (_· (mc ! s)) (orbit-∈ A m s∈)))
            (permuted-⊗ʳ [] m t₀ mc tc (f [] []) s)
        at-s s (no s∉) =
          G.≾-trans (G.≾-reflexive (cong (_· (mc ! s)) (orbit-∉ A m s∉)))
            (fold-⊗ʳ (mapᴸ (m !_) (outside A m)) (proj₁ cases) (proj₂ cases))
          where
            g : ∀ r → r ∉ A → (m ! r) · (mc ! s) ≾ n ! s
            g r r∉ = subst (λ k → (m ! k) · (mc ! s) ≾ n ! s) (ρ-carry r s)
                       (permuted-⊗ʳ ((r , s) ∷ []) m t₀ mc tc (f _ (carry r∉ s∉)) s)
            cases = rest-cases A m (λ x → x · (mc ! s) ≾ n ! s) g

    lub-⊗ˡ : ∀ {A x c t} → (∀ π → Fixes A π → Dioid._⊗_ boxes c (along actᵇ π x) ≤ᵇ t)
           → Dioid._⊗_ boxes c (⟨ x ⟩ᵇ A) ≤ᵇ t
    lub-⊗ˡ {A} {nothing} {nothing} f = tt
    lub-⊗ˡ {A} {nothing} {just _} f = tt
    lub-⊗ˡ {A} {just _} {nothing} f = tt
    lub-⊗ˡ {A} {just (m , t₀)} {just (mc , tc)} {nothing} f = ⊥-elim (f [] [])
    lub-⊗ˡ {A} {just (m , t₀)} {just (mc , tc)} {just (n , t₁)} f =
      pw (λ s → G.≾-trans (G.≾-reflexive (!-map₂ _·_ mc (orbit A m) s)) (at-s s (s ∈? A))) , proj₂ (f [] [])
      where
        at-s : ∀ s → Dec (s ∈ A) → (mc ! s) · (orbit A m ! s) ≾ n ! s
        at-s s (yes s∈) =
          G.≾-trans (G.≾-reflexive (cong ((mc ! s) ·_) (orbit-∈ A m s∈)))
            (permuted-⊗ˡ [] m t₀ mc tc (f [] []) s)
        at-s s (no s∉) =
          G.≾-trans (G.≾-reflexive (cong ((mc ! s) ·_) (orbit-∉ A m s∉)))
            (fold-⊗ˡ (mapᴸ (m !_) (outside A m)) (proj₁ cases) (proj₂ cases))
          where
            g : ∀ r → r ∉ A → (mc ! s) · (m ! r) ≾ n ! s
            g r r∉ = subst (λ k → (mc ! s) · (m ! k) ≾ n ! s) (ρ-carry r s)
                       (permuted-⊗ˡ ((r , s) ∷ []) m t₀ mc tc (f _ (carry r∉ s∉)) s)
            cases = rest-cases A m (λ x → (mc ! s) · x ≾ n ! s) g
