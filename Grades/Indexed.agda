------------------------------------------------------------------------
-- Indexed grades: maps from names, constant outside a finite set.    --
--                                                                    --
-- Over an infinite set of names with decidable equality, `Map C` is  --
-- the set of maps from names to `C` that are constant outside a      --
-- finite set, each held as a default and finitely many entries;      --
-- `m ! s` is the value at the name `s`. Pointwise operations are     --
-- again such maps, and a relation holds pointwise iff it holds at    --
-- the default and at every name of an entry (`pointwise`): a name    --
-- outside the entries stands for all of them.                        --
--                                                                    --
-- A semilattice, an action and a grade lift to maps, with every      --
-- operation, the order included, pointwise, and every law holding    --
-- pointwise; `of-dur τ` is constantly `of-dur τ`. Distinct           --
-- representations of one map are equivalent but not equal, so        --
-- `≃⇒≡?` is not declared. Its hints declare the unit least and `_·_` --
-- commutative where those of the component do, and no closures.      --
------------------------------------------------------------------------

module Grades.Indexed where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
import Data.List.Membership.DecPropositional as DecMembership
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ; suc; _≤_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; n≮n; ≤-refl; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.List.Base as List

open import Relation.Binary.Definitions using (DecidableEquality; Decidable)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Nullary.Decidable using (_×-dec_; map′)

open import Grades.Durations using (Duration)
open import Grades.Base
open import Grades.Hints
open import Grades.SemiDirect using (Semilattice; Action)

open import Util.Equality

------------------------------------------------------------------------
-- Infinite sets of names with decidable equality

record Names : Set₁ where
  field
    Name    : Set
    _≟ᴺ_    : DecidableEquality Name
    fresh   : List Name → Name
    fresh-∉ : ∀ ns → fresh ns ∉ ns

-- the natural numbers

ℕ-names : Names
ℕ-names = record
  { Name = ℕ ; _≟ᴺ_ = _≟_ ; fresh = λ ns → suc (sum ns) ; fresh-∉ = λ ns p → n≮n (sum ns) (≤-sum p) }
  where
    sum : List ℕ → ℕ
    sum = List.foldr _+_ 0
    ≤-sum : ∀ {x xs} → x ∈ xs → x ≤ sum xs
    ≤-sum {xs = y ∷ ys} (here refl) = m≤m+n y (sum ys)
    ≤-sum {xs = y ∷ ys} (there q)   = ≤-trans (≤-sum q) (m≤n+m (sum ys) y)

------------------------------------------------------------------------
-- Maps constant outside a finite set

module Maps (𝒩 : Names) where

  open Names 𝒩
  open DecMembership _≟ᴺ_ using (_∈?_)

  record Map (C : Set) : Set where
    constructor _∣_
    field
      others : C
      named  : List (Name × C)

  open Map public

  module _ {C : Set} where

    -- the value in a list of entries, the first one for the name

    lookup : C → List (Name × C) → Name → C
    lookup d []             s = d
    lookup d ((s' , c) ∷ es) s with s ≟ᴺ s'
    ... | yes _ = c
    ... | no _  = lookup d es s

    infixl 9 _!_

    _!_ : Map C → Name → C
    m ! s = lookup (others m) (named m) s

    keys : Map C → List Name
    keys m = mapᴸ proj₁ (named m)

    lookup-∉ : ∀ d es s → s ∉ mapᴸ proj₁ es → lookup d es s ≡ d
    lookup-∉ d []              s _ = refl
    lookup-∉ d ((s' , c) ∷ es) s p with s ≟ᴺ s'
    ... | yes eq = ⊥-elim (p (here eq))
    ... | no _   = lookup-∉ d es s (λ q → p (there q))

    -- entries for the names `ks`, valued by `g`

    tab : List Name → (Name → C) → List (Name × C)
    tab ks g = mapᴸ (λ k → k , g k) ks

    lookup-tab-∈ : ∀ d ks g s → s ∈ ks → lookup d (tab ks g) s ≡ g s
    lookup-tab-∈ d (k ∷ ks) g s p with s ≟ᴺ k
    ... | yes refl = refl
    ... | no ¬eq with p
    ...   | here eq = ⊥-elim (¬eq eq)
    ...   | there q = lookup-tab-∈ d ks g s q

    lookup-tab-∉ : ∀ d ks g s → s ∉ ks → lookup d (tab ks g) s ≡ d
    lookup-tab-∉ d []       g s _ = refl
    lookup-tab-∉ d (k ∷ ks) g s p with s ≟ᴺ k
    ... | yes eq = ⊥-elim (p (here eq))
    ... | no _   = lookup-tab-∉ d ks g s (λ q → p (there q))

  -- the constant map

  everywhere : {C : Set} → C → Map C
  everywhere c = c ∣ []

  !-everywhere : {C : Set} (c : C) (s : Name) → everywhere c ! s ≡ c
  !-everywhere c s = refl

  -- a map composed with a function

  map : {C C' : Set} → (C → C') → Map C → Map C'
  map f m = f (others m) ∣ mapᴸ (λ (s , c) → s , f c) (named m)

  !-map : {C C' : Set} (f : C → C') (m : Map C) (s : Name) → map f m ! s ≡ f (m ! s)
  !-map {C} f (d ∣ es) s = go es
    where
      go : (es : List (Name × C)) → lookup (f d) (mapᴸ (λ (s , c) → s , f c) es) s ≡ f (lookup d es s)
      go []              = refl
      go ((s' , c) ∷ es) with s ≟ᴺ s'
      ... | yes _ = refl
      ... | no _  = go es

  -- two maps combined pointwise

  map₂ : {C : Set} → (C → C → C) → Map C → Map C → Map C
  map₂ f m m' = f (others m) (others m') ∣ tab (keys m ++ keys m') (λ s → f (m ! s) (m' ! s))

  !-map₂ : {C : Set} (f : C → C → C) (m m' : Map C) (s : Name)
         → map₂ f m m' ! s ≡ f (m ! s) (m' ! s)
  !-map₂ f m m' s with s ∈? (keys m ++ keys m')
  ... | yes p = lookup-tab-∈ _ (keys m ++ keys m') _ s p
  ... | no ¬p =
    trans (lookup-tab-∉ _ (keys m ++ keys m') _ s ¬p)
          (sym (cong₂ f (lookup-∉ (others m) (named m) s (λ q → ¬p (∈-++⁺ˡ q)))
                        (lookup-∉ (others m') (named m') s (λ q → ¬p (∈-++⁺ʳ (keys m) q)))))

  ----------------------------------------------------------------------
  -- Relations, pointwise

  module _ {C : Set} (R : C → C → Set) where

    -- at the default and at every name of an entry

    record Pointwise (m m' : Map C) : Set where
      constructor _,ᵖ_
      field
        at-others : R (others m) (others m')
        at-keys   : All (λ s → R (m ! s) (m' ! s)) (keys m ++ keys m')

    -- which is at every name

    pointwise⁻ : ∀ {m m'} → Pointwise m m' → ∀ s → R (m ! s) (m' ! s)
    pointwise⁻ {m} {m'} (r ,ᵖ rs) s with s ∈? (keys m ++ keys m')
    ... | yes p = All.lookup rs p
    ... | no ¬p =
      subst₂ R (sym (lookup-∉ (others m) (named m) s (λ q → ¬p (∈-++⁺ˡ q))))
               (sym (lookup-∉ (others m') (named m') s (λ q → ¬p (∈-++⁺ʳ (keys m) q))))
               r

    pointwise⁺ : ∀ {m m'} → (∀ s → R (m ! s) (m' ! s)) → Pointwise m m'
    pointwise⁺ {m} {m'} f =
        subst₂ R (lookup-∉ (others m) (named m) s (λ q → fresh-∉ ks (∈-++⁺ˡ q)))
                 (lookup-∉ (others m') (named m') s (λ q → fresh-∉ ks (∈-++⁺ʳ (keys m) q)))
                 (f s)
      ,ᵖ All.tabulate (λ {s} _ → f s)
      where
        ks = keys m ++ keys m'
        s  = fresh ks

    Pointwise? : Decidable R → Decidable Pointwise
    Pointwise? R? m m' =
      map′ (λ (r , rs) → r ,ᵖ rs) (λ (r ,ᵖ rs) → r , rs)
           (R? (others m) (others m') ×-dec All.all? (λ s → R? (m ! s) (m' ! s)) _)

    Pointwise-irrelevant : (∀ {c d} (p q : R c d) → p ≡ q)
                         → ∀ {m m'} (p q : Pointwise m m') → p ≡ q
    Pointwise-irrelevant irr (r ,ᵖ rs) (r' ,ᵖ rs') =
      cong₂ _,ᵖ_ (irr r r') (All.irrelevant (λ p q → irr p q) rs rs')

  ----------------------------------------------------------------------
  -- Lifting a semilattice

  module _ (N : Semilattice) where

    private module N = Semilattice N
    open N using (_⊑_; _∨_)

    private
      ⊑ᴹ : Map N.Carrier → Map N.Carrier → Set
      ⊑ᴹ = Pointwise _⊑_

      pw = pointwise⁺ _⊑_
      at = pointwise⁻ _⊑_

      !∨ : ∀ m m' s → map₂ _∨_ m m' ! s ≡ (m ! s) ∨ (m' ! s)
      !∨ = !-map₂ _∨_

    indexedˢ : Semilattice
    indexedˢ = record
      { Carrier      = Map N.Carrier
      ; _⊑_          = ⊑ᴹ
      ; bot          = everywhere N.bot
      ; top          = everywhere N.top
      ; _∨_          = map₂ _∨_
      ; ⊑-refl       = pw λ _ → N.⊑-refl
      ; ⊑-trans      = λ p q → pw λ s → N.⊑-trans (at p s) (at q s)
      ; ⊑-irrelevant = Pointwise-irrelevant _⊑_ N.⊑-irrelevant
      ; _⊑?_         = Pointwise? _⊑_ N._⊑?_
      ; bot-⊑        = λ m → pw λ s → N.bot-⊑ (m ! s)
      ; ⊑-top        = λ m → pw λ s → N.⊑-top (m ! s)
      ; ∨-ubˡ        = λ m m' → pw λ s → subst ((m ! s) ⊑_) (sym (!∨ m m' s)) (N.∨-ubˡ _ _)
      ; ∨-ubʳ        = λ m m' → pw λ s → subst ((m' ! s) ⊑_) (sym (!∨ m m' s)) (N.∨-ubʳ _ _)
      ; ∨-lub        = λ {m} {m'} p q → pw λ s →
                         subst (_⊑ _) (sym (!∨ m m' s)) (N.∨-lub (at p s) (at q s))
      ; ≈⇒≡?         = nothing
      }

  ----------------------------------------------------------------------
  -- Lifting an action, pointwise

  module _ {D : Duration} {M : Grade D} {N : Semilattice} (A : Action M N) where

    private
      module M = Grade M
      module N = Semilattice N
      module A = Action A
      open N using (_⊑_; _∨_)
      pw = pointwise⁺ _⊑_
      at = pointwise⁻ _⊑_

    indexedᵃ : Action M (indexedˢ N)
    indexedᵃ = record
      { act              = λ m → map (A.act m)
      ; act-identity     = λ f →
            (pw λ s → subst (_⊑ _) (sym (!-map (A.act M.u) f s)) (proj₁ (A.act-identity (f ! s))))
          , (pw λ s → subst (_ ⊑_) (sym (!-map (A.act M.u) f s)) (proj₂ (A.act-identity (f ! s))))
      ; act-comp         = λ m m' f →
            (pw λ s → subst₂ _⊑_ (sym (!-map (A.act (m M.· m')) f s)) (sym (inner m m' f s))
                                (proj₁ (A.act-comp m m' (f ! s))))
          , (pw λ s → subst₂ _⊑_ (sym (inner m m' f s)) (sym (!-map (A.act (m M.· m')) f s))
                                (proj₂ (A.act-comp m m' (f ! s))))
      ; act-bot          = λ m → pw λ s → A.act-bot m
      ; act-∨            = λ m f f' → pw λ s →
          subst₂ _⊑_ (sym (trans (!-map (A.act m) (map₂ _∨_ f f') s)
                                 (cong (A.act m) (!-map₂ _∨_ f f' s))))
                     (sym (trans (!-map₂ _∨_ (map (A.act m) f) (map (A.act m) f') s)
                                 (cong₂ _∨_ (!-map (A.act m) f s) (!-map (A.act m) f' s))))
                     (A.act-∨ m (f ! s) (f' ! s))
      ; act-⊔            = λ m m' f → pw λ s →
          subst₂ _⊑_ (sym (!-map (A.act (m M.⊔ m')) f s))
                     (sym (trans (!-map₂ _∨_ (map (A.act m) f) (map (A.act m') f) s)
                                 (cong₂ _∨_ (!-map (A.act m) f s) (!-map (A.act m') f s))))
                     (A.act-⊔ m m' (f ! s))
      ; act-monoˡ        = λ {m} {m'} {f} p → pw λ s →
          subst₂ _⊑_ (sym (!-map (A.act m) f s)) (sym (!-map (A.act m') f s)) (A.act-monoˡ p)
      ; act-monoʳ        = λ {m} {f} {f'} q → pw λ s →
          subst₂ _⊑_ (sym (!-map (A.act m) f s)) (sym (!-map (A.act m) f' s)) (A.act-monoʳ (at q s))
      ; act-reflects-bot = λ {m} {f} p q → pw λ s →
          A.act-reflects-bot p (subst (_⊑ N.bot) (!-map (A.act m) f s) (at q s))
      }
      where
        inner : ∀ m m' f s → map (A.act m) (map (A.act m') f) ! s ≡ A.act m (A.act m' (f ! s))
        inner m m' f s = trans (!-map (A.act m) (map (A.act m') f) s) (cong (A.act m) (!-map (A.act m') f s))

  ----------------------------------------------------------------------
  -- Lifting a grade, pointwise

  module _ {D : Duration} (G : Grade D) where

    private
      module G = Grade G
      open G using (_≾_; _·_; _⊔_)
      pw = pointwise⁺ _≾_
      at = pointwise⁻ _≾_

      !· : ∀ m m' s → map₂ _·_ m m' ! s ≡ (m ! s) · (m' ! s)
      !· = !-map₂ _·_

      !⊔ : ∀ m m' s → map₂ _⊔_ m m' ! s ≡ (m ! s) ⊔ (m' ! s)
      !⊔ = !-map₂ _⊔_

      -- equivalences, pointwise
      pw≃ : ∀ {m m'} → (∀ s → (m ! s) G.≃ (m' ! s))
          → Pointwise _≾_ m m' × Pointwise _≾_ m' m
      pw≃ e = (pw λ s → proj₁ (e s)) , (pw λ s → proj₂ (e s))

      -- rewriting along equations at a name
      ≃-at : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → a' G.≃ b' → a G.≃ b
      ≃-at refl refl e = e

      ≾-at : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → a' ≾ b' → a ≾ b
      ≾-at refl refl p = p

    indexedᵍ : Grade D
    indexedᵍ = record
      { Carrier         = Map G.Carrier
      ; _·_             = map₂ _·_
      ; u               = everywhere G.u
      ; _≾_             = Pointwise _≾_
      ; ⊤               = everywhere G.⊤
      ; _⊔_             = map₂ _⊔_
      ; of-dur          = λ τ → everywhere (G.of-dur τ)
      ; ·-identityˡ     = λ m → pw≃ λ s → ≃-at (!· (everywhere G.u) m s) refl (G.·-identityˡ (m ! s))
      ; ·-identityʳ     = λ m → pw≃ λ s → ≃-at (!· m (everywhere G.u) s) refl (G.·-identityʳ (m ! s))
      ; ·-assoc         = λ m m' m'' → pw≃ λ s →
          ≃-at (trans (!· (map₂ _·_ m m') m'' s) (cong (_· (m'' ! s)) (!· m m' s)))
               (trans (!· m (map₂ _·_ m' m'') s) (cong ((m ! s) ·_) (!· m' m'' s)))
               (G.·-assoc (m ! s) (m' ! s) (m'' ! s))
      ; ≾-refl          = pw λ _ → G.≾-refl
      ; ≾-trans         = λ p q → pw λ s → G.≾-trans (at p s) (at q s)
      ; ≾-irrelevant    = Pointwise-irrelevant _≾_ G.≾-irrelevant
      ; _≾?_            = Pointwise? _≾_ G._≾?_
      ; ≾-⊤             = λ m → pw λ s → G.≾-⊤ (m ! s)
      ; ⊔-ubˡ           = λ m m' → pw λ s → ≾-at refl (!⊔ m m' s) (G.⊔-ubˡ _ _)
      ; ⊔-ubʳ           = λ m m' → pw λ s → ≾-at refl (!⊔ m m' s) (G.⊔-ubʳ _ _)
      ; ⊔-lub           = λ {m} {m'} p q → pw λ s → ≾-at (!⊔ m m' s) refl (G.⊔-lub (at p s) (at q s))
      ; ·-monoˡ-≾       = λ {m''} {m} {m'} p → pw λ s →
          ≾-at (!· m m'' s) (!· m' m'' s) (G.·-monoˡ-≾ (at p s))
      ; ·-monoʳ-≾       = λ {m''} {m} {m'} p → pw λ s →
          ≾-at (!· m'' m s) (!· m'' m' s) (G.·-monoʳ-≾ (at p s))
      ; ·-distribˡ-⊔-≾  = λ m m' m'' → pw λ s →
          ≾-at (trans (!· m (map₂ _⊔_ m' m'') s) (cong ((m ! s) ·_) (!⊔ m' m'' s)))
               (trans (!⊔ (map₂ _·_ m m') (map₂ _·_ m m'') s)
                      (cong₂ _⊔_ (!· m m' s) (!· m m'' s)))
               (G.·-distribˡ-⊔-≾ (m ! s) (m' ! s) (m'' ! s))
      ; ·-distribʳ-⊔-≾  = λ m m' m'' → pw λ s →
          ≾-at (trans (!· (map₂ _⊔_ m' m'') m s) (cong (_· (m ! s)) (!⊔ m' m'' s)))
               (trans (!⊔ (map₂ _·_ m' m) (map₂ _·_ m'' m) s)
                      (cong₂ _⊔_ (!· m' m s) (!· m'' m s)))
               (G.·-distribʳ-⊔-≾ (m ! s) (m' ! s) (m'' ! s))
      ; ≾-zero-productˡ = λ {m} {m'} p → pw λ s →
          G.≾-zero-productˡ (≾-at (sym (!· m m' s)) refl (at p s))
      ; ≾-zero-productʳ = λ {m} {m'} p → pw λ s →
          G.≾-zero-productʳ (≾-at (sym (!· m m' s)) refl (at p s))
      ; of-dur-zero     = pw≃ λ _ → G.of-dur-zero
      ; of-dur-plus     = λ {τ} {τ'} → pw≃ λ s →
          ≃-at refl (!· (everywhere (G.of-dur τ)) (everywhere (G.of-dur τ')) s) G.of-dur-plus
      ; ≃⇒≡?            = nothing
      }

    -- its hints, from those of `G`

    indexedʰ : GradeHints G → GradeHints indexedᵍ
    indexedʰ H = record
      { u-least? = Maybe.map (λ l m → pw λ s → l (m ! s)) (GradeHints.u-least? H)
      ; ·-comm?  = Maybe.map (λ c m m' → pw≃ λ s →
                     ≃-at (!· m m' s) (!· m' m s) (c (m ! s) (m' ! s))) (GradeHints.·-comm? H)
      ; plus?    = λ _ → nothing
      }

    -- evaluation at a name is a grade morphism onto `G`

    evalᵍ : Name → indexedᵍ →ᵍ G
    evalᵍ s = record
      { map          = _! s
      ; map-monotone = λ p → at p s
      ; map-u        = G.≃-refl
      ; map-·        = λ {m} {m'} → ≃-at (!· m m' s) refl G.≃-refl
      ; map-⊤        = G.≃-refl
      ; map-⊔        = λ {m} {m'} → ≃-at (!⊔ m m' s) refl G.≃-refl
      ; map-of-dur   = G.≃-refl
      }
