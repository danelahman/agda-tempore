------------------------------------------------------------------------
-- Indexed grades: maps from names, constant outside a finite set.    --
--                                                                    --
-- Over a set of names with decidable equality, `Map C` is the set of --
-- maps from names to `C` that are constant outside a finite set,     --
-- each held as a default and finitely many entries; `m ! s` is the   --
-- value at the name `s`. Pointwise operations are again such maps.   --
-- A relation is lifted to maps by holding between the defaults and   --
-- at every name of an entry (`Pointwise`); it then holds at every    --
-- name (`pointwise⁻`).                                               --
--                                                                    --
-- A semilattice, an action and a grade lift to maps, with every      --
-- operation, the order included, pointwise, and every law holding    --
-- pointwise; `ι τ` is constantly `ι τ`. Its hints declare the unit   --
-- least, `_·_` commutative and closures, pointwise, where those of   --
-- the component do. The condition under which a closure gives one of --
-- a semidirect product (`ActionPlus`) holds of the action on maps    --
-- where it holds of the action (`indexed⁺`).                         --
------------------------------------------------------------------------

module Grades.Indexed where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
import Data.List.Membership.DecPropositional as DecMembership
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
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
open import Grades.SemiDirect using (Semilattice; Action; ActionPlus)

open import Util.Equality

------------------------------------------------------------------------
-- Sets of names with decidable equality

record DecNames : Set₁ where
  field
    Name : Set
    _≟ᴺ_ : DecidableEquality Name

-- infinite ones, with a name outside every list

record Names : Set₁ where
  field
    dec     : DecNames
  open DecNames dec public
  field
    fresh   : List Name → Name
    fresh-∉ : ∀ ns → fresh ns ∉ ns

-- the natural numbers

ℕ-names : DecNames
ℕ-names = record { Name = ℕ ; _≟ᴺ_ = _≟_ }

ℕ-infinite : Names
ℕ-infinite = record
  { dec = ℕ-names ; fresh = λ ns → suc (sum ns) ; fresh-∉ = λ ns p → n≮n (sum ns) (≤-sum p) }
  where
    sum : List ℕ → ℕ
    sum = List.foldr _+_ 0
    ≤-sum : ∀ {x xs} → x ∈ xs → x ≤ sum xs
    ≤-sum {xs = y ∷ ys} (here refl) = m≤m+n y (sum ys)
    ≤-sum {xs = y ∷ ys} (there q)   = ≤-trans (≤-sum q) (m≤n+m (sum ys) y)

------------------------------------------------------------------------
-- Maps constant outside a finite set

module Maps (𝒩 : DecNames) where

  open DecNames 𝒩
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

    pointwise⁺ : ∀ {m m'} → R (others m) (others m') → (∀ s → R (m ! s) (m' ! s)) → Pointwise m m'
    pointwise⁺ r f = r ,ᵖ All.tabulate (λ {s} _ → f s)

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
      at₀ = Pointwise.at-others

      !∨ : ∀ m m' s → map₂ _∨_ m m' ! s ≡ (m ! s) ∨ (m' ! s)
      !∨ = !-map₂ _∨_

    indexedˢ : Semilattice
    indexedˢ = record
      { Carrier      = Map N.Carrier
      ; _⊑_          = ⊑ᴹ
      ; bot          = everywhere N.bot
      ; top          = everywhere N.top
      ; _∨_          = map₂ _∨_
      ; ⊑-refl       = pw N.⊑-refl λ _ → N.⊑-refl
      ; ⊑-trans      = λ p q → pw (N.⊑-trans (at₀ p) (at₀ q)) λ s → N.⊑-trans (at p s) (at q s)
      ; ⊑-irrelevant = Pointwise-irrelevant _⊑_ N.⊑-irrelevant
      ; _⊑?_         = Pointwise? _⊑_ N._⊑?_
      ; bot-⊑        = λ m → pw (N.bot-⊑ (others m)) λ s → N.bot-⊑ (m ! s)
      ; ⊑-top        = λ m → pw (N.⊑-top (others m)) λ s → N.⊑-top (m ! s)
      ; ∨-ubˡ        = λ m m' → pw (N.∨-ubˡ _ _) λ s → subst ((m ! s) ⊑_) (sym (!∨ m m' s)) (N.∨-ubˡ _ _)
      ; ∨-ubʳ        = λ m m' → pw (N.∨-ubʳ _ _) λ s → subst ((m' ! s) ⊑_) (sym (!∨ m m' s)) (N.∨-ubʳ _ _)
      ; ∨-lub        = λ {m} {m'} p q → pw (N.∨-lub (at₀ p) (at₀ q)) λ s →
                         subst (_⊑ _) (sym (!∨ m m' s)) (N.∨-lub (at p s) (at q s))
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
      at₀ = Pointwise.at-others

    indexedᵃ : Action M (indexedˢ N)
    indexedᵃ = record
      { act              = λ m → map (A.act m)
      ; act-identity     = λ f →
            (pw (proj₁ (A.act-identity (others f))) λ s →
               subst (_⊑ _) (sym (!-map (A.act M.𝟏) f s)) (proj₁ (A.act-identity (f ! s))))
          , (pw (proj₂ (A.act-identity (others f))) λ s →
               subst (_ ⊑_) (sym (!-map (A.act M.𝟏) f s)) (proj₂ (A.act-identity (f ! s))))
      ; act-comp         = λ m m' f →
            (pw (proj₁ (A.act-comp m m' (others f))) λ s →
               subst₂ _⊑_ (sym (!-map (A.act (m M.· m')) f s)) (sym (inner m m' f s))
                      (proj₁ (A.act-comp m m' (f ! s))))
          , (pw (proj₂ (A.act-comp m m' (others f))) λ s →
               subst₂ _⊑_ (sym (inner m m' f s)) (sym (!-map (A.act (m M.· m')) f s))
                      (proj₂ (A.act-comp m m' (f ! s))))
      ; act-bot          = λ m → pw (A.act-bot m) λ s → A.act-bot m
      ; act-∨            = λ m f f' → pw (A.act-∨ m (others f) (others f')) λ s →
          subst₂ _⊑_ (sym (trans (!-map (A.act m) (map₂ _∨_ f f') s)
                                 (cong (A.act m) (!-map₂ _∨_ f f' s))))
                     (sym (trans (!-map₂ _∨_ (map (A.act m) f) (map (A.act m) f') s)
                                 (cong₂ _∨_ (!-map (A.act m) f s) (!-map (A.act m) f' s))))
                     (A.act-∨ m (f ! s) (f' ! s))
      ; act-⊔            = λ m m' f → pw (A.act-⊔ m m' (others f)) λ s →
          subst₂ _⊑_ (sym (!-map (A.act (m M.⊔ m')) f s))
                     (sym (trans (!-map₂ _∨_ (map (A.act m) f) (map (A.act m') f) s)
                                 (cong₂ _∨_ (!-map (A.act m) f s) (!-map (A.act m') f s))))
                     (A.act-⊔ m m' (f ! s))
      ; act-monoˡ        = λ {m} {m'} {f} p → pw (A.act-monoˡ p) λ s →
          subst₂ _⊑_ (sym (!-map (A.act m) f s)) (sym (!-map (A.act m') f s)) (A.act-monoˡ p)
      ; act-monoʳ        = λ {m} {f} {f'} q → pw (A.act-monoʳ (at₀ q)) λ s →
          subst₂ _⊑_ (sym (!-map (A.act m) f s)) (sym (!-map (A.act m) f' s)) (A.act-monoʳ (at q s))
      ; act-reflects-bot = λ {m} {f} p q → pw (A.act-reflects-bot p (at₀ q)) λ s →
          A.act-reflects-bot p (subst (_⊑ N.bot) (!-map (A.act m) f s) (at q s))
      }
      where
        inner : ∀ m m' f s → map (A.act m) (map (A.act m') f) ! s ≡ A.act m (A.act m' (f ! s))
        inner m m' f s = trans (!-map (A.act m) (map (A.act m') f) s) (cong (A.act m) (!-map (A.act m') f s))

    -- a closure whose action raises nothing that of `m` does not, at
    -- every name

    indexed⁺ : ∀ {m} → ActionPlus A m → ActionPlus indexedᵃ m
    indexed⁺ {m} P = record
      { closure = closure
      ; act-⁺   = λ {f} q → pw (act-⁺ (at₀ q)) λ s →
          subst (_⊑ (f ! s)) (sym (!-map (A.act (Plus.c⁺ closure)) f s))
                (act-⁺ (subst (_⊑ (f ! s)) (!-map (A.act m) f s) (at q s)))
      }
      where open ActionPlus P

  ----------------------------------------------------------------------
  -- Lifting a grade, pointwise

  module _ {D : Duration} (G : Grade D) where

    private
      module G = Grade G
      open G using (_≾_; _·_; _⊔_)
      pw = pointwise⁺ _≾_
      at = pointwise⁻ _≾_
      at₀ = Pointwise.at-others

      !· : ∀ m m' s → map₂ _·_ m m' ! s ≡ (m ! s) · (m' ! s)
      !· = !-map₂ _·_

      !⊔ : ∀ m m' s → map₂ _⊔_ m m' ! s ≡ (m ! s) ⊔ (m' ! s)
      !⊔ = !-map₂ _⊔_

      -- equivalences, pointwise
      pw≃ : ∀ {m m'} → others m G.≃ others m' → (∀ s → (m ! s) G.≃ (m' ! s))
          → Pointwise _≾_ m m' × Pointwise _≾_ m' m
      pw≃ e₀ e = (pw (proj₁ e₀) λ s → proj₁ (e s)) , (pw (proj₂ e₀) λ s → proj₂ (e s))

      -- rewriting along equations at a name
      ≃-at : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → a' G.≃ b' → a G.≃ b
      ≃-at refl refl e = e

      ≾-at : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → a' ≾ b' → a ≾ b
      ≾-at refl refl p = p

      -- closures at the entries of a map
      PlusAt : Name × G.Carrier → Set
      PlusAt (_ , c) = Plus _·_ _≾_ c

      plus-all? : ((c : G.Carrier) → Maybe.Maybe (Plus _·_ _≾_ c))
                → (es : List (Name × G.Carrier)) → Maybe.Maybe (All PlusAt es)
      plus-all? pl []             = Maybe.just All.[]
      plus-all? pl ((_ , c) ∷ es) = Maybe.zipWith All._∷_ (pl c) (plus-all? pl es)

      closures : ∀ {es} → All PlusAt es → List (Name × G.Carrier)
      closures {[]}          All.[]       = []
      closures {(s , _) ∷ _} (p All.∷ ps) = (s , Plus.c⁺ p) ∷ closures ps

      -- the closure at a name, the first entry for it or the default's
      plus-at : ∀ {d} → Plus _·_ _≾_ d → ∀ {es} → All PlusAt es
              → (s : Name) → Plus _·_ _≾_ (lookup d es s)
      plus-at p₀ All.[] s = p₀
      plus-at p₀ {(s' , _) ∷ _} (p All.∷ ps) s with s ≟ᴺ s'
      ... | yes _ = p
      ... | no _  = plus-at p₀ ps s

      !-closures : ∀ {d} (p₀ : Plus _·_ _≾_ d) {es} (ps : All PlusAt es) (s : Name)
                 → lookup (Plus.c⁺ p₀) (closures ps) s ≡ Plus.c⁺ (plus-at p₀ ps s)
      !-closures p₀ All.[] s = refl
      !-closures p₀ {(s' , _) ∷ _} (p All.∷ ps) s with s ≟ᴺ s'
      ... | yes _ = refl
      ... | no _  = !-closures p₀ ps s

      -- the closure of a map, at every name the closure there
      plusᴹ : ∀ {m} → Plus _·_ _≾_ (others m) → All PlusAt (named m)
            → Plus (map₂ _·_) (Pointwise _≾_) m
      plusᴹ {m} p₀ ps = plus m⁺
        (pw (Plus.≾-c⁺ p₀) λ s → ≾-at refl (e s) (Plus.≾-c⁺ (P s)))
        (pw (Plus.c⁺-iter p₀) λ s →
           ≾-at (trans (!· m⁺ m⁺ s) (cong₂ _·_ (e s) (e s))) (e s) (Plus.c⁺-iter (P s)))
        (λ {v} q r → pw (Plus.c⁺-least p₀ (at₀ q) (at₀ r)) λ s →
           ≾-at (e s) refl (Plus.c⁺-least (P s) (at q s) (≾-at (sym (!· v v s)) refl (at r s))))
        (λ {d} q → pw (Plus.⁺-indˡ p₀ (at₀ q)) λ s →
           ≾-at (trans (!· m⁺ d s) (cong (_· (d ! s)) (e s))) refl
                (Plus.⁺-indˡ (P s) (≾-at (sym (!· m d s)) refl (at q s))))
        (λ {d} q → pw (Plus.⁺-indʳ p₀ (at₀ q)) λ s →
           ≾-at (trans (!· d m⁺ s) (cong ((d ! s) ·_) (e s))) refl
                (Plus.⁺-indʳ (P s) (≾-at (sym (!· d m s)) refl (at q s))))
        where
          m⁺ = Plus.c⁺ p₀ ∣ closures ps
          P  = plus-at p₀ ps
          e  = !-closures p₀ ps

    indexedᵍ : Grade D
    indexedᵍ = record
      { Carrier         = Map G.Carrier
      ; _·_             = map₂ _·_
      ; 𝟏               = everywhere G.𝟏
      ; _≾_             = Pointwise _≾_
      ; ⊤               = everywhere G.⊤
      ; _⊔_             = map₂ _⊔_
      ; ι               = λ τ → everywhere (G.ι τ)
      ; ·-identityˡ     = λ m → pw≃ (G.·-identityˡ (others m)) λ s →
          ≃-at (!· (everywhere G.𝟏) m s) refl (G.·-identityˡ (m ! s))
      ; ·-identityʳ     = λ m → pw≃ (G.·-identityʳ (others m)) λ s →
          ≃-at (!· m (everywhere G.𝟏) s) refl (G.·-identityʳ (m ! s))
      ; ·-assoc         = λ m m' m'' → pw≃ (G.·-assoc (others m) (others m') (others m'')) λ s →
          ≃-at (trans (!· (map₂ _·_ m m') m'' s) (cong (_· (m'' ! s)) (!· m m' s)))
               (trans (!· m (map₂ _·_ m' m'') s) (cong ((m ! s) ·_) (!· m' m'' s)))
               (G.·-assoc (m ! s) (m' ! s) (m'' ! s))
      ; ≾-refl          = pw G.≾-refl λ _ → G.≾-refl
      ; ≾-trans         = λ p q → pw (G.≾-trans (at₀ p) (at₀ q)) λ s → G.≾-trans (at p s) (at q s)
      ; ≾-irrelevant    = Pointwise-irrelevant _≾_ G.≾-irrelevant
      ; _≾?_            = Pointwise? _≾_ G._≾?_
      ; ≾-⊤             = λ m → pw (G.≾-⊤ (others m)) λ s → G.≾-⊤ (m ! s)
      ; ⊔-ubˡ           = λ m m' → pw (G.⊔-ubˡ _ _) λ s → ≾-at refl (!⊔ m m' s) (G.⊔-ubˡ _ _)
      ; ⊔-ubʳ           = λ m m' → pw (G.⊔-ubʳ _ _) λ s → ≾-at refl (!⊔ m m' s) (G.⊔-ubʳ _ _)
      ; ⊔-lub           = λ {m} {m'} p q → pw (G.⊔-lub (at₀ p) (at₀ q)) λ s →
          ≾-at (!⊔ m m' s) refl (G.⊔-lub (at p s) (at q s))
      ; ·-monoˡ-≾       = λ {m''} {m} {m'} p → pw (G.·-monoˡ-≾ (at₀ p)) λ s →
          ≾-at (!· m m'' s) (!· m' m'' s) (G.·-monoˡ-≾ (at p s))
      ; ·-monoʳ-≾       = λ {m''} {m} {m'} p → pw (G.·-monoʳ-≾ (at₀ p)) λ s →
          ≾-at (!· m'' m s) (!· m'' m' s) (G.·-monoʳ-≾ (at p s))
      ; ·-distribˡ-⊔-≾  = λ m m' m'' → pw (G.·-distribˡ-⊔-≾ (others m) (others m') (others m'')) λ s →
          ≾-at (trans (!· m (map₂ _⊔_ m' m'') s) (cong ((m ! s) ·_) (!⊔ m' m'' s)))
               (trans (!⊔ (map₂ _·_ m m') (map₂ _·_ m m'') s)
                      (cong₂ _⊔_ (!· m m' s) (!· m m'' s)))
               (G.·-distribˡ-⊔-≾ (m ! s) (m' ! s) (m'' ! s))
      ; ·-distribʳ-⊔-≾  = λ m m' m'' → pw (G.·-distribʳ-⊔-≾ (others m) (others m') (others m'')) λ s →
          ≾-at (trans (!· (map₂ _⊔_ m' m'') m s) (cong (_· (m ! s)) (!⊔ m' m'' s)))
               (trans (!⊔ (map₂ _·_ m' m) (map₂ _·_ m'' m) s)
                      (cong₂ _⊔_ (!· m' m s) (!· m'' m s)))
               (G.·-distribʳ-⊔-≾ (m ! s) (m' ! s) (m'' ! s))
      ; ≾-zero-productˡ = λ {m} {m'} p → pw (G.≾-zero-productˡ (at₀ p)) λ s →
          G.≾-zero-productˡ (≾-at (sym (!· m m' s)) refl (at p s))
      ; ≾-zero-productʳ = λ {m} {m'} p → pw (G.≾-zero-productʳ (at₀ p)) λ s →
          G.≾-zero-productʳ (≾-at (sym (!· m m' s)) refl (at p s))
      ; ι-zero          = pw≃ G.ι-zero λ _ → G.ι-zero
      ; ι-plus          = λ {τ} {τ'} → pw≃ G.ι-plus λ s →
          ≃-at refl (!· (everywhere (G.ι τ)) (everywhere (G.ι τ')) s) G.ι-plus
      }

    -- its hints, from those of `G`, the closure of a map where its
    -- default and its entries have one

    indexedʰ : GradeHints G → GradeHints indexedᵍ
    indexedʰ H = record
      { 𝟏-least? = Maybe.map (λ l m → pw (l (others m)) λ s → l (m ! s)) (GradeHints.𝟏-least? H)
      ; ·-comm?  = Maybe.map (λ c m m' → pw≃ (c (others m) (others m')) λ s →
                     ≃-at (!· m m' s) (!· m' m s) (c (m ! s) (m' ! s))) (GradeHints.·-comm? H)
      ; plus?    = λ m → Maybe.zipWith (plusᴹ {m}) (GradeHints.plus? H (others m))
                                   (plus-all? (GradeHints.plus? H) (named m))
      }

    -- evaluation at a name is a grade morphism onto `G`

    evalᵍ : Name → indexedᵍ →ᵍ G
    evalᵍ s = record
      { map          = _! s
      ; map-monotone = λ p → at p s
      ; map-𝟏        = G.≃-refl
      ; map-·        = λ {m} {m'} → ≃-at (!· m m' s) refl G.≃-refl
      ; map-⊤        = G.≃-refl
      ; map-⊔        = λ {m} {m'} → ≃-at (!⊔ m m' s) refl G.≃-refl
      ; map-ι        = G.≃-refl
      }
