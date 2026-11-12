------------------------------------------------------------------------
-- Optional values as possibly empty ones.                            --
--                                                                    --
-- `nothing` is the empty value (`NonEmpty`): below every value       --
-- (`Order`), the unit of the join `_∨?_` lifted from a join on the   --
-- values (`Join`), and absorbing for a binary operation lifted       --
-- strictly (`lift₂`). The lifted order, join and operations inherit  --
-- the laws of the underlying ones. Where the join of the values is   --
-- associative, commutative and idempotent on the nose, so is the     --
-- lifted one, with unit `nothing` (`∨?-icm`), and the standard       --
-- library's solver for idempotent commutative monoids regroups its   --
-- terms.                                                             --
------------------------------------------------------------------------

module Grades.Examples.InterArrival.Options where

open import Algebra.Bundles using (IdempotentCommutativeMonoid)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

private variable
  A B C X : Set

------------------------------------------------------------------------
-- Non-empty values

NonEmpty : Maybe X → Set
NonEmpty (just _) = ⊤
NonEmpty nothing  = ⊥

------------------------------------------------------------------------
-- Binary operations, lifted strictly

lift₂ : (A → B → C) → Maybe A → Maybe B → Maybe C
lift₂ f (just a) (just b) = just (f a b)
lift₂ f (just _) nothing  = nothing
lift₂ f nothing  _        = nothing

lift₂-nonempty : (f : A → B → C) (u : Maybe A) (v : Maybe B)
               → NonEmpty u → NonEmpty v → NonEmpty (lift₂ f u v)
lift₂-nonempty f (just _) (just _) _ _ = tt

lift₂-nothingʳ : (f : A → B → C) (u : Maybe A) → lift₂ f u nothing ≡ nothing
lift₂-nothingʳ f (just _) = refl
lift₂-nothingʳ f nothing  = refl

-- a unit of the operation is one of the lifted operation

lift₂-identityˡ : (f : A → B → B) {e : A} → (∀ b → f e b ≡ b)
                → ∀ v → lift₂ f (just e) v ≡ v
lift₂-identityˡ f id (just b) = cong just (id b)
lift₂-identityˡ f id nothing  = refl

lift₂-identityʳ : (f : A → B → A) {e : B} → (∀ a → f a e ≡ a)
                → ∀ u → lift₂ f u (just e) ≡ u
lift₂-identityʳ f id (just a) = cong just (id a)
lift₂-identityʳ f id nothing  = refl

-- an associativity law of the operations is one of the lifted ones

lift₂-assoc : ∀ {A B C AB BC ABC : Set}
              (f : A → B → AB) (g : AB → C → ABC) (f' : A → BC → ABC) (g' : B → C → BC)
            → (∀ a b c → g (f a b) c ≡ f' a (g' b c))
            → ∀ u v w → lift₂ g (lift₂ f u v) w ≡ lift₂ f' u (lift₂ g' v w)
lift₂-assoc f g f' g' as (just a) (just b) (just c) = cong just (as a b c)
lift₂-assoc f g f' g' as (just a) (just b) nothing  = refl
lift₂-assoc f g f' g' as (just a) nothing  w        = sym (lift₂-nothingʳ f' (just a))
lift₂-assoc f g f' g' as nothing  v        w        = refl

------------------------------------------------------------------------
-- The order: `nothing` below every value

module Order (_⊑_ : X → X → Set) where

  infix 4 _⊑?_

  _⊑?_ : Maybe X → Maybe X → Set
  nothing ⊑? _       = ⊤
  just _  ⊑? nothing = ⊥
  just x  ⊑? just y  = x ⊑ y

  ⊑?-nothing : ∀ u → u ⊑? nothing → u ≡ nothing
  ⊑?-nothing nothing _ = refl

  ⊑?-refl : (∀ {x} → x ⊑ x) → ∀ {u} → u ⊑? u
  ⊑?-refl r {just _} = r
  ⊑?-refl r {nothing} = tt

  ⊑?-reflexive : (∀ {x} → x ⊑ x) → ∀ {u v} → u ≡ v → u ⊑? v
  ⊑?-reflexive r {u} refl = ⊑?-refl r {u}

  ⊑?-trans : (∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z)
           → ∀ {u v w} → u ⊑? v → v ⊑? w → u ⊑? w
  ⊑?-trans t {just _} {just _} {just _} p q = t p q
  ⊑?-trans t {just _} {just _} {nothing} _ ()
  ⊑?-trans t {just _} {nothing} {_} () _
  ⊑?-trans t {nothing} _ _ = tt

  ⊑?-antisym : (∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y)
             → ∀ {u v} → u ⊑? v → v ⊑? u → u ≡ v
  ⊑?-antisym a {just _} {just _} p q = cong just (a p q)
  ⊑?-antisym a {nothing} {nothing} _ _ = refl

  ⊑?-irrelevant : (∀ {x y} (p q : x ⊑ y) → p ≡ q)
                → ∀ {u v} (p q : u ⊑? v) → p ≡ q
  ⊑?-irrelevant i {just _} {just _} p q = i p q
  ⊑?-irrelevant i {nothing} _ _ = refl

  ⊑?-dec : Decidable _⊑_ → Decidable _⊑?_
  ⊑?-dec d (just x) (just y) = d x y
  ⊑?-dec d (just _) nothing  = no λ ()
  ⊑?-dec d nothing  _        = yes tt

------------------------------------------------------------------------
-- The join: `nothing` its unit

module Join (_∨_ : X → X → X) where

  infixl 6 _∨?_

  _∨?_ : Maybe X → Maybe X → Maybe X
  nothing ∨? v       = v
  just x  ∨? nothing = just x
  just x  ∨? just y  = just (x ∨ y)

  ∨?-identityʳ : ∀ u → u ∨? nothing ≡ u
  ∨?-identityʳ (just _) = refl
  ∨?-identityʳ nothing  = refl

  -- a join is empty only when both sides are

  ∨?-nothingˡ : ∀ u v → u ∨? v ≡ nothing → u ≡ nothing
  ∨?-nothingˡ nothing  _        _ = refl
  ∨?-nothingˡ (just _) nothing  ()
  ∨?-nothingˡ (just _) (just _) ()

  ∨?-nothingʳ : ∀ u v → u ∨? v ≡ nothing → v ≡ nothing
  ∨?-nothingʳ nothing  _        e = e
  ∨?-nothingʳ (just _) nothing  ()
  ∨?-nothingʳ (just _) (just _) ()

  -- and non-empty when either side is

  ∨?-nonemptyˡ : ∀ u v → NonEmpty u → NonEmpty (u ∨? v)
  ∨?-nonemptyˡ (just _) (just _) _ = tt
  ∨?-nonemptyˡ (just _) nothing  _ = tt

  ∨?-nonemptyʳ : ∀ u v → NonEmpty v → NonEmpty (u ∨? v)
  ∨?-nonemptyʳ (just _) (just _) _ = tt
  ∨?-nonemptyʳ nothing  (just _) _ = tt

  module _ (assoc : ∀ x y z → (x ∨ y) ∨ z ≡ x ∨ (y ∨ z))
           (comm  : ∀ x y → x ∨ y ≡ y ∨ x)
           (idem  : ∀ x → x ∨ x ≡ x) where

    ∨?-assoc : ∀ u v w → (u ∨? v) ∨? w ≡ u ∨? (v ∨? w)
    ∨?-assoc (just x) (just y) (just z) = cong just (assoc x y z)
    ∨?-assoc (just x) (just y) nothing  = refl
    ∨?-assoc (just x) nothing  (just z) = refl
    ∨?-assoc (just x) nothing  nothing  = refl
    ∨?-assoc nothing  _        _        = refl

    ∨?-comm : ∀ u v → u ∨? v ≡ v ∨? u
    ∨?-comm (just x) (just y) = cong just (comm x y)
    ∨?-comm (just x) nothing  = refl
    ∨?-comm nothing  v        = sym (∨?-identityʳ v)

    ∨?-idem : ∀ u → u ∨? u ≡ u
    ∨?-idem (just x) = cong just (idem x)
    ∨?-idem nothing  = refl

    -- an idempotent commutative monoid, on the nose

    ∨?-icm : IdempotentCommutativeMonoid 0ℓ 0ℓ
    ∨?-icm = record
      { Carrier = Maybe X
      ; _≈_     = _≡_
      ; _∙_     = _∨?_
      ; ε       = nothing
      ; isIdempotentCommutativeMonoid = record
        { isCommutativeMonoid = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _∨?_ }
              ; assoc   = ∨?-assoc }
            ; identity = (λ _ → refl) , ∨?-identityʳ }
          ; comm = ∨?-comm }
        ; idem = ∨?-idem }
      }

------------------------------------------------------------------------
-- The join against the order

module JoinOrder (_⊑_ : X → X → Set) (_∨_ : X → X → X)
                 (⊑-refl : ∀ {x} → x ⊑ x)
                 (⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z)
                 (∨-ubˡ : ∀ x y → x ⊑ (x ∨ y))
                 (∨-ubʳ : ∀ x y → y ⊑ (x ∨ y))
                 (∨-lub : ∀ {x y z} → x ⊑ z → y ⊑ z → (x ∨ y) ⊑ z) where

  open Order _⊑_
  open Join _∨_

  ∨?-ubˡ : ∀ u v → u ⊑? u ∨? v
  ∨?-ubˡ (just x) (just y) = ∨-ubˡ x y
  ∨?-ubˡ (just x) nothing  = ⊑-refl
  ∨?-ubˡ nothing  _        = tt

  ∨?-ubʳ : ∀ u v → v ⊑? u ∨? v
  ∨?-ubʳ (just x) (just y) = ∨-ubʳ x y
  ∨?-ubʳ (just x) nothing  = tt
  ∨?-ubʳ nothing  v        = ⊑?-refl ⊑-refl {v}

  ∨?-lub : ∀ {u v w} → u ⊑? w → v ⊑? w → u ∨? v ⊑? w
  ∨?-lub {just _} {just _} {just _} p q = ∨-lub p q
  ∨?-lub {just _} {nothing} {just _} p _ = p
  ∨?-lub {nothing} _ q = q

  ∨?-mono : ∀ {u u' v v'} → u ⊑? u' → v ⊑? v' → u ∨? v ⊑? u' ∨? v'
  ∨?-mono {u} {u'} {v} {v'} p q =
    ∨?-lub {u} {v} {u' ∨? v'}
      (⊑?-trans ⊑-trans {u} {u'} {u' ∨? v'} p (∨?-ubˡ u' v'))
      (⊑?-trans ⊑-trans {v} {v'} {u' ∨? v'} q (∨?-ubʳ u' v'))

------------------------------------------------------------------------
-- Lifted operations against the order and the join

-- a monotone operation lifts to a monotone one

module _ {_⊑ᴬ_ : A → A → Set} {_⊑ᴮ_ : B → B → Set} {_⊑ᶜ_ : C → C → Set} where

  private
    open module OA = Order _⊑ᴬ_ using () renaming (_⊑?_ to _⊑ᴬ?_)
    open module OB = Order _⊑ᴮ_ using () renaming (_⊑?_ to _⊑ᴮ?_)
    open module OC = Order _⊑ᶜ_ using () renaming (_⊑?_ to _⊑ᶜ?_)

  lift₂-mono : (f : A → B → C)
             → (∀ {a a' b b'} → a ⊑ᴬ a' → b ⊑ᴮ b' → f a b ⊑ᶜ f a' b')
             → ∀ {u u' v v'} → u ⊑ᴬ? u' → v ⊑ᴮ? v' → lift₂ f u v ⊑ᶜ? lift₂ f u' v'
  lift₂-mono f m {just _} {just _} {just _} {just _} p q = m p q
  lift₂-mono f m {just _} {just _} {just _} {nothing} _ ()
  lift₂-mono f m {just _} {just _} {nothing} _ _ = tt
  lift₂-mono f m {just _} {nothing} () _
  lift₂-mono f m {nothing} _ _ = tt

-- an operation distributing over the join, in one argument, lifts to
-- one that does

module _ {_∨ᴬ_ : A → A → A} {_∨ᴮ_ : B → B → B} {_∨ᶜ_ : C → C → C} where

  private
    open module JA = Join _∨ᴬ_ using () renaming (_∨?_ to _∨ᴬ?_)
    open module JB = Join _∨ᴮ_ using () renaming (_∨?_ to _∨ᴮ?_)
    open module JC = Join _∨ᶜ_ using () renaming (_∨?_ to _∨ᶜ?_)

  lift₂-distribˡ : (f : A → B → C)
                 → (∀ a a' b → f (a ∨ᴬ a') b ≡ f a b ∨ᶜ f a' b)
                 → ∀ u u' v → lift₂ f (u ∨ᴬ? u') v ≡ lift₂ f u v ∨ᶜ? lift₂ f u' v
  lift₂-distribˡ f d (just a) (just a') (just b) = cong just (d a a' b)
  lift₂-distribˡ f d (just a) (just a') nothing  = refl
  lift₂-distribˡ f d (just a) nothing   v        = sym (JC.∨?-identityʳ (lift₂ f (just a) v))
  lift₂-distribˡ f d nothing  u'        v        = refl

  lift₂-distribʳ : (f : A → B → C)
                 → (∀ a b b' → f a (b ∨ᴮ b') ≡ f a b ∨ᶜ f a b')
                 → ∀ u v v' → lift₂ f u (v ∨ᴮ? v') ≡ lift₂ f u v ∨ᶜ? lift₂ f u v'
  lift₂-distribʳ f d (just a) (just b) (just b') = cong just (d a b b')
  lift₂-distribʳ f d (just a) (just b) nothing   = refl
  lift₂-distribʳ f d (just a) nothing  v'        = refl
  lift₂-distribʳ f d nothing  v        v'        = refl
