------------------------------------------------------------------------
-- Security levels as grades.                                           --
--                                                                     --
-- A decidable bounded join-semilattice of levels is a grade: `_·_` and --
-- `_⊔_` are both the join, the unit is the least level and `⊤` the     --
-- greatest. Time does not raise a level, so `of-nat` is constantly the --
-- least one. The unit is least and `_·_` commutes, and both are        --
-- declared.                                                            --
--                                                                     --
-- The level is a floating label, as in LIO. A computation's effect     --
-- grade is the highest level it has touched (for taint sets, the set   --
-- of labels). A lock `⟨ ℓ ⟩` joins `ℓ` into the label, and `[ ℓ ] A`    --
-- can be unboxed only while the label raised since boxing is `≾ ℓ`: a  --
-- `Low`-boxed public channel is unusable once `High` data has been     --
-- touched, so there is no write-down after read-up. A variable that is --
-- not eternal needs the locks to its right to be `≾` the unit, so it   --
-- goes stale after any `High` activity.                                --
--                                                                     --
-- Instances: the two-point `Low < High`, and sets of taint labels over --
-- `Fin n`, the `n`-fold power of the two-point lattice, represented as --
-- vectors so that antisymmetry is propositional equality.              --
------------------------------------------------------------------------

module Syntax.Grades.Example.SecurityLevel where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_; replicate)

open import Level using (0ℓ)

open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Irrelevant; Decidable)
open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades using (Grade)

open import Util.Equality

------------------------------------------------------------------------
-- Decidable bounded join-semilattices

record LevelLattice : Set₁ where
  infix  4 _⊑_ _⊑?_
  infixl 6 _∨_

  field
    Carrier : Set
    _⊑_     : Rel Carrier 0ℓ
    bot     : Carrier
    top     : Carrier
    _∨_     : Carrier → Carrier → Carrier

    -- a decidable, proof-irrelevant partial order
    ⊑-refl       : Reflexive _⊑_
    ⊑-trans      : Transitive _⊑_
    ⊑-antisym    : ∀ {ℓ ℓ'} → ℓ ⊑ ℓ' → ℓ' ⊑ ℓ → ℓ ≡ ℓ'
    ⊑-irrelevant : Irrelevant _⊑_
    _⊑?_         : Decidable _⊑_

    -- bounded
    bot-⊑ : (ℓ : Carrier) → bot ⊑ ℓ
    ⊑-top : (ℓ : Carrier) → ℓ ⊑ top

    -- `_∨_` a binary join
    ∨-ubˡ : (ℓ ℓ' : Carrier) → ℓ ⊑ ℓ ∨ ℓ'
    ∨-ubʳ : (ℓ ℓ' : Carrier) → ℓ' ⊑ ℓ ∨ ℓ'
    ∨-lub : ∀ {ℓ ℓ' ℓ''} → ℓ ⊑ ℓ'' → ℓ' ⊑ ℓ'' → ℓ ∨ ℓ' ⊑ ℓ''

------------------------------------------------------------------------
-- A lattice of levels as a grade

module _ (L : LevelLattice) where

  open LevelLattice L

  private

    ∨-mono : ∀ {a a' b b'} → a ⊑ a' → b ⊑ b' → a ∨ b ⊑ a' ∨ b'
    ∨-mono {a' = a'} {b' = b'} p q =
      ∨-lub (⊑-trans p (∨-ubˡ a' b')) (⊑-trans q (∨-ubʳ a' b'))

    ∨-identityˡ : (a : Carrier) → bot ∨ a ≡ a
    ∨-identityˡ a = ⊑-antisym (∨-lub (bot-⊑ a) ⊑-refl) (∨-ubʳ bot a)

    ∨-identityʳ : (a : Carrier) → a ∨ bot ≡ a
    ∨-identityʳ a = ⊑-antisym (∨-lub ⊑-refl (bot-⊑ a)) (∨-ubˡ a bot)

    ∨-assoc : (a b c : Carrier) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
    ∨-assoc a b c =
      ⊑-antisym
        (∨-lub (∨-mono ⊑-refl (∨-ubˡ b c))
               (⊑-trans (∨-ubʳ b c) (∨-ubʳ a (b ∨ c))))
        (∨-lub (⊑-trans (∨-ubˡ a b) (∨-ubˡ (a ∨ b) c))
               (∨-mono (∨-ubʳ a b) ⊑-refl))

    ∨-comm : (a b : Carrier) → a ∨ b ≡ b ∨ a
    ∨-comm a b = ⊑-antisym (∨-lub (∨-ubʳ b a) (∨-ubˡ b a))
                           (∨-lub (∨-ubʳ a b) (∨-ubˡ a b))

    ∨-distribˡ : (a b c : Carrier) → a ∨ (b ∨ c) ⊑ (a ∨ b) ∨ (a ∨ c)
    ∨-distribˡ a b c =
      ∨-lub (⊑-trans (∨-ubˡ a b) (∨-ubˡ (a ∨ b) (a ∨ c)))
            (∨-mono (∨-ubʳ a b) (∨-ubʳ a c))

    ∨-distribʳ : (a b c : Carrier) → (b ∨ c) ∨ a ⊑ (b ∨ a) ∨ (c ∨ a)
    ∨-distribʳ a b c =
      ∨-lub (∨-mono (∨-ubˡ b a) (∨-ubˡ c a))
            (⊑-trans (∨-ubʳ b a) (∨-ubˡ (b ∨ a) (c ∨ a)))

  level-grade : Grade
  level-grade = record
    { Carrier         = Carrier
    ; _·_             = _∨_
    ; u               = bot
    ; _≾_             = _⊑_
    ; ⊤               = top
    ; _⊔_             = _∨_
    ; of-nat          = λ _ → bot
    ; ·-identityˡ     = ∨-identityˡ
    ; ·-identityʳ     = ∨-identityʳ
    ; ·-assoc         = ∨-assoc
    ; ≾-refl          = ⊑-refl
    ; ≾-trans         = ⊑-trans
    ; ≾-antisym       = ⊑-antisym
    ; ≾-irrelevant    = ⊑-irrelevant
    ; _≾?_            = _⊑?_
    ; ≾-⊤             = ⊑-top
    ; ⊔-ubˡ           = ∨-ubˡ
    ; ⊔-ubʳ           = ∨-ubʳ
    ; ⊔-lub           = ∨-lub
    ; ·-monoˡ-≾       = λ p → ∨-mono p ⊑-refl
    ; ·-monoʳ-≾       = λ p → ∨-mono ⊑-refl p
    ; ·-distribˡ-⊔-≾  = ∨-distribˡ
    ; ·-distribʳ-⊔-≾  = ∨-distribʳ
    ; ≾-zero-productˡ = λ {a} {b} p → ⊑-trans (∨-ubˡ a b) p
    ; ≾-zero-productʳ = λ {a} {b} p → ⊑-trans (∨-ubʳ a b) p
    ; of-nat-zero     = refl
    ; of-nat-plus     = sym (∨-identityˡ bot)
    ; u-least?        = just bot-⊑
    ; ·-comm?         = just ∨-comm
    }

------------------------------------------------------------------------
-- The two-point lattice `Low < High`

data LowHigh : Set where
  Low High : LowHigh

infix 4 _⊑ₗₕ_

data _⊑ₗₕ_ : LowHigh → LowHigh → Set where
  Low⊑  : ∀ {ℓ} → Low ⊑ₗₕ ℓ
  High⊑ : High ⊑ₗₕ High

infixl 6 _∨ₗₕ_

_∨ₗₕ_ : LowHigh → LowHigh → LowHigh
Low  ∨ₗₕ ℓ = ℓ
High ∨ₗₕ _ = High

low-high : LevelLattice
low-high = record
  { Carrier      = LowHigh
  ; _⊑_          = _⊑ₗₕ_
  ; bot          = Low
  ; top          = High
  ; _∨_          = _∨ₗₕ_
  ; ⊑-refl       = λ { {Low} → Low⊑ ; {High} → High⊑ }
  ; ⊑-trans      = λ { Low⊑ _ → Low⊑ ; High⊑ q → q }
  ; ⊑-antisym    = λ { Low⊑ Low⊑ → refl ; High⊑ _ → refl }
  ; ⊑-irrelevant = λ { Low⊑ Low⊑ → refl ; High⊑ High⊑ → refl }
  ; _⊑?_         = λ { Low _ → yes Low⊑
                     ; High Low → no λ ()
                     ; High High → yes High⊑ }
  ; bot-⊑        = λ _ → Low⊑
  ; ⊑-top        = λ { Low → Low⊑ ; High → High⊑ }
  ; ∨-ubˡ        = λ { Low _ → Low⊑ ; High _ → High⊑ }
  ; ∨-ubʳ        = λ { Low Low → Low⊑ ; Low High → High⊑ ; High Low → Low⊑
                     ; High High → High⊑ }
  ; ∨-lub        = λ { Low⊑ q → q ; High⊑ _ → High⊑ }
  }

two-point-levels : Grade
two-point-levels = level-grade low-high

------------------------------------------------------------------------
-- Powers: `n`-tuples of levels, ordered and joined pointwise

module Power (L : LevelLattice) where

  open LevelLattice L

  infix 4 _⊑ⱽ_

  data _⊑ⱽ_ : ∀ {n} → Vec Carrier n → Vec Carrier n → Set where
    []  : [] ⊑ⱽ []
    _∷_ : ∀ {n a b} {as bs : Vec Carrier n}
        → a ⊑ b → as ⊑ⱽ bs → (a ∷ as) ⊑ⱽ (b ∷ bs)

  infixl 6 _∨ⱽ_

  _∨ⱽ_ : ∀ {n} → Vec Carrier n → Vec Carrier n → Vec Carrier n
  []       ∨ⱽ []       = []
  (a ∷ as) ∨ⱽ (b ∷ bs) = a ∨ b ∷ as ∨ⱽ bs

  ⊑ⱽ-refl : ∀ {n} {as : Vec Carrier n} → as ⊑ⱽ as
  ⊑ⱽ-refl {as = []}    = []
  ⊑ⱽ-refl {as = _ ∷ _} = ⊑-refl ∷ ⊑ⱽ-refl

  ⊑ⱽ-trans : ∀ {n} {as bs cs : Vec Carrier n} → as ⊑ⱽ bs → bs ⊑ⱽ cs → as ⊑ⱽ cs
  ⊑ⱽ-trans []       []       = []
  ⊑ⱽ-trans (p ∷ ps) (q ∷ qs) = ⊑-trans p q ∷ ⊑ⱽ-trans ps qs

  ⊑ⱽ-antisym : ∀ {n} {as bs : Vec Carrier n} → as ⊑ⱽ bs → bs ⊑ⱽ as → as ≡ bs
  ⊑ⱽ-antisym []       []       = refl
  ⊑ⱽ-antisym (p ∷ ps) (q ∷ qs) = cong₂ _∷_ (⊑-antisym p q) (⊑ⱽ-antisym ps qs)

  ⊑ⱽ-irrelevant : ∀ {n} → Irrelevant (_⊑ⱽ_ {n})
  ⊑ⱽ-irrelevant []       []       = refl
  ⊑ⱽ-irrelevant (p ∷ ps) (q ∷ qs) =
    cong₂ _∷_ (⊑-irrelevant p q) (⊑ⱽ-irrelevant ps qs)

  _⊑ⱽ?_ : ∀ {n} → Decidable (_⊑ⱽ_ {n})
  []       ⊑ⱽ? []       = yes []
  (a ∷ as) ⊑ⱽ? (b ∷ bs) with a ⊑? b | as ⊑ⱽ? bs
  ... | yes p | yes ps = yes (p ∷ ps)
  ... | no ¬p | _      = no λ { (p ∷ _) → ¬p p }
  ... | yes _ | no ¬ps = no λ { (_ ∷ ps) → ¬ps ps }

  bot-⊑ⱽ : ∀ {n} (as : Vec Carrier n) → replicate n bot ⊑ⱽ as
  bot-⊑ⱽ []       = []
  bot-⊑ⱽ (a ∷ as) = bot-⊑ a ∷ bot-⊑ⱽ as

  ⊑ⱽ-top : ∀ {n} (as : Vec Carrier n) → as ⊑ⱽ replicate n top
  ⊑ⱽ-top []       = []
  ⊑ⱽ-top (a ∷ as) = ⊑-top a ∷ ⊑ⱽ-top as

  ∨ⱽ-ubˡ : ∀ {n} (as bs : Vec Carrier n) → as ⊑ⱽ as ∨ⱽ bs
  ∨ⱽ-ubˡ []       []       = []
  ∨ⱽ-ubˡ (a ∷ as) (b ∷ bs) = ∨-ubˡ a b ∷ ∨ⱽ-ubˡ as bs

  ∨ⱽ-ubʳ : ∀ {n} (as bs : Vec Carrier n) → bs ⊑ⱽ as ∨ⱽ bs
  ∨ⱽ-ubʳ []       []       = []
  ∨ⱽ-ubʳ (a ∷ as) (b ∷ bs) = ∨-ubʳ a b ∷ ∨ⱽ-ubʳ as bs

  ∨ⱽ-lub : ∀ {n} {as bs cs : Vec Carrier n}
         → as ⊑ⱽ cs → bs ⊑ⱽ cs → as ∨ⱽ bs ⊑ⱽ cs
  ∨ⱽ-lub []       []       = []
  ∨ⱽ-lub (p ∷ ps) (q ∷ qs) = ∨-lub p q ∷ ∨ⱽ-lub ps qs

  power : ℕ → LevelLattice
  power n = record
    { Carrier      = Vec Carrier n
    ; _⊑_          = _⊑ⱽ_
    ; bot          = replicate n bot
    ; top          = replicate n top
    ; _∨_          = _∨ⱽ_
    ; ⊑-refl       = ⊑ⱽ-refl
    ; ⊑-trans      = ⊑ⱽ-trans
    ; ⊑-antisym    = ⊑ⱽ-antisym
    ; ⊑-irrelevant = ⊑ⱽ-irrelevant
    ; _⊑?_         = _⊑ⱽ?_
    ; bot-⊑        = bot-⊑ⱽ
    ; ⊑-top        = ⊑ⱽ-top
    ; ∨-ubˡ        = ∨ⱽ-ubˡ
    ; ∨-ubʳ        = ∨ⱽ-ubʳ
    ; ∨-lub        = ∨ⱽ-lub
    }

------------------------------------------------------------------------
-- Sets of taint labels over `Fin n`
--
-- A subset of `Fin n` is its characteristic vector: `High` at the
-- labels it contains. Inclusion is the pointwise order and union the
-- pointwise join.

TaintSet : ℕ → Set
TaintSet n = Vec LowHigh n

taint-lattice : ℕ → LevelLattice
taint-lattice = Power.power low-high

taint-sets : ℕ → Grade
taint-sets n = level-grade (taint-lattice n)

-- the empty set and the singletons

∅ᵗ : ∀ {n} → TaintSet n
∅ᵗ {n} = replicate n Low

label : ∀ {n} → Fin n → TaintSet n
label zero    = High ∷ ∅ᵗ
label (suc i) = Low ∷ label i

infixl 6 _∪ᵗ_

_∪ᵗ_ : ∀ {n} → TaintSet n → TaintSet n → TaintSet n
_∪ᵗ_ = Power._∨ⱽ_ low-high

