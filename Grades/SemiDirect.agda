------------------------------------------------------------------------
-- Semidirect products of a grade with a semilattice.                 --
--                                                                    --
-- A grade `M` acts on a bounded join-semilattice `N` by `act`, and   --
-- `M ⋉⟨ act ⟩ N` is the grade on `M × N` with                        --
--                                                                    --
--   (m , n) · (m' , n')  =  (m · m' , n ∨ act m n')                  --
--                                                                    --
-- the unit `(u , ⊥)`, the order, the joins and `⊤` componentwise,    --
-- and `of-dur τ = (of-dur τ , ⊥)`. The second component records      --
-- what happened, each later record seen through the first component  --
-- of what came before it.                                            --
--                                                                    --
-- The action is lawful (`Action`) when, up to the equivalence of the --
-- order,                                                             --
--                                                                    --
--   (A1) act u n ≃ n                                                 --
--   (A2) act (m · m') n ≃ act m (act m' n)                           --
--   (A3) act m ⊥ ≃ ⊥   and   act m (n ∨ n') ≃ act m n ∨ act m n'     --
--   (A4) act (m ⊔ m') n ≃ act m n ∨ act m' n                         --
--   (A5) act is monotone in each argument                            --
--   (A6) for m ≾ u, act m n ≾ ⊥ only if n ≾ ⊥                        --
--                                                                    --
-- the inequalities of A3 and A4 that follow from A5 being omitted.   --
-- The identities follow from A1 and A3, associativity from A2 and    --
-- A3, the left distributive law from A3 and the right one from A4.   --
-- A6 is exactly the right zero-product law (`zero-productʳ⇒A6`); it  --
-- holds where the unit of `M` is least (`A6-of-u-least`) and where   --
-- every `act m` reflects `⊥`.                                        --
--                                                                    --
-- Its hints declare the unit least where those of `M` do; `_·_` is   --
-- not declared to commute, and no closures are declared. The first   --
-- projection is a grade morphism onto `M`.                           --
------------------------------------------------------------------------

module Grades.SemiDirect where

open import Data.Maybe.Base using (nothing)
import Data.Maybe.Base as Maybe
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Level using (0ℓ)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Irrelevant; Decidable; Minimum)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Grades.Durations using (Duration)
open import Grades.Base
open import Grades.Hints

open import Util.Equality

------------------------------------------------------------------------
-- Bounded join-semilattices, preordered and decidable

record Semilattice : Set₁ where
  infix  4 _⊑_ _⊑?_ _≈_
  infixl 6 _∨_

  field
    Carrier : Set
    _⊑_     : Rel Carrier 0ℓ
    bot     : Carrier
    top     : Carrier
    _∨_     : Carrier → Carrier → Carrier

    -- a decidable, proof-irrelevant preorder
    ⊑-refl       : Reflexive _⊑_
    ⊑-trans      : Transitive _⊑_
    ⊑-irrelevant : Irrelevant _⊑_
    _⊑?_         : Decidable _⊑_

    -- bounded
    bot-⊑ : (n : Carrier) → bot ⊑ n
    ⊑-top : (n : Carrier) → n ⊑ top

    -- `_∨_` a binary join
    ∨-ubˡ : (n n' : Carrier) → n ⊑ n ∨ n'
    ∨-ubʳ : (n n' : Carrier) → n' ⊑ n ∨ n'
    ∨-lub : ∀ {n n' n''} → n ⊑ n'' → n' ⊑ n'' → n ∨ n' ⊑ n''

  -- the order's equivalence
  _≈_ : Rel Carrier 0ℓ
  n ≈ n' = (n ⊑ n') × (n' ⊑ n)

  ≈-refl : ∀ {n} → n ≈ n
  ≈-refl = ⊑-refl , ⊑-refl

  ≈-sym : ∀ {n n'} → n ≈ n' → n' ≈ n
  ≈-sym (p , q) = q , p

  ≈-trans : ∀ {n n' n''} → n ≈ n' → n' ≈ n'' → n ≈ n''
  ≈-trans (p , q) (p' , q') = ⊑-trans p p' , ⊑-trans q' q

  ∨-mono : ∀ {a a' b b'} → a ⊑ a' → b ⊑ b' → a ∨ b ⊑ a' ∨ b'
  ∨-mono {a' = a'} {b' = b'} p q =
    ∨-lub (⊑-trans p (∨-ubˡ a' b')) (⊑-trans q (∨-ubʳ a' b'))

  ∨-cong : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → a ∨ b ≈ a' ∨ b'
  ∨-cong (p , p') (q , q') = ∨-mono p q , ∨-mono p' q'

  ∨-assoc : (a b c : Carrier) → (a ∨ b) ∨ c ≈ a ∨ (b ∨ c)
  ∨-assoc a b c =
      ∨-lub (∨-mono ⊑-refl (∨-ubˡ b c))
            (⊑-trans (∨-ubʳ b c) (∨-ubʳ a (b ∨ c)))
    , ∨-lub (⊑-trans (∨-ubˡ a b) (∨-ubˡ (a ∨ b) c))
            (∨-mono (∨-ubʳ a b) ⊑-refl)

------------------------------------------------------------------------
-- Actions of a grade on a semilattice

module _ {D : Duration} (M : Grade D) (N : Semilattice) where

  private
    module M = Grade M
    module N = Semilattice N
  open M using (_·_; u; _≾_; _⊔_)
  open N using (_⊑_; _≈_; bot; _∨_)

  record Action : Set where
    field
      act : M.Carrier → N.Carrier → N.Carrier

      -- (A1), (A2): a monoid action
      act-identity : ∀ n → act u n ≈ n
      act-comp     : ∀ m m' n → act (m · m') n ≈ act m (act m' n)

      -- (A3): by maps of bounded join-semilattices
      act-bot : ∀ m → act m bot ⊑ bot
      act-∨   : ∀ m n n' → act m (n ∨ n') ⊑ act m n ∨ act m n'

      -- (A4): preserving the joins of `M`
      act-⊔ : ∀ m m' n → act (m ⊔ m') n ⊑ act m n ∨ act m' n

      -- (A5): monotone in each argument
      act-monoˡ : ∀ {m m' n} → m ≾ m' → act m n ⊑ act m' n
      act-monoʳ : ∀ {m n n'} → n ⊑ n' → act m n ⊑ act m n'

      -- (A6): grades below the unit reflect `⊥`
      act-reflects-bot : ∀ {m n} → m ≾ u → act m n ⊑ bot → n ⊑ bot

    -- the converses of (A3)
    act-bot-≈ : ∀ m → act m bot ≈ bot
    act-bot-≈ m = act-bot m , N.bot-⊑ (act m bot)

    act-∨-≈ : ∀ m n n' → act m (n ∨ n') ≈ act m n ∨ act m n'
    act-∨-≈ m n n' =
      act-∨ m n n' , N.∨-lub (act-monoʳ (N.∨-ubˡ n n')) (act-monoʳ (N.∨-ubʳ n n'))

  -- (A6) holds where the unit is least, given (A1) and (A5)

  A6-of-u-least : Minimum _≾_ u
                → (act : M.Carrier → N.Carrier → N.Carrier)
                → (∀ n → act u n ≈ n)
                → (∀ {m m' n} → m ≾ m' → act m n ⊑ act m' n)
                → ∀ {m n} → m ≾ u → act m n ⊑ bot → n ⊑ bot
  A6-of-u-least least act ident monoˡ {m} {n} _ q =
    N.⊑-trans (proj₂ (ident n)) (N.⊑-trans (monoˡ (least m)) q)

------------------------------------------------------------------------
-- The operations on pairs, for any map `act`

module Pairs {D : Duration} (M : Grade D) (N : Semilattice)
             (act : Grade.Carrier M → Semilattice.Carrier N → Semilattice.Carrier N) where

  private
    module M = Grade M
    module N = Semilattice N

  infixl 7 _·ˢ_
  infix  5 _≾ˢ_

  _·ˢ_ : M.Carrier × N.Carrier → M.Carrier × N.Carrier → M.Carrier × N.Carrier
  (m , n) ·ˢ (m' , n') = (m M.· m' , n N.∨ act m n')

  uˢ : M.Carrier × N.Carrier
  uˢ = (M.u , N.bot)

  _≾ˢ_ : M.Carrier × N.Carrier → M.Carrier × N.Carrier → Set
  (m , n) ≾ˢ (m' , n') = (m M.≾ m') × (n N.⊑ n')

  -- (A6) is necessary for the right zero-product law

  zero-productʳ⇒A6 : (∀ {c d} → c ·ˢ d ≾ˢ uˢ → d ≾ˢ uˢ)
                   → ∀ {m n} → m M.≾ M.u → act m n N.⊑ N.bot → n N.⊑ N.bot
  zero-productʳ⇒A6 zp {m} {n} p q =
    proj₂ (zp {m , N.bot} {M.u , n}
               (M.≾-trans (proj₁ (M.·-identityʳ m)) p , N.∨-lub (N.bot-⊑ N.bot) q))

------------------------------------------------------------------------
-- The semidirect product

semidirect : {D : Duration} (M : Grade D) (N : Semilattice) → Action M N → Grade D
syntax semidirect M N A = M ⋉⟨ A ⟩ N
semidirect M N A = record
  { Carrier         = M.Carrier × N.Carrier
  ; _·_             = _·ˢ_
  ; u               = uˢ
  ; _≾_             = _≾ˢ_
  ; ⊤               = (M.⊤ , N.top)
  ; _⊔_             = λ (m , n) (m' , n') → (m M.⊔ m' , n N.∨ n')
  ; of-dur          = λ τ → (M.of-dur τ , N.bot)
  ; ·-identityˡ     = λ (m , n) →
      pair (M.·-identityˡ m)
           (N.∨-lub (N.bot-⊑ n) (proj₁ (act-identity n))
           , N.⊑-trans (proj₂ (act-identity n)) (N.∨-ubʳ N.bot (act M.u n)))
  ; ·-identityʳ     = λ (m , n) →
      pair (M.·-identityʳ m)
           (N.∨-lub N.⊑-refl (N.⊑-trans (act-bot m) (N.bot-⊑ n)) , N.∨-ubˡ n (act m N.bot))
  ; ·-assoc         = λ (m , n) (m' , n') (m'' , n'') →
      pair (M.·-assoc m m' m'')
           (N.≈-trans (N.∨-cong N.≈-refl (act-comp m m' n''))
             (N.≈-trans (N.∨-assoc n (act m n') (act m (act m' n'')))
               (N.∨-cong N.≈-refl (N.≈-sym (act-∨-≈ m n' (act m' n''))))))
  ; ≾-refl          = M.≾-refl , N.⊑-refl
  ; ≾-trans         = λ (p , q) (p' , q') → M.≾-trans p p' , N.⊑-trans q q'
  ; ≾-irrelevant    = λ (p , q) (p' , q') →
                        cong₂ _,_ (M.≾-irrelevant p p') (N.⊑-irrelevant q q')
  ; _≾?_            = λ (m , n) (m' , n') → (m M.≾? m') ×-dec (n N.⊑? n')
  ; ≾-⊤             = λ (m , n) → M.≾-⊤ m , N.⊑-top n
  ; ⊔-ubˡ           = λ (m , n) (m' , n') → M.⊔-ubˡ m m' , N.∨-ubˡ n n'
  ; ⊔-ubʳ           = λ (m , n) (m' , n') → M.⊔-ubʳ m m' , N.∨-ubʳ n n'
  ; ⊔-lub           = λ (p , q) (p' , q') → M.⊔-lub p p' , N.∨-lub q q'
  ; ·-monoˡ-≾       = λ (p , q) → M.·-monoˡ-≾ p , N.∨-mono q (act-monoˡ p)
  ; ·-monoʳ-≾       = λ (p , q) → M.·-monoʳ-≾ p , N.∨-mono N.⊑-refl (act-monoʳ q)
  ; ·-distribˡ-⊔-≾  = λ (m , n) (m' , n') (m'' , n'') →
        M.·-distribˡ-⊔-≾ m m' m''
      , N.∨-lub (N.⊑-trans (N.∨-ubˡ n (act m n')) (N.∨-ubˡ _ _))
                (N.⊑-trans (act-∨ m n' n'')
                           (N.∨-mono (N.∨-ubʳ n (act m n')) (N.∨-ubʳ n (act m n''))))
  ; ·-distribʳ-⊔-≾  = λ (m , n) (m' , n') (m'' , n'') →
        M.·-distribʳ-⊔-≾ m m' m''
      , N.∨-lub (N.∨-mono (N.∨-ubˡ n' (act m' n)) (N.∨-ubˡ n'' (act m'' n)))
                (N.⊑-trans (act-⊔ m' m'' n)
                           (N.∨-mono (N.∨-ubʳ n' (act m' n)) (N.∨-ubʳ n'' (act m'' n))))
  ; ≾-zero-productˡ = λ (p , q) → M.≾-zero-productˡ p , N.⊑-trans (N.∨-ubˡ _ _) q
  ; ≾-zero-productʳ = λ (p , q) →
        M.≾-zero-productʳ p
      , act-reflects-bot (M.≾-zero-productˡ p) (N.⊑-trans (N.∨-ubʳ _ _) q)
  ; of-dur-zero     = pair M.of-dur-zero N.≈-refl
  ; of-dur-plus     = pair M.of-dur-plus (N.bot-⊑ _ , N.∨-lub N.⊑-refl (act-bot _))
  }
  where
    module M = Grade M
    module N = Semilattice N
    open Action A
    open Pairs M N act
    pair : ∀ {m m' n n'} → m M.≃ m' → n N.≈ n'
         → ((m M.≾ m') × (n N.⊑ n')) × ((m' M.≾ m) × (n' N.⊑ n))
    pair (p , p') (q , q') = (p , q) , (p' , q')

-- its hints, from those of `M`

semidirectʰ : {D : Duration} {M : Grade D} → GradeHints M
            → (N : Semilattice) (A : Action M N) → GradeHints (M ⋉⟨ A ⟩ N)
semidirectʰ H N A = record
  { u-least? = Maybe.map (λ l (m , n) → l m , Semilattice.bot-⊑ N n) (GradeHints.u-least? H)
  ; ·-comm?  = nothing
  ; plus?    = λ _ → nothing
  }

------------------------------------------------------------------------
-- The first projection

module _ {D : Duration} {M : Grade D} {N : Semilattice} {A : Action M N} where

  π₁ˢ : (M ⋉⟨ A ⟩ N) →ᵍ M
  π₁ˢ = record
    { map          = proj₁
    ; map-monotone = proj₁
    ; map-u        = Grade.≃-refl M
    ; map-·        = Grade.≃-refl M
    ; map-⊤        = Grade.≃-refl M
    ; map-⊔        = Grade.≃-refl M
    ; map-of-dur   = Grade.≃-refl M
    }
