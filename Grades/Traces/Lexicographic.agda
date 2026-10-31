------------------------------------------------------------------------
-- A strict total order on timed traces.                              --
--                                                                    --
-- Traces are compared lexicographically: first by which constructor  --
-- heads them, with `ε` below an operation and an operation below a   --
-- delay, and then, on a common head, by the operation symbol or the  --
-- delay's duration and finally by the continuation. The delay-free   --
-- traces `Trace⁻` are ordered by the same scheme, and the two orders --
-- are mutually recursive because the two types are.                  --
--                                                                    --
-- It orders the syntax and is unrelated to the orders of             --
-- `Traces.Order`: it fixes an enumeration of the runs and says       --
-- nothing about how one run relates to another.                      --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Decidable; Transitive; Trichotomous; tri<; tri≈; tri>)

open import Util.Equality

-- the order on traces is built from one on the alphabet

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Lexicographic
  {D : Duration} (T : TimeDomain D) (Op : Set) (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_) where

open import Relation.Nullary using (Dec; yes; no)

open import Grades.Traces.Base T Op

------------------------------------------------------------------------
-- The order

infix 4 _<ᵀ_ _<ᵀ⁻_

mutual

  data _<ᵀ_ : Rel Trace lzero where
    ε<op     : ∀ {o t}        → ε <ᵀ operation o t
    ε<del    : ∀ {d t}        → ε <ᵀ delay d t
    op<del   : ∀ {o s d t}    → operation o s <ᵀ delay d t
    op-head  : ∀ {o o' s s'}  → o <ᵒ o'  → operation o s <ᵀ operation o' s'
    op-tail  : ∀ {o s s'}     → s <ᵀ s'  → operation o s <ᵀ operation o s'
    del-head : ∀ {d d' s s'}  → d <⁺ d'  → delay d s <ᵀ delay d' s'
    del-tail : ∀ {d s s'}     → s <ᵀ⁻ s' → delay d s <ᵀ delay d s'

  data _<ᵀ⁻_ : Rel Trace⁻ lzero where
    ε⁻<op⁻    : ∀ {o t}       → ε⁻ <ᵀ⁻ operation⁻ o t
    op⁻-head  : ∀ {o o' s s'} → o <ᵒ o' → operation⁻ o s <ᵀ⁻ operation⁻ o' s'
    op⁻-tail  : ∀ {o s s'}    → s <ᵀ s' → operation⁻ o s <ᵀ⁻ operation⁻ o s'

------------------------------------------------------------------------
-- Transitivity

mutual

  <ᵀ-trans : Transitive _<ᵀ_
  <ᵀ-trans ε<op          op<del         = ε<del
  <ᵀ-trans ε<op          (op-head _)    = ε<op
  <ᵀ-trans ε<op          (op-tail _)    = ε<op
  <ᵀ-trans ε<del         (del-head _)   = ε<del
  <ᵀ-trans ε<del         (del-tail _)   = ε<del
  <ᵀ-trans op<del        (del-head _)   = op<del
  <ᵀ-trans op<del        (del-tail _)   = op<del
  <ᵀ-trans (op-head _)   op<del         = op<del
  <ᵀ-trans (op-head p)   (op-head q)    = op-head (<ᵒ-trans p q)
  <ᵀ-trans (op-head p)   (op-tail _)    = op-head p
  <ᵀ-trans (op-tail _)   op<del         = op<del
  <ᵀ-trans (op-tail _)   (op-head q)    = op-head q
  <ᵀ-trans (op-tail p)   (op-tail q)    = op-tail (<ᵀ-trans p q)
  <ᵀ-trans (del-head p)  (del-head q)   = del-head (<⁺-trans p q)
  <ᵀ-trans (del-head p)  (del-tail _)   = del-head p
  <ᵀ-trans (del-tail _)  (del-head q)   = del-head q
  <ᵀ-trans (del-tail p)  (del-tail q)   = del-tail (<ᵀ⁻-trans p q)

  <ᵀ⁻-trans : Transitive _<ᵀ⁻_
  <ᵀ⁻-trans ε⁻<op⁻       (op⁻-head _)   = ε⁻<op⁻
  <ᵀ⁻-trans ε⁻<op⁻       (op⁻-tail _)   = ε⁻<op⁻
  <ᵀ⁻-trans (op⁻-head p) (op⁻-head q)   = op⁻-head (<ᵒ-trans p q)
  <ᵀ⁻-trans (op⁻-head p) (op⁻-tail _)   = op⁻-head p
  <ᵀ⁻-trans (op⁻-tail _) (op⁻-head q)   = op⁻-head q
  <ᵀ⁻-trans (op⁻-tail p) (op⁻-tail q)   = op⁻-tail (<ᵀ-trans p q)

------------------------------------------------------------------------
-- Trichotomy

mutual

  <ᵀ-cmp : Trichotomous _≡_ _<ᵀ_
  <ᵀ-cmp ε               ε               = tri≈ (λ ()) refl (λ ())
  <ᵀ-cmp ε               (operation _ _) = tri< ε<op (λ ()) (λ ())
  <ᵀ-cmp ε               (delay _ _)     = tri< ε<del (λ ()) (λ ())
  <ᵀ-cmp (operation _ _) ε               = tri> (λ ()) (λ ()) ε<op
  <ᵀ-cmp (operation _ _) (delay _ _)     = tri< op<del (λ ()) (λ ())
  <ᵀ-cmp (delay _ _)     ε               = tri> (λ ()) (λ ()) ε<del
  <ᵀ-cmp (delay _ _)     (operation _ _) = tri> (λ ()) (λ ()) op<del

  <ᵀ-cmp (operation o s) (operation o' s') with <ᵒ-cmp o o'
  ... | tri< p ¬q ¬r =
          tri< (op-head p)
               (λ { refl → ¬q refl })
               (λ { (op-head r) → ¬r r ; (op-tail _) → ¬q refl })
  ... | tri> ¬p ¬q r =
          tri> (λ { (op-head p) → ¬p p ; (op-tail _) → ¬q refl })
               (λ { refl → ¬q refl })
               (op-head r)
  ... | tri≈ ¬p refl ¬r with <ᵀ-cmp s s'
  ...   | tri< p' ¬q' ¬r' =
            tri< (op-tail p')
                 (λ { refl → ¬q' refl })
                 (λ { (op-head r) → ¬r r ; (op-tail r) → ¬r' r })
  ...   | tri≈ ¬p' refl ¬r' =
            tri≈ (λ { (op-head p) → ¬p p ; (op-tail p) → ¬p' p })
                 refl
                 (λ { (op-head r) → ¬r r ; (op-tail r) → ¬r' r })
  ...   | tri> ¬p' ¬q' r' =
            tri> (λ { (op-head p) → ¬p p ; (op-tail p) → ¬p' p })
                 (λ { refl → ¬q' refl })
                 (op-tail r')

  <ᵀ-cmp (delay d s)     (delay d' s')   with <⁺-cmp d d'
  ... | tri< p ¬q ¬r =
          tri< (del-head p)
               (λ { refl → ¬q refl })
               (λ { (del-head r) → ¬r r ; (del-tail _) → ¬q refl })
  ... | tri> ¬p ¬q r =
          tri> (λ { (del-head p) → ¬p p ; (del-tail _) → ¬q refl })
               (λ { refl → ¬q refl })
               (del-head r)
  ... | tri≈ ¬p refl ¬r with <ᵀ⁻-cmp s s'
  ...   | tri< p' ¬q' ¬r' =
            tri< (del-tail p')
                 (λ { refl → ¬q' refl })
                 (λ { (del-head r) → ¬r r ; (del-tail r) → ¬r' r })
  ...   | tri≈ ¬p' refl ¬r' =
            tri≈ (λ { (del-head p) → ¬p p ; (del-tail p) → ¬p' p })
                 refl
                 (λ { (del-head r) → ¬r r ; (del-tail r) → ¬r' r })
  ...   | tri> ¬p' ¬q' r' =
            tri> (λ { (del-head p) → ¬p p ; (del-tail p) → ¬p' p })
                 (λ { refl → ¬q' refl })
                 (del-tail r')

  <ᵀ⁻-cmp : Trichotomous _≡_ _<ᵀ⁻_
  <ᵀ⁻-cmp ε⁻              ε⁻               = tri≈ (λ ()) refl (λ ())
  <ᵀ⁻-cmp ε⁻              (operation⁻ _ _) = tri< ε⁻<op⁻ (λ ()) (λ ())
  <ᵀ⁻-cmp (operation⁻ _ _) ε⁻              = tri> (λ ()) (λ ()) ε⁻<op⁻

  <ᵀ⁻-cmp (operation⁻ o s) (operation⁻ o' s') with <ᵒ-cmp o o'
  ... | tri< p ¬q ¬r =
          tri< (op⁻-head p)
               (λ { refl → ¬q refl })
               (λ { (op⁻-head r) → ¬r r ; (op⁻-tail _) → ¬q refl })
  ... | tri> ¬p ¬q r =
          tri> (λ { (op⁻-head p) → ¬p p ; (op⁻-tail _) → ¬q refl })
               (λ { refl → ¬q refl })
               (op⁻-head r)
  ... | tri≈ ¬p refl ¬r with <ᵀ-cmp s s'
  ...   | tri< p' ¬q' ¬r' =
            tri< (op⁻-tail p')
                 (λ { refl → ¬q' refl })
                 (λ { (op⁻-head r) → ¬r r ; (op⁻-tail r) → ¬r' r })
  ...   | tri≈ ¬p' refl ¬r' =
            tri≈ (λ { (op⁻-head p) → ¬p p ; (op⁻-tail p) → ¬p' p })
                 refl
                 (λ { (op⁻-head r) → ¬r r ; (op⁻-tail r) → ¬r' r })
  ...   | tri> ¬p' ¬q' r' =
            tri> (λ { (op⁻-head p) → ¬p p ; (op⁻-tail p) → ¬p' p })
                 (λ { refl → ¬q' refl })
                 (op⁻-tail r')

------------------------------------------------------------------------
-- Decidability
--
-- Read off trichotomy, which decides all three comparisons at once.

_<ᵀ?_ : Decidable _<ᵀ_
s <ᵀ? t with <ᵀ-cmp s t
... | tri< p _  _ = yes p
... | tri≈ ¬p _ _ = no ¬p
... | tri> ¬p _ _ = no ¬p

_<ᵀ⁻?_ : Decidable _<ᵀ⁻_
s <ᵀ⁻? t with <ᵀ⁻-cmp s t
... | tri< p _  _ = yes p
... | tri≈ ¬p _ _ = no ¬p
... | tri> ¬p _ _ = no ¬p
