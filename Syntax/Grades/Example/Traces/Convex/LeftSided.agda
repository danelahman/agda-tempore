------------------------------------------------------------------------
-- Sets of timed traces, ordered by the convex (Egli-Milner) lift of   --
-- the sub-trace preorder:                                             --
--                                                                     --
--   P ≾ Q   iff   every trace of Q fits inside some trace of P        --
--            and  every trace of P has some trace of Q inside it.     --
--                                                                     --
-- The first conjunct is `Subtrace.LeftSided`'s order, the floor        --
-- proper; the second is its Smyth partner, which additionally caps how --
-- far the two sets may drift apart. Weakening a grade may therefore    --
-- ask for less only between traces already present: the extremes are   --
-- exact.                                                               --
--                                                                     --
-- As in `Subtrace.LeftSided`, a grade is read as a lower bound on      --
-- what must have happened, so that `unbox`'s premise `ρ' ≾ᵣ ρ` admits --
-- a run that does more than `ρ` asks for and never one that does less. --
--                                                                     --
-- This is a floor only: it does not bound a run from above, both       --
-- halves orienting `_≼_` the same way and differing only in which set  --
-- the quantifier runs over, so a run that does far more than `Q` asks  --
-- for is still admitted. What the extra half buys is that every listed --
-- demand be achievable by a run already present, so weakening may fill --
-- in between demands but not extend past them. `Convex.RightSided` is  --
-- the mirror image, and `Convex.TwoSided` pairs the two.               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Convex.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.Nat.Properties using (n≤0⇒n≡0)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness; _×-dec_)

open import Syntax.Grades

-- the timed-trace monoid, the sub-trace preorder, and both of its lifts
-- to sets of traces are shared with the Smyth-ordered sets of traces

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op cost
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost

open WithDecEq _≟ₒ_ using (_≟ᴺ_; _∈?_; liftˢ-irrelevant)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The convex order on (non-empty) sets of traces
--
-- Both halves compare the two sets in the same direction as
-- `Subtrace.LeftSided` does, i.e. with `Q` on the left.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = (traces Q ≼ˢ traces P) × (traces Q ≽ˢ traces P)

≾ᶜ-refl : {P : NeTraces} → P ≾ P
≾ᶜ-refl {P} = ≼ˢ-refl {traces P} , ≽ˢ-refl {traces P}

≾ᶜ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᶜ-trans {P} {Q} {R} (h₁ , s₁) (h₂ , s₂) =
    ≼ˢ-trans {traces R} {traces Q} {traces P} h₂ h₁
  , ≽ˢ-trans {traces R} {traces Q} {traces P} s₂ s₁

-- the language product is monotone in both arguments, half by half

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} (h , s) =
    ≼ˢ-·ˢ {traces Q} {traces P} {traces C} {traces C} h (≼ˢ-refl {traces C})
  , ≽ˢ-·ˢ {traces Q} {traces P} {traces C} {traces C} s (≽ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} (h , s) =
    ≼ˢ-·ˢ {traces C} {traces C} {traces Q} {traces P} (≼ˢ-refl {traces C}) h
  , ≽ˢ-·ˢ {traces C} {traces C} {traces Q} {traces P} (≽ˢ-refl {traces C}) s

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit `{ ε }` asks for nothing and its single trace fits inside
-- every trace, so both halves hold of it outright and the zero-product
-- property is vacuous -- as it is for the left-sided intervals.

≾ᶜ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᶜ-zero-productˡ {P} {Q} _ =
  u-≼ˢ (traces P) (nonempty P) , u-≽ˢ (traces P)

≾ᶜ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᶜ-zero-productʳ {P} {Q} _ =
  u-≼ˢ (traces Q) (nonempty Q) , u-≽ˢ (traces Q)

-- both halves are decided, so the order is proof-irrelevant

≾ᶜ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᶜ-irrelevant {P} {Q} (h , s) (h' , s') =
  cong₂ _,_ (liftˢ-irrelevant h h') (liftˢ-irrelevant s s')

------------------------------------------------------------------------
-- The order is decidable, half by half

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = (traces Q ≼ˢ? traces P) ×-dec (traces Q ≽ˢ? traces P)

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, convexly ordered

convex-left-sided : Grade
convex-left-sided = record
  { Carrier         = NeTraces
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᶜ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᶜ-trans {i} {j} {k}
  ; _≡?_            = _≟ᴺ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᶜ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᶜ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᶜ-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }

------------------------------------------------------------------------
-- The convex order is strictly finer than either of its halves
--
-- The sets `{ o }`, `{ ε , o }` and `{ ε }` separate the two lifts:
-- adding a trace *below* everything present is allowed by the Hoare
-- half alone, and dropping one is allowed by the Smyth half alone.
-- Both are ruled out by `_≾_`. No condition on the operation's cost is
-- needed: a demand naming an operation is met by no spent run at all.

module Separation (o : Op) (co : ¬ (cost o ≡ zero)) where

  ⟨o⟩ : Trace
  ⟨o⟩ = operation o ε

  P Q : NeTraces
  P = neTraces (⟨o⟩ ∷ []) tt
  Q = neTraces (ε ∷ ⟨o⟩ ∷ []) tt

  -- `{ o } ≼ˢ { ε , o }`, but the empty trace of the larger set is
  -- covered by nothing in the smaller one

  P≼Q : traces P ≼ˢ traces Q
  P≼Q s m = fromWitness (cover s (toWitness {a? = s ∈? traces P} m))
    where
      cover : (s : Trace) → s ∈ traces P → Any (λ t → s ≼ t) (traces Q)
      cover .⟨o⟩ (here refl) = there (here (≼-refl ⟨o⟩))
      cover _    (there ())

  -- a demand naming an operation is met by no spent run

  ¬⟨o⟩≼ε : ¬ (⟨o⟩ ≼ ε)
  ¬⟨o⟩≼ε ()

  -- `ε` is covered by nothing in `{ o }`

  ¬P≽Q : ¬ (traces P ≽ˢ traces Q)
  ¬P≽Q h
    with find (toWitness {a? = any? (λ s → s ≼? ε) (traces P)}
                (h ε (fromWitness {a? = ε ∈? traces Q} (here refl))))
  ... | s , here refl , s≼ε = ¬⟨o⟩≼ε s≼ε
  ... | s , there ()  , _

  -- `{ ε , o } ≽ˢ { ε }`, but the operation of the larger set is
  -- covered by nothing in the unit

  Q≽u : traces Q ≽ˢ traces u
  Q≽u t m =
    fromWitness {a? = any? (λ s → s ≼? t) (traces Q)}
                (cover t (toWitness {a? = t ∈? traces u} m))
    where
      cover : (t : Trace) → t ∈ traces u → Any (λ s → s ≼ t) (traces Q)
      cover .ε (here refl) = here (≼-refl ε)
      cover _  (there ())

  ¬Q≼u : ¬ (traces Q ≼ˢ traces u)
  ¬Q≼u h
    with find (toWitness {a? = any? (λ t → ⟨o⟩ ≼? t) (traces u)}
                (h ⟨o⟩ (fromWitness {a? = ⟨o⟩ ∈? traces Q} (there (here refl)))))
  ... | t , here refl , ⟨o⟩≼t = ¬⟨o⟩≼ε ⟨o⟩≼t
  ... | t , there ()  , _

  -- read as the convex order: `Q ≾ P` fails although its Hoare half
  -- holds, and `u ≾ Q` fails although its Smyth half holds

  ¬Q≾P : ¬ (Q ≾ P)
  ¬Q≾P (_ , s) = ¬P≽Q s

  ¬u≾Q : ¬ (u ≾ Q)
  ¬u≾Q (h , _) = ¬Q≼u h
