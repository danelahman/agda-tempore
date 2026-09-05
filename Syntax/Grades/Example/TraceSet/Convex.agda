------------------------------------------------------------------------
-- Sets of timed traces, ordered by the convex (Egli-Milner) lift of   --
-- the sub-trace preorder:                                             --
--                                                                     --
--   P ≾ Q   iff   every trace of P is `≼` some trace of Q             --
--            and  every trace of Q is `≽` some trace of P.            --
--                                                                     --
-- The first conjunct is the Hoare lower lift, shared with             --
-- `TraceSet.UpToSubtrace`; the second is the Smyth upper lift.        --
-- Weakening a grade may add traces only between traces already        --
-- present: the extremes are exact.                                    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.TraceSet.Convex
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.Nat.Properties using (n≤0⇒n≡0)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades

-- the timed-trace monoid, the sub-trace preorder, and the Hoare half of
-- the order are shared with the Hoare-ordered sets of traces

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op cost

open import Syntax.Grades.Example.TraceSet.UpToSubtrace Op _≟ₒ_ cost
  using (_≼ˢ_; ≼ˢ-refl; ≼ˢ-trans; ≼ˢ-·ˢ)
  renaming (≾ᵗ-zero-productˡ to ≼ˢ-zero-productˡ;
            ≾ᵗ-zero-productʳ to ≼ˢ-zero-productʳ)

open WithDecEq _≟ₒ_ using (_≟ᴺ_; _∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The Smyth upper lift of the sub-trace preorder
--
-- Dual to `_≼ˢ_`: the quantification runs over the members of the
-- right-hand set, and the witness is found on the left.

infix 5 _≽ˢ_

_≽ˢ_ : List Trace → List Trace → Set
xs ≽ˢ ys = (t : Trace) → True (t ∈? ys) → True (any? (λ s → s ≼? t) xs)

-- the lift of a reflexive relation is reflexive

≽ˢ-refl : {xs : List Trace} → xs ≽ˢ xs
≽ˢ-refl {xs} t m =
  fromWitness (Any.map (λ eq → subst (_≼ t) eq (≼-refl t)) (toWitness m))

-- the lift of a transitive relation is transitive

≽ˢ-trans : {xs ys zs : List Trace} → xs ≽ˢ ys → ys ≽ˢ zs → xs ≽ˢ zs
≽ˢ-trans {xs} {ys} {zs} xy yz t m
  with find (toWitness (yz t m))
... | y , y∈ys , y≼t
        with find (toWitness (xy y (fromWitness y∈ys)))
...     | x , x∈xs , x≼y =
          fromWitness
            (Any.map (λ eq → subst (_≼ t) eq (≼-trans x≼y y≼t)) x∈xs)

-- the language product is monotone for the lift (in both arguments at
-- once), since the trace product is monotone for `_≼_`

≽ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ≽ˢ xs' → ys ≽ˢ ys' → (xs ·ˢ ys) ≽ˢ (xs' ·ˢ ys')
≽ˢ-·ˢ {xs} {xs'} {ys} {ys'} pxs pys r m
  with ∈-cartesianProductWith⁻ _∙_ xs' ys' (toWitness m)
... | a' , b' , a'∈xs' , b'∈ys' , refl
        with find (toWitness (pxs a' (fromWitness a'∈xs')))
           | find (toWitness (pys b' (fromWitness b'∈ys')))
...     | a , a∈xs , a≼a' | b , b∈ys , b≼b' =
          fromWitness
            (Any.map (λ eq → subst (_≼ (a' ∙ b')) eq (mono-∙ a≼a' b≼b'))
                     (∈-cartesianProductWith⁺ _∙_ a∈xs b∈ys))

------------------------------------------------------------------------
-- The convex order on (non-empty) sets of traces

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = (traces P ≼ˢ traces Q) × (traces P ≽ˢ traces Q)

≾ᶜ-refl : {P : NeTraces} → P ≾ P
≾ᶜ-refl {P} = ≼ˢ-refl {traces P} , ≽ˢ-refl {traces P}

≾ᶜ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᶜ-trans {P} {Q} {R} (h₁ , s₁) (h₂ , s₂) =
    ≼ˢ-trans {traces P} {traces Q} {traces R} h₁ h₂
  , ≽ˢ-trans {traces P} {traces Q} {traces R} s₁ s₂

-- the language product is monotone in both arguments, half by half

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} (h , s) =
    ≼ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} h (≼ˢ-refl {traces C})
  , ≽ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} s (≽ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} (h , s) =
    ≼ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≼ˢ-refl {traces C}) h
  , ≽ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≽ˢ-refl {traces C}) s

------------------------------------------------------------------------
-- Zero-product property
--
-- Only the Hoare half carries information here: it already forces every
-- trace of a factor to be `≼ ε`, and a witness for the Smyth half is
-- then any member of the (non-empty) factor.

≾ᶜ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᶜ-zero-productˡ {P} {Q} (h , _) = hoare , smyth
  where
    hoare : traces P ≼ˢ traces u
    hoare = ≼ˢ-zero-productˡ {P} {Q} h

    smyth : traces P ≽ˢ traces u
    smyth t m
      with neHead (traces P) (nonempty P)
    ... | x , x∈P
            with find (toWitness (hoare x (fromWitness x∈P)))
    ...     | e , e∈u , x≼e =
              fromWitness
                (Any.map
                  (λ eq → subst (_≼ t) eq
                            (subst (x ≼_)
                                   (trans (∈-[ε]⁻ e∈u)
                                          (sym (∈-[ε]⁻ (toWitness m))))
                                   x≼e))
                  x∈P)

≾ᶜ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᶜ-zero-productʳ {P} {Q} (h , _) = hoare , smyth
  where
    hoare : traces Q ≼ˢ traces u
    hoare = ≼ˢ-zero-productʳ {P} {Q} h

    smyth : traces Q ≽ˢ traces u
    smyth t m
      with neHead (traces Q) (nonempty Q)
    ... | x , x∈Q
            with find (toWitness (hoare x (fromWitness x∈Q)))
    ...     | e , e∈u , x≼e =
              fromWitness
                (Any.map
                  (λ eq → subst (_≼ t) eq
                            (subst (x ≼_)
                                   (trans (∈-[ε]⁻ e∈u)
                                          (sym (∈-[ε]⁻ (toWitness m))))
                                   x≼e))
                  x∈Q)

-- both halves are decided, so the order is proof-irrelevant

≾ᶜ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᶜ-irrelevant {P} {Q} (h , s) (h' , s') =
  cong₂ _,_
    (fun-ext (λ t → fun-ext (λ m →
       True-irr (any? (λ t' → t ≼? t') (traces Q)) (h t m) (h' t m))))
    (fun-ext (λ t → fun-ext (λ m →
       True-irr (any? (λ s' → s' ≼? t) (traces P)) (s t m) (s' t m))))

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, convexly ordered

traces-convex : Grade
traces-convex = record
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
-- Given an operation symbol `o` that takes time, the sets `{ o }`,
-- `{ ε , o }` and `{ ε }` separate the two lifts: adding a trace
-- *below* everything present is allowed by the Hoare half alone, and
-- dropping one is allowed by the Smyth half alone. Both are ruled out
-- by `_≾_`. The operation has to take time, since an instantaneous one
-- is covered by the empty trace.

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

  -- an operation that takes time is not covered by the empty trace,
  -- which has no slack to pay for it

  ¬⟨o⟩≼ε : ¬ (⟨o⟩ ≼ ε)
  ¬⟨o⟩≼ε (use-op p _) = co (n≤0⇒n≡0 p)

  -- `ε` is covered by nothing in `{ o }`

  ¬P≽Q : ¬ (traces P ≽ˢ traces Q)
  ¬P≽Q h
    with find (toWitness (h ε (fromWitness {a? = ε ∈? traces Q} (here refl))))
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
    with find (toWitness
                (h ⟨o⟩ (fromWitness {a? = ⟨o⟩ ∈? traces Q} (there (here refl)))))
  ... | t , here refl , ⟨o⟩≼t = ¬⟨o⟩≼ε ⟨o⟩≼t
  ... | t , there ()  , _
