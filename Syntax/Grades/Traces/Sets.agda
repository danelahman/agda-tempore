------------------------------------------------------------------------
-- Non-empty finite sets of timed traces, and their monoid structure.  --
--                                                                     --
-- Every trace-based grade is built from the same carrier: a non-empty  --
-- finite set of timed traces, read as a set of alternative runs. The    --
-- monoid is the language product, which sequences each trace of one     --
-- set with each trace of the other, with unit `{ ε }`. The grades       --
-- differ in the *order* they put on this carrier -- that is what the    --
-- modules under `Grades.Example.Traces` do -- and the two-sided       --
-- grades there pair two such sets, as a floor and a cap.                --
--                                                                     --
-- Deciding membership -- hence any order phrased through it -- needs   --
-- decidable equality of operation symbols, which the `WithDecEq`       --
-- submodule takes as a parameter rather than the whole file.           --
--                                                                     --
-- The timed traces themselves are re-exported from `Traces.Base`.      --
------------------------------------------------------------------------

open import Util.Equality

module Syntax.Grades.Traces.Sets (Op : Set) where

open import Data.Empty using (⊥)
open import Data.List.Base
  using (List; []; _∷_; [_]; _++_; map; cartesianProductWith)
open import Data.List.Properties
  using (++-identityʳ; ++-conicalˡ; ++-conicalʳ; map-++; map-id; map-cong;
         ∷-injectiveˡ; ∷-injectiveʳ; cartesianProductWith-distribʳ-++; ≡-dec)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_,_; Σ)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness; map′)

-- the timed traces the sets are made of

open import Syntax.Grades.Traces.Base Op public

------------------------------------------------------------------------
-- Non-empty sets of timed traces

-- non-emptiness of a list of timed traces

NonEmpty : List Trace → Set
NonEmpty []      = ⊥
NonEmpty (_ ∷ _) = ⊤

-- non-emptiness is proof-irrelevant

NonEmpty-irr : (xs : List Trace) → (p q : NonEmpty xs) → p ≡ q
NonEmpty-irr []      ()
NonEmpty-irr (_ ∷ _) tt tt = refl

-- a grade is a non-empty (finite) set of timed traces, represented as a
-- non-empty list of timed traces

record NeTraces : Set where
  constructor neTraces
  field
    traces   : List Trace
    nonempty : NonEmpty traces

open NeTraces public

-- two sets of traces are equal as soon as their underlying lists are
-- (the non-emptiness proofs are irrelevant)

ne-ext : {P Q : NeTraces} → traces P ≡ traces Q → P ≡ Q
ne-ext {neTraces xs p} {neTraces .xs q} refl = cong (neTraces xs) (NonEmpty-irr xs p q)

------------------------------------------------------------------------
-- Monoid structure on sets of traces: the language product with unit { ε }

infixl 7 _·ˢ_

-- elementwise sequencing of two sets of timed traces

_·ˢ_ : List Trace → List Trace → List Trace
xs ·ˢ ys = cartesianProductWith _∙_ xs ys

-- the language product of two non-empty sets of traces is non-empty

·ˢ-ne : {xs ys : List Trace} → NonEmpty xs → NonEmpty ys → NonEmpty (xs ·ˢ ys)
·ˢ-ne {[]}     ()    _
·ˢ-ne {_ ∷ _}  {[]}  _  ()
·ˢ-ne {_ ∷ _}  {_ ∷ _} _ _ = tt

-- the unit is the singleton set containing the empty trace

u : NeTraces
u = neTraces [ ε ] tt

infixl 7 _·_

_·_ : NeTraces → NeTraces → NeTraces
P · Q = neTraces (traces P ·ˢ traces Q) (·ˢ-ne (nonempty P) (nonempty Q))

-- sequencing the empty trace on the left is the identity

map-ε∙ : (xs : List Trace) → map (ε ∙_) xs ≡ xs
map-ε∙ xs = trans (map-cong ∙-identityˡ xs) (map-id xs)

-- left and right unit laws (on the underlying lists)

·ˢ-identityˡ : (xs : List Trace) → ([ ε ] ·ˢ xs) ≡ xs
·ˢ-identityˡ xs = trans (++-identityʳ (map (ε ∙_) xs)) (map-ε∙ xs)

·ˢ-identityʳ : (xs : List Trace) → (xs ·ˢ [ ε ]) ≡ xs
·ˢ-identityʳ []       = refl
·ˢ-identityʳ (x ∷ xs) = cong₂ _∷_ (∙-identityʳ x) (·ˢ-identityʳ xs)

-- the language product distributes over the left factor being mapped

cpw-map : (x : Trace) (ys zs : List Trace)
        → (map (x ∙_) ys ·ˢ zs) ≡ map (x ∙_) (ys ·ˢ zs)
cpw-map x []       zs = refl
cpw-map x (y ∷ ys) zs =
  begin
    map ((x ∙ y) ∙_) zs ++ (map (x ∙_) ys ·ˢ zs)
      ≡⟨ cong (map ((x ∙ y) ∙_) zs ++_) (cpw-map x ys zs) ⟩
    map ((x ∙ y) ∙_) zs ++ map (x ∙_) (ys ·ˢ zs)
      ≡⟨ cong (_++ map (x ∙_) (ys ·ˢ zs)) (step zs) ⟩
    map (x ∙_) (map (y ∙_) zs) ++ map (x ∙_) (ys ·ˢ zs)
      ≡⟨ sym (map-++ (x ∙_) (map (y ∙_) zs) (ys ·ˢ zs)) ⟩
    map (x ∙_) (map (y ∙_) zs ++ (ys ·ˢ zs))
  ∎
  where
    step : (ws : List Trace) → map ((x ∙ y) ∙_) ws ≡ map (x ∙_) (map (y ∙_) ws)
    step []       = refl
    step (w ∷ ws) = cong₂ _∷_ (∙-assoc x y w) (step ws)

-- associativity (on the underlying lists)

·ˢ-assoc : (xs ys zs : List Trace) → ((xs ·ˢ ys) ·ˢ zs) ≡ (xs ·ˢ (ys ·ˢ zs))
·ˢ-assoc []       ys zs = refl
·ˢ-assoc (x ∷ xs) ys zs =
  begin
    (map (x ∙_) ys ++ (xs ·ˢ ys)) ·ˢ zs
      ≡⟨ cartesianProductWith-distribʳ-++ _∙_ (map (x ∙_) ys) (xs ·ˢ ys) zs ⟩
    (map (x ∙_) ys ·ˢ zs) ++ ((xs ·ˢ ys) ·ˢ zs)
      ≡⟨ cong (_++ ((xs ·ˢ ys) ·ˢ zs)) (cpw-map x ys zs) ⟩
    map (x ∙_) (ys ·ˢ zs) ++ ((xs ·ˢ ys) ·ˢ zs)
      ≡⟨ cong (map (x ∙_) (ys ·ˢ zs) ++_) (·ˢ-assoc xs ys zs) ⟩
    map (x ∙_) (ys ·ˢ zs) ++ (xs ·ˢ (ys ·ˢ zs))
  ∎

-- the monoid laws for sets of traces

·-identityʳ : (P : NeTraces) → (P · u) ≡ P
·-identityʳ P = ne-ext (·ˢ-identityʳ (traces P))

·-identityˡ : (P : NeTraces) → (u · P) ≡ P
·-identityˡ P = ne-ext (·ˢ-identityˡ (traces P))

·-assoc : (P Q R : NeTraces) → ((P · Q) · R) ≡ (P · (Q · R))
·-assoc P Q R = ne-ext (·ˢ-assoc (traces P) (traces Q) (traces R))

------------------------------------------------------------------------
-- Zero-product property of the unit (on the underlying lists)

-- the language product of a set with a non-empty set is empty only if
-- the first set is empty

cpw-emptyˡ : {xs : List Trace} {y : Trace} {ys : List Trace}
           → (xs ·ˢ (y ∷ ys)) ≡ [] → xs ≡ []
cpw-emptyˡ {[]}    _  = refl
cpw-emptyˡ {_ ∷ _} ()

map-emptyˡ : {f : Trace → Trace} {ys : List Trace} → map f ys ≡ [] → ys ≡ []
map-emptyˡ {ys = []}    _  = refl
map-emptyˡ {ys = _ ∷ _} ()

-- if a language product is the unit, then so are both factors

·ˢ-zero-productˡ : {xs ys : List Trace}
                 → NonEmpty xs → NonEmpty ys → (xs ·ˢ ys) ≡ [ ε ] → xs ≡ [ ε ]
·ˢ-zero-productˡ {[]}     ()    _  _
·ˢ-zero-productˡ {_ ∷ _}  {[]}  _  () _
·ˢ-zero-productˡ {x ∷ xs} {y ∷ ys} _ _ eq =
  cong₂ _∷_
    (∙-conicalˡ {x} {y} (∷-injectiveˡ eq))
    (cpw-emptyˡ {xs} {y} {ys}
      (++-conicalʳ (map (x ∙_) ys) (xs ·ˢ (y ∷ ys)) (∷-injectiveʳ eq)))

·ˢ-zero-productʳ : {xs ys : List Trace}
                 → NonEmpty xs → NonEmpty ys → (xs ·ˢ ys) ≡ [ ε ] → ys ≡ [ ε ]
·ˢ-zero-productʳ {[]}     ()    _  _
·ˢ-zero-productʳ {_ ∷ _}  {[]}  _  () _
·ˢ-zero-productʳ {x ∷ xs} {y ∷ ys} _ _ eq =
  cong₂ _∷_
    (∙-conicalʳ {x} {y} (∷-injectiveˡ eq))
    (map-emptyˡ {x ∙_} {ys}
      (++-conicalˡ (map (x ∙_) ys) (xs ·ˢ (y ∷ ys)) (∷-injectiveʳ eq)))

·-zero-productˡ : {P Q : NeTraces} → (P · Q) ≡ u → P ≡ u
·-zero-productˡ {P} {Q} eq =
  ne-ext (·ˢ-zero-productˡ (nonempty P) (nonempty Q) (cong traces eq))

·-zero-productʳ : {P Q : NeTraces} → (P · Q) ≡ u → Q ≡ u
·-zero-productʳ {P} {Q} eq =
  ne-ext (·ˢ-zero-productʳ (nonempty P) (nonempty Q) (cong traces eq))

------------------------------------------------------------------------
-- Auxiliary facts about membership

-- a non-empty set of traces has a witnessing trace

neHead : (xs : List Trace) → NonEmpty xs → Σ Trace (_∈ xs)
neHead (y ∷ _) _ = y , here refl
neHead []      ()

-- the only element of the unit is the empty trace

∈-[ε]⁻ : {a : Trace} → a ∈ [ ε ] → a ≡ ε
∈-[ε]⁻ (here px) = px
∈-[ε]⁻ (there ())

------------------------------------------------------------------------
-- Inclusion of the natural numbers as pure delays
--
-- A natural number `n` becomes the singleton set containing the pure
-- delay of duration `n`, which is what a grade's `of-nat` asks for.

of-nat : ℕ → NeTraces
of-nat n = neTraces [ ⟨ n ⟩ ] tt

of-nat-zero : of-nat 0 ≡ u
of-nat-zero = refl

of-nat-plus : {m n : ℕ} → of-nat (m + n) ≡ (of-nat m · of-nat n)
of-nat-plus {m} {n} =
  ne-ext {of-nat (m + n)} {of-nat m · of-nat n} (cong [_] (⟨⟩-hom m n))

------------------------------------------------------------------------
-- What decidable equality of operation symbols buys
--
-- Membership in a finite set of traces becomes decidable, and with it
-- the set-level lift `liftˢ` that every trace grade's order is an
-- instance of, the subset preorder `_⊑_` on the underlying lists (the
-- lift at equality), and decidable equality of sets of traces.

module WithDecEq (_≟ₒ_ : DecidableEquality Op) where

  open DecTrace _≟ₒ_ public

  open import Data.List.Membership.DecPropositional _≟ᵀ_ public using (_∈?_)

  ----------------------------------------------------------------------
  -- The set-level lift of a relation on traces
  --
  -- Every order the trace grades put on sets of traces has one shape:
  -- every trace of the left-hand set is related to *some* trace of the
  -- right-hand one. Only the relation lifted differs, so the properties
  -- are proved here once and instantiated elsewhere.
  --
  -- The superscript marks the level, not one of the instances: at `_≡_`
  -- the lift is the subset preorder, at `_≼_` the Hoare lower lift, and
  -- at the converse of `_≼_` the Smyth upper lift read backwards.
  --
  -- Membership and `R` are both decided, so the lift is stated in the
  -- proof-irrelevant `True`-of-a-decision form.

  liftˢ : (R : Trace → Trace → Set) → Decidable R
        → List Trace → List Trace → Set
  liftˢ R R? xs ys = (s : Trace) → True (s ∈? xs) → True (any? (R? s) ys)

  -- reflexivity, transitivity, and monotonicity for the language
  -- product are inherited from the relation being lifted

  liftˢ-refl : {R : Trace → Trace → Set} → (R? : Decidable R)
             → ((s : Trace) → R s s)
             → {xs : List Trace} → liftˢ R R? xs xs
  liftˢ-refl {R} R? rfl s m =
    fromWitness (Any.map (λ eq → subst (R s) eq (rfl s)) (toWitness m))

  liftˢ-trans : {R : Trace → Trace → Set} → (R? : Decidable R)
              → ({s t u : Trace} → R s t → R t u → R s u)
              → {xs ys zs : List Trace}
              → liftˢ R R? xs ys → liftˢ R R? ys zs → liftˢ R R? xs zs
  liftˢ-trans {R} R? tr xy yz s m
    with find (toWitness (xy s m))
  ... | y , y∈ys , sRy
          with find (toWitness (yz y (fromWitness y∈ys)))
  ...     | z , z∈zs , yRz =
            fromWitness
              (Any.map (λ eq → subst (R s) eq (tr sRy yRz)) z∈zs)

  liftˢ-·ˢ : {R : Trace → Trace → Set} → (R? : Decidable R)
           → ({a a' b b' : Trace} → R a a' → R b b' → R (a ∙ b) (a' ∙ b'))
           → {xs xs' ys ys' : List Trace}
           → liftˢ R R? xs xs' → liftˢ R R? ys ys'
           → liftˢ R R? (xs ·ˢ ys) (xs' ·ˢ ys')
  liftˢ-·ˢ {R} R? mono {xs} {xs'} {ys} {ys'} pxs pys r m
    with ∈-cartesianProductWith⁻ _∙_ xs ys (toWitness m)
  ... | a , b , a∈xs , b∈ys , refl
          with find (toWitness (pxs a (fromWitness a∈xs)))
             | find (toWitness (pys b (fromWitness b∈ys)))
  ...     | a' , a'∈ , aRa' | b' , b'∈ , bRb' =
            fromWitness
              (Any.map (λ eq → subst (R (a ∙ b)) eq (mono aRa' bRb'))
                       (∈-cartesianProductWith⁺ _∙_ a'∈ b'∈))

  -- weakening the relation weakens the lift, which is what relates two
  -- of the trace grades to a third built on a coarser relation

  liftˢ-mono : {R R' : Trace → Trace → Set}
             → (R? : Decidable R) → (R'? : Decidable R')
             → ({s t : Trace} → R s t → R' s t)
             → {xs ys : List Trace}
             → liftˢ R R? xs ys → liftˢ R' R'? xs ys
  liftˢ-mono R? R'? f p s m =
    fromWitness (Any.map f (toWitness (p s m)))

  -- the orders built from the lift are proof-irrelevant

  True-irr : {A : Set} (a? : Dec A) (p q : True a?) → p ≡ q
  True-irr (yes _) _  _ = refl
  True-irr (no  _) ()

  -- so the lift is too, pointwise -- which is every trace grade's
  -- `≾-irrelevant`, one endpoint at a time

  liftˢ-irrelevant : {R : Trace → Trace → Set} → {R? : Decidable R}
                   → {xs ys : List Trace}
                   → (p q : liftˢ R R? xs ys) → p ≡ q
  liftˢ-irrelevant {R} {R?} {xs} {ys} p q =
    fun-ext (λ s → fun-ext (λ m → True-irr (any? (R? s) ys) (p s m) (q s m)))

  -- the lift is decidable: the quantifier ranges over all traces, but
  -- only the finitely many members of the left-hand list satisfy its
  -- premise, so reading it as an `All` over that list decides it

  liftˢ-all : {R : Trace → Trace → Set} → {R? : Decidable R}
            → {xs ys : List Trace}
            → All (λ s → Any (R s) ys) xs → liftˢ R R? xs ys
  liftˢ-all as s m = fromWitness (All.lookup as (toWitness m))

  all-liftˢ : {R : Trace → Trace → Set} → {R? : Decidable R}
            → {xs ys : List Trace}
            → liftˢ R R? xs ys → All (λ s → Any (R s) ys) xs
  all-liftˢ f = All.tabulate (λ {s} s∈xs → toWitness (f s (fromWitness s∈xs)))

  liftˢ? : {R : Trace → Trace → Set} → (R? : Decidable R)
         → (xs ys : List Trace) → Dec (liftˢ R R? xs ys)
  liftˢ? R? xs ys = map′ liftˢ-all all-liftˢ (all? (λ s → any? (R? s) ys) xs)

  ----------------------------------------------------------------------
  -- The subset preorder is the lift at equality

  _⊑_ : List Trace → List Trace → Set
  _⊑_ = liftˢ _≡_ _≟ᵀ_

  ⊑-refl : {xs : List Trace} → xs ⊑ xs
  ⊑-refl = liftˢ-refl _≟ᵀ_ (λ _ → refl)

  ⊑-trans : {xs ys zs : List Trace} → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
  ⊑-trans = liftˢ-trans _≟ᵀ_ trans

  -- the language product is monotone in both arguments

  ⊑-·ˢ : {xs xs' ys ys' : List Trace}
       → xs ⊑ xs' → ys ⊑ ys' → (xs ·ˢ ys) ⊑ (xs' ·ˢ ys')
  ⊑-·ˢ = liftˢ-·ˢ _≟ᵀ_ (cong₂ _∙_)

  infix 5 _⊑?_

  _⊑?_ : (xs ys : List Trace) → Dec (xs ⊑ ys)
  _⊑?_ = liftˢ? _≟ᵀ_

  -- decidable equality of sets of traces

  _≟ᴺ_ : DecidableEquality NeTraces
  P ≟ᴺ Q with ≡-dec _≟ᵀ_ (traces P) (traces Q)
  ... | yes eq = yes (ne-ext eq)
  ... | no ¬eq = no λ p → ¬eq (cong traces p)
