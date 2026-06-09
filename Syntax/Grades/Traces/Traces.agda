------------------------------------------------------------------------
-- Sets of timed traces of operations as grades                        --
--                                                                     --
-- An example grade where a grade is a (finite, non-empty) set of      --
-- timed traces. A timed trace is a finite sequence of events, where   --
-- an event is either an operation symbol `Op` or a delay carrying a   --
-- time duration (a natural number). Concretely, a timed trace is      --
-- represented as a list of (delay , operation) pairs followed by a    --
-- final trailing delay:                                               --
--                                                                     --
--   ([ (d₁ , o₁) , … , (dₖ , oₖ) ] , dₖ₊₁)                            --
--     ≡   delay d₁ · o₁ · delay d₂ · o₂ · … · oₖ · delay dₖ₊₁         --
--                                                                     --
-- so that consecutive delays add up and a delay of duration 0 is the  --
-- unit. A grade is then a finite, non-empty set of such timed traces. --
--                                                                     --
--   * the monoid multiplication is the elementwise sequencing of two  --
--     sets of timed traces (the language product over the timed-trace --
--     monoid), with the singleton set `{ ε }` of the empty trace as   --
--     its unit;                                                        --
--   * the order is the subset order on sets of timed traces;          --
--   * the inclusion of the natural numbers sends `n` to the singleton --
--     set `{ delay n }` of the pure delay of duration `n` -- this is  --
--     a monoid homomorphism precisely because delays add up.          --
--                                                                     --
-- The example is parameterised by a `LanguageSpec` (hence by the      --
-- operations and their signatures) together with an assumption that   --
-- the operation symbols have decidable equality. The latter is what   --
-- makes equality of finite sets of timed traces decidable.            --
--                                                                     --
-- Sets of timed traces are required to be non-empty: the empty set is --
-- an absorbing element for the language product, which would break    --
-- the zero-product property of the order (`c · d ≾ u` does not imply  --
-- `c ≾ u` when `d` is the empty set).                                 --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Grades.Traces.Traces (S : LanguageSpec) where

open import Data.Empty using (⊥)
open import Data.List.Base
  using (List; []; _∷_; [_]; _++_; map; cartesianProductWith)
open import Data.List.Properties
  using (++-assoc; ++-identityʳ; ++-conicalˡ; ++-conicalʳ; map-++; map-id; map-cong;
         ∷-injectiveˡ; ∷-injectiveʳ; cartesianProductWith-distribʳ-++; ≡-dec)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (_≟_; +-assoc; +-identityʳ; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Product.Properties using () renaming (≡-dec to ×-≡-dec)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades
open import Syntax.Operations

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

------------------------------------------------------------------------
-- Timed traces and their monoid structure
--
-- A timed trace is a list of (delay , operation) pairs followed by a
-- final trailing delay.

Trace : Set
Trace = List (ℕ × Op) × ℕ

-- the empty timed trace (a single delay of duration 0)

ε : Trace
ε = [] , 0

-- the pure delay of duration n

delay : ℕ → Trace
delay n = [] , n

-- sequencing of two timed traces; the trailing delay of the first
-- trace is added to the leading delay of the second trace

infixl 7 _∙_

_∙_ : Trace → Trace → Trace
(xs , d) ∙ ([] , e)             = xs , d + e
(xs , d) ∙ ((e₁ , o) ∷ ys , e)  = (xs ++ (d + e₁ , o) ∷ ys) , e

-- the monoid laws

∙-identityˡ : (t : Trace) → (ε ∙ t) ≡ t
∙-identityˡ ([] , e)            = refl
∙-identityˡ ((e₁ , o) ∷ ys , e) = refl

∙-identityʳ : (t : Trace) → (t ∙ ε) ≡ t
∙-identityʳ (xs , d) = cong (xs ,_) (+-identityʳ d)

∙-assoc : (s t u : Trace) → ((s ∙ t) ∙ u) ≡ (s ∙ (t ∙ u))
∙-assoc (xs , d) ([] , e)            ([] , g)            =
  cong (xs ,_) (+-assoc d e g)
∙-assoc (xs , d) ([] , e)            ((g₁ , p) ∷ zs , g) =
  cong (λ k → (xs ++ (k , p) ∷ zs) , g) (+-assoc d e g₁)
∙-assoc (xs , d) ((e₁ , o) ∷ ys , e) ([] , g)            = refl
∙-assoc (xs , d) ((e₁ , o) ∷ ys , e) ((g₁ , p) ∷ zs , g) =
  cong (_, g) (++-assoc xs ((d + e₁ , o) ∷ ys) ((e + g₁ , p) ∷ zs))

-- the timed-trace monoid is conical: a product is the empty trace only
-- if both factors are the empty trace

∙-conicalˡ : {s t : Trace} → (s ∙ t) ≡ ε → s ≡ ε
∙-conicalˡ {xs , d} {[] , e} eq =
  cong₂ _,_ (cong proj₁ eq) (m+n≡0⇒m≡0 d (cong proj₂ eq))
∙-conicalˡ {xs , d} {(e₁ , o) ∷ ys , e} eq
  with ++-conicalʳ xs ((d + e₁ , o) ∷ ys) (cong proj₁ eq)
... | ()

∙-conicalʳ : {s t : Trace} → (s ∙ t) ≡ ε → t ≡ ε
∙-conicalʳ {xs , d} {[] , e} eq =
  cong ([] ,_) (m+n≡0⇒n≡0 d (cong proj₂ eq))
∙-conicalʳ {xs , d} {(e₁ , o) ∷ ys , e} eq
  with ++-conicalʳ xs ((d + e₁ , o) ∷ ys) (cong proj₁ eq)
... | ()

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
  constructor mkNe
  field
    traces   : List Trace
    nonempty : NonEmpty traces

open NeTraces public

-- two sets of traces are equal as soon as their underlying lists are
-- (the non-emptiness proofs are irrelevant)

eqNe : {P Q : NeTraces} → traces P ≡ traces Q → P ≡ Q
eqNe {mkNe xs p} {mkNe .xs q} refl = cong (mkNe xs) (NonEmpty-irr xs p q)

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
u = mkNe [ ε ] tt

infixl 7 _·_

_·_ : NeTraces → NeTraces → NeTraces
P · Q = mkNe (traces P ·ˢ traces Q) (·ˢ-ne (nonempty P) (nonempty Q))

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
·-identityʳ P = eqNe (·ˢ-identityʳ (traces P))

·-identityˡ : (P : NeTraces) → (u · P) ≡ P
·-identityˡ P = eqNe (·ˢ-identityˡ (traces P))

·-assoc : (P Q R : NeTraces) → ((P · Q) · R) ≡ (P · (Q · R))
·-assoc P Q R = eqNe (·ˢ-assoc (traces P) (traces Q) (traces R))

------------------------------------------------------------------------
-- Zero-product property of the unit

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
    (∙-conicalˡ (∷-injectiveˡ eq))
    (cpw-emptyˡ {xs} {y} {ys}
      (++-conicalʳ (map (x ∙_) ys) (xs ·ˢ (y ∷ ys)) (∷-injectiveʳ eq)))

·ˢ-zero-productʳ : {xs ys : List Trace}
                 → NonEmpty xs → NonEmpty ys → (xs ·ˢ ys) ≡ [ ε ] → ys ≡ [ ε ]
·ˢ-zero-productʳ {[]}     ()    _  _
·ˢ-zero-productʳ {_ ∷ _}  {[]}  _  () _
·ˢ-zero-productʳ {x ∷ xs} {y ∷ ys} _ _ eq =
  cong₂ _∷_
    (∙-conicalʳ (∷-injectiveˡ eq))
    (map-emptyˡ {x ∙_} {ys}
      (++-conicalˡ (map (x ∙_) ys) (xs ·ˢ (y ∷ ys)) (∷-injectiveʳ eq)))

·-zero-productˡ : {P Q : NeTraces} → (P · Q) ≡ u → P ≡ u
·-zero-productˡ {P} {Q} eq =
  eqNe (·ˢ-zero-productˡ (nonempty P) (nonempty Q) (cong traces eq))

·-zero-productʳ : {P Q : NeTraces} → (P · Q) ≡ u → Q ≡ u
·-zero-productʳ {P} {Q} eq =
  eqNe (·ˢ-zero-productʳ (nonempty P) (nonempty Q) (cong traces eq))

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

of-nat : ℕ → NeTraces
of-nat n = mkNe [ delay n ] tt

of-nat-zero : of-nat 0 ≡ u
of-nat-zero = refl

of-nat-plus : {m n : ℕ} → of-nat (m + n) ≡ (of-nat m · of-nat n)
of-nat-plus {m} {n} = eqNe {of-nat (m + n)} {of-nat m · of-nat n} refl

------------------------------------------------------------------------
-- The subset order and the grade
--
-- The remaining structure (the subset order and decidable equality of
-- sets of traces) relies on decidable equality of the events.

module _ (_≟ₒ_ : DecidableEquality Op) where

  -- decidable equality of timed traces

  _≟ᵀ_ : DecidableEquality Trace
  _≟ᵀ_ = ×-≡-dec (≡-dec (×-≡-dec _≟_ (λ {_} → _≟ₒ_))) (λ {_} → _≟_)

  open import Data.List.Membership.DecPropositional _≟ᵀ_ using (_∈?_)

  -- the subset order on sets of traces (membership-based, so that it is
  -- proof-irrelevant)

  infix 5 _≾_

  _⊑_ : List Trace → List Trace → Set
  xs ⊑ ys = (s : Trace) → True (s ∈? xs) → True (s ∈? ys)

  _≾_ : NeTraces → NeTraces → Set
  P ≾ Q = traces P ⊑ traces Q

  ⊑-refl : {xs : List Trace} → xs ⊑ xs
  ⊑-refl s m = m

  ≾ᵗ-refl : {P : NeTraces} → P ≾ P
  ≾ᵗ-refl s m = m

  ≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
  ≾ᵗ-trans pq qr s m = qr s (pq s m)

  -- the language product is monotone in both arguments

  ⊑-·ˢ : {xs xs' ys ys' : List Trace}
       → xs ⊑ xs' → ys ⊑ ys' → (xs ·ˢ ys) ⊑ (xs' ·ˢ ys')
  ⊑-·ˢ {xs} {xs'} {ys} {ys'} pxs pys s mem
    with ∈-cartesianProductWith⁻ _∙_ xs ys (toWitness mem)
  ... | a , b , a∈xs , b∈ys , refl =
        fromWitness
          (∈-cartesianProductWith⁺ _∙_
            (toWitness (pxs a (fromWitness a∈xs)))
            (toWitness (pys b (fromWitness b∈ys))))

  ·-monoˡ : {c x y : NeTraces} → x ≾ y → (x · c) ≾ (y · c)
  ·-monoˡ {c} {x} {y} rel =
    ⊑-·ˢ {traces x} {traces y} {traces c} {traces c} rel (⊑-refl {traces c})

  ·-monoʳ : {c x y : NeTraces} → x ≾ y → (c · x) ≾ (c · y)
  ·-monoʳ {c} {x} {y} rel =
    ⊑-·ˢ {traces c} {traces c} {traces x} {traces y} (⊑-refl {traces c}) rel

  -- the order is proof-irrelevant

  True-irr : {A : Set} (a? : Dec A) (p q : True a?) → p ≡ q
  True-irr (yes _) _  _ = refl
  True-irr (no  _) ()

  ≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
  ≾ᵗ-irrelevant {P} {Q} p q =
    fun-ext (λ s → fun-ext (λ m → True-irr (s ∈? traces Q) (p s m) (q s m)))

  -- decidable equality of sets of traces

  _≟ᴺ_ : DecidableEquality NeTraces
  P ≟ᴺ Q with ≡-dec _≟ᵀ_ (traces P) (traces Q)
  ... | yes eq = yes (eqNe eq)
  ... | no ¬eq = no λ p → ¬eq (cong traces p)

  -- zero-product property of the order: if `P · Q ⊆ { ε }` then, since
  -- `Q` is non-empty, every trace of `P` sequenced with some trace of
  -- `Q` is the empty trace, hence `P ⊆ { ε }` (and symmetrically for `Q`)

  ≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
  ≾ᵗ-zero-productˡ {P} {Q} hyp s mem with neHead (traces Q) (nonempty Q)
  ... | y , y∈Q = fromWitness (here s≡ε)
    where
      sy∈ : (s ∙ y) ∈ (traces P ·ˢ traces Q)
      sy∈ = ∈-cartesianProductWith⁺ _∙_ (toWitness mem) y∈Q

      s≡ε : s ≡ ε
      s≡ε = ∙-conicalˡ (∈-[ε]⁻ (toWitness (hyp (s ∙ y) (fromWitness sy∈))))

  ≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
  ≾ᵗ-zero-productʳ {P} {Q} hyp s mem with neHead (traces P) (nonempty P)
  ... | x , x∈P = fromWitness (here s≡ε)
    where
      xs∈ : (x ∙ s) ∈ (traces P ·ˢ traces Q)
      xs∈ = ∈-cartesianProductWith⁺ _∙_ x∈P (toWitness mem)

      s≡ε : s ≡ ε
      s≡ε = ∙-conicalʳ (∈-[ε]⁻ (toWitness (hyp (x ∙ s) (fromWitness xs∈))))

  -- the grade of (non-empty) sets of timed traces, ordered by inclusion

  traces-grade : Grade
  traces-grade = record
    { Carrier         = NeTraces
    ; _·_             = _·_
    ; u               = u
    ; ·-identityʳ     = ·-identityʳ
    ; ·-identityˡ     = ·-identityˡ
    ; ·-assoc         = ·-assoc
    ; _≾_             = _≾_
    ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
    ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
    ; ≾-refl          = λ {x} → ≾ᵗ-refl {x}
    ; ≾-trans         = λ {i} {j} {k} → ≾ᵗ-trans {i} {j} {k}
    ; _≡?_            = _≟ᴺ_
    ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗ-zero-productˡ {c} {d}
    ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗ-zero-productʳ {c} {d}
    ; of-nat          = of-nat
    ; of-nat-zero     = of-nat-zero
    ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
    }
