---------------------------------------------
-- Timed traces and their monoid structure --
---------------------------------------------

open import Util.Equality

-- Trace-based grades are parameterised by a set `Op` of operation names.

module Syntax.Grades.Traces.Base (Op : Set) where

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
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (_,_; Σ)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

------------------------------------------------------------------------
-- Positive durations
--
-- Delays carry a strictly positive duration, so that zero-valued delays
-- cannot appear in a trace. We use a small dedicated type of positive
-- naturals together with its addition.

data ℕ⁺ : Set where
  𝟏    : ℕ⁺
  suc⁺ : ℕ⁺ → ℕ⁺

infixl 6 _+⁺_

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
𝟏      +⁺ n = suc⁺ n
suc⁺ m +⁺ n = suc⁺ (m +⁺ n)

+⁺-assoc : (m n o : ℕ⁺) → ((m +⁺ n) +⁺ o) ≡ (m +⁺ (n +⁺ o))
+⁺-assoc 𝟏        n o = refl
+⁺-assoc (suc⁺ m) n o = cong suc⁺ (+⁺-assoc m n o)

_≟⁺_ : DecidableEquality ℕ⁺
𝟏      ≟⁺ 𝟏      = yes refl
𝟏      ≟⁺ suc⁺ _ = no λ ()
suc⁺ _ ≟⁺ 𝟏      = no λ ()
suc⁺ m ≟⁺ suc⁺ n with m ≟⁺ n
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }

-- the positive natural `1 + n` (used to read a positive duration off a
-- natural number)

infix 8 1+_

1+_ : ℕ → ℕ⁺
1+ zero    = 𝟏
1+ (suc n) = suc⁺ (1+ n)

1+-+⁺ : (m n : ℕ) → ((1+ m) +⁺ (1+ n)) ≡ 1+ (m + suc n)
1+-+⁺ zero    n = refl
1+-+⁺ (suc m) n = cong suc⁺ (1+-+⁺ m n)

------------------------------------------------------------------------
-- Timed traces and their monoid structure
--
-- A timed trace alternates positive delays and operations (see the
-- module header). The empty trace is `ε`; `op o t` prepends an
-- operation (with no delay before it); and `del d t` prepends a
-- positive delay before a delay-free-headed trace `t`. A delay node
-- thus carries only its duration, an operation node only its operation,
-- and the `Trace⁻` continuation of a delay rules out adjacent delays.

mutual

  data Trace : Set where
    ε         : Trace
    operation : Op → Trace → Trace
    delay     : ℕ⁺ → Trace⁻ → Trace

  -- timed traces that do not begin with a delay

  data Trace⁻ : Set where
    ε⁻         : Trace⁻
    operation⁻ : Op → Trace → Trace⁻

-- the pure delay of duration n (a zero delay is just the empty trace)

⟨_⟩ : ℕ → Trace
⟨ zero  ⟩ = ε
⟨ suc n ⟩ = delay (1+ n) ε⁻

-- a single operation event (no surrounding delay)

⌈_⌉ : Op → Trace
⌈ op ⌉ = operation op ε

-- prepending a positive delay to a trace,
-- merging it with the leading delay of the trace

prepend : ℕ⁺ → Trace → Trace
prepend d ε                = delay d ε⁻
prepend d (operation op t) = delay d (operation⁻ op t)
prepend d (delay e t)      = delay (d +⁺ e) t

-- sequencing of two timed traces; the trailing delay of the first trace
-- is merged with the leading delay of the second trace

infixl 7 _∙_

_∙_ : Trace → Trace → Trace
ε                        ∙ t = t
operation o s            ∙ t = operation o (s ∙ t)
delay d ε⁻               ∙ t = prepend d t
delay d (operation⁻ o s) ∙ t = delay d (operation⁻ o (s ∙ t))

-- the monoid laws

∙-identityˡ : (t : Trace) → (ε ∙ t) ≡ t
∙-identityˡ t = refl

∙-identityʳ : (t : Trace) → (t ∙ ε) ≡ t
∙-identityʳ ε                          = refl
∙-identityʳ (operation o t)            = cong (operation o) (∙-identityʳ t)
∙-identityʳ (delay d ε⁻)               = refl
∙-identityʳ (delay d (operation⁻ o t)) = cong (λ z → delay d (operation⁻ o z)) (∙-identityʳ t)

-- prepending commutes with the additive merging of delays

prepend-+⁺ : (d e : ℕ⁺) (u : Trace) → prepend (d +⁺ e) u ≡ prepend d (prepend e u)
prepend-+⁺ d e ε                = refl
prepend-+⁺ d e (operation o u)  = refl
prepend-+⁺ d e (delay f u)      = cong (λ z → delay z u) (+⁺-assoc d e f)

-- prepending commutes with sequencing on the right

prepend-∙ : (d : ℕ⁺) (t u : Trace) → ((prepend d t) ∙ u) ≡ prepend d (t ∙ u)
prepend-∙ d ε                        u = refl
prepend-∙ d (operation o t)          u = refl
prepend-∙ d (delay e ε⁻)             u = prepend-+⁺ d e u
prepend-∙ d (delay e (operation⁻ o t)) u = refl

∙-assoc : (s t u : Trace) → ((s ∙ t) ∙ u) ≡ (s ∙ (t ∙ u))
∙-assoc ε                          t u = refl
∙-assoc (operation o s)            t u = cong (operation o) (∙-assoc s t u)
∙-assoc (delay d ε⁻)               t u = prepend-∙ d t u
∙-assoc (delay d (operation⁻ o s)) t u = cong (λ z → delay d (operation⁻ o z)) (∙-assoc s t u)

-- the timed-trace monoid is conical: a product is the
-- empty trace only if both factors are the empty trace

∙-conicalˡ : {s t : Trace} → (s ∙ t) ≡ ε → s ≡ ε
∙-conicalˡ {ε}                          _  = refl
∙-conicalˡ {operation _ _}              ()
∙-conicalˡ {delay _ (operation⁻ _ _)}   ()
∙-conicalˡ {delay _ ε⁻} {ε}             ()
∙-conicalˡ {delay _ ε⁻} {operation _ _} ()
∙-conicalˡ {delay _ ε⁻} {delay _ _}     ()

∙-conicalʳ : {s t : Trace} → (s ∙ t) ≡ ε → t ≡ ε
∙-conicalʳ {ε}                          eq = eq
∙-conicalʳ {operation _ _}              ()
∙-conicalʳ {delay _ (operation⁻ _ _)}   ()
∙-conicalʳ {delay _ ε⁻} {ε}             ()
∙-conicalʳ {delay _ ε⁻} {operation _ _} ()
∙-conicalʳ {delay _ ε⁻} {delay _ _}     ()

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

-- pure delays are a monoid homomorphism: adding durations corresponds
-- to sequencing the pure delays

⟨⟩-hom : (m n : ℕ) → ⟨ m + n ⟩ ≡ (⟨ m ⟩ ∙ ⟨ n ⟩)
⟨⟩-hom zero    n       = refl
⟨⟩-hom (suc m) zero    = cong (λ z → delay (1+ z) ε⁻) (+-identityʳ m)
⟨⟩-hom (suc m) (suc n) = cong (λ z → delay z ε⁻) (sym (1+-+⁺ m n))

of-nat : ℕ → NeTraces
of-nat n = neTraces [ ⟨ n ⟩ ] tt

of-nat-zero : of-nat 0 ≡ u
of-nat-zero = refl

of-nat-plus : {m n : ℕ} → of-nat (m + n) ≡ (of-nat m · of-nat n)
of-nat-plus {m} {n} =
  ne-ext {of-nat (m + n)} {of-nat m · of-nat n} (cong [_] (⟨⟩-hom m n))

------------------------------------------------------------------------
-- Traces have decidable equality.

module WithDecEq (_≟ₒ_ : DecidableEquality Op) where

  -- decidable (structural) equality of timed traces

  mutual

    _≟ᵀ_ : DecidableEquality Trace
    ε           ≟ᵀ ε           = yes refl
    ε           ≟ᵀ operation _ _ = no λ ()
    ε           ≟ᵀ delay _ _    = no λ ()
    operation _ _ ≟ᵀ ε          = no λ ()
    operation o s ≟ᵀ operation o' s' with o ≟ₒ o' | s ≟ᵀ s'
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬q    = no λ { refl → ¬q refl }
    operation _ _ ≟ᵀ delay _ _  = no λ ()
    delay _ _   ≟ᵀ ε            = no λ ()
    delay _ _   ≟ᵀ operation _ _ = no λ ()
    delay d s   ≟ᵀ delay d' s'  with d ≟⁺ d' | s ≟ᵀ⁻ s'
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬q    = no λ { refl → ¬q refl }

    -- decidable equality of delay-free-headed traces

    _≟ᵀ⁻_ : DecidableEquality Trace⁻
    ε⁻            ≟ᵀ⁻ ε⁻            = yes refl
    ε⁻            ≟ᵀ⁻ operation⁻ _ _ = no λ ()
    operation⁻ _ _ ≟ᵀ⁻ ε⁻           = no λ ()
    operation⁻ o s ≟ᵀ⁻ operation⁻ o' s' with o ≟ₒ o' | s ≟ᵀ s'
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬q    = no λ { refl → ¬q refl }

  open import Data.List.Membership.DecPropositional _≟ᵀ_ public using (_∈?_)

  -- the subset preorder on lists of traces

  _⊑_ : List Trace → List Trace → Set
  xs ⊑ ys = (s : Trace) → True (s ∈? xs) → True (s ∈? ys)

  ⊑-refl : {xs : List Trace} → xs ⊑ xs
  ⊑-refl s m = m

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

  -- the orders built from `_⊑_` are proof-irrelevant

  True-irr : {A : Set} (a? : Dec A) (p q : True a?) → p ≡ q
  True-irr (yes _) _  _ = refl
  True-irr (no  _) ()

  -- decidable equality of sets of traces

  _≟ᴺ_ : DecidableEquality NeTraces
  P ≟ᴺ Q with ≡-dec _≟ᵀ_ (traces P) (traces Q)
  ... | yes eq = yes (ne-ext eq)
  ... | no ¬eq = no λ p → ¬eq (cong traces p)
