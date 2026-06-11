--------------------------------------------------------------------------
-- Timed traces and their monoid structure                              --
--                                                                      --
-- This module collects the data and proofs that are common to both     --
-- kinds of trace-based interval grades (the right-sided subset-ordered --
-- example `Syntax.Grades.Traces.RightSidedTraces` and the left-sided   --
-- superset-ordered example `Syntax.Grades.Traces.LeftSidedTraces`).    --
-- The two examples share everything below and differ only in their     --
-- order, so all of it lives here and is re-used from there.            --
--                                                                      --
-- A timed trace is a finite sequence of events that alternates time    --
-- delays and operation symbols `Op`. It is represented by a custom     --
-- inductive type with four constructors:                               --
--                                                                      --
--   ε             -- the empty trace                                   --
--   op o t        -- an operation `o`, then the rest `t`               --
--   del d o t     -- a (positive) delay `d`, an operation `o`, then    --
--                 --   the rest `t`                                    --
--   fin d         -- a final (positive) trailing delay `d`             --
--                                                                     --
-- Delays carry a *positive* duration `ℕ⁺`, so a zero-valued delay is   --
-- never visible in a trace: waiting no time before an operation is the --
-- bare `op` constructor, and the empty trace is `ε` rather than a      --
-- delay of duration `0`. A delay is moreover always immediately        --
-- followed by an operation (`del`) or is the final event (`fin`), so   --
-- two delays never sit next to each other. Hence every timed trace has --
-- a unique representation, which is what makes propositional (and      --
-- decidable) equality of traces the right notion.                      --
--                                                                     --
-- Traces are written using the event-sequence notation                --
--                                                                     --
--   ⟨ d₁ ⟩ ∙ ⌈ o₁ ⌉ ∙ ⟨ d₂ ⟩ ∙ ⌈ o₂ ⌉ ∙ … ∙ ⌈ oₖ ⌉ ∙ ⟨ dₖ₊₁ ⟩       --
--                                                                     --
-- built from the pure delays `⟨ d ⟩` (where `⟨ 0 ⟩` is the empty       --
-- trace `ε`), the operation events `⌈ o ⌉`, and their sequencing       --
-- `_∙_`, under which consecutive delays add up and `ε` is the unit.    --
--                                                                     --
-- A grade is then a finite, non-empty set of such timed traces, with   --
--                                                                     --
--   * the monoid multiplication the elementwise sequencing of two sets --
--     of timed traces (the language product over the timed-trace       --
--     monoid), with the singleton set `{ ε }` of the empty trace as    --
--     its unit;                                                        --
--   * the inclusion of the natural numbers sending `n` to the          --
--     singleton set `{ ⟨ n ⟩ }` of the pure delay of duration `n` --   --
--     a monoid homomorphism precisely because delays add up.           --
--                                                                     --
-- Sets of timed traces are required to be non-empty: the empty set is  --
-- an absorbing element for the language product, which would break     --
-- the zero-product property of the order (`c · d ≾ u` does not imply   --
-- `c ≾ u` when `d` is the empty set).                                  --
--                                                                     --
------------------------------------------------------------------------

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
-- operation (with no delay before it); `del d o t` prepends a positive
-- delay followed by an operation; and `fin d` is a final trailing
-- positive delay.

data Trace : Set where
  ε   : Trace
  op  : Op → Trace → Trace
  del : ℕ⁺ → Op → Trace → Trace
  fin : ℕ⁺ → Trace

-- the pure delay of duration n (a zero delay is just the empty trace)

⟨_⟩ : ℕ → Trace
⟨ zero  ⟩ = ε
⟨ suc n ⟩ = fin (1+ n)

-- a single operation event (no surrounding delay)

⌈_⌉ : Op → Trace
⌈ o ⌉ = op o ε

-- prepending a positive delay to a trace,
-- merging it with the leading delay of the trace

pre : ℕ⁺ → Trace → Trace
pre d ε           = fin d
pre d (op o t)    = del d o t
pre d (del e o t) = del (d +⁺ e) o t
pre d (fin e)     = fin (d +⁺ e)

-- sequencing of two timed traces; the trailing delay of the first trace
-- is merged with the leading delay of the second trace

infixl 7 _∙_

_∙_ : Trace → Trace → Trace
ε         ∙ t = t
op o s    ∙ t = op o (s ∙ t)
del d o s ∙ t = del d o (s ∙ t)
fin d     ∙ t = pre d t

-- the monoid laws

∙-identityˡ : (t : Trace) → (ε ∙ t) ≡ t
∙-identityˡ t = refl

∙-identityʳ : (t : Trace) → (t ∙ ε) ≡ t
∙-identityʳ ε           = refl
∙-identityʳ (op o t)    = cong (op o) (∙-identityʳ t)
∙-identityʳ (del d o t) = cong (del d o) (∙-identityʳ t)
∙-identityʳ (fin d)     = refl

-- prepending commutes with the additive merging of delays

pre-+⁺ : (d e : ℕ⁺) (u : Trace) → pre (d +⁺ e) u ≡ pre d (pre e u)
pre-+⁺ d e ε           = refl
pre-+⁺ d e (op o u)    = refl
pre-+⁺ d e (del f o u) = cong (λ z → del z o u) (+⁺-assoc d e f)
pre-+⁺ d e (fin f)     = cong fin (+⁺-assoc d e f)

-- prepending commutes with sequencing on the right

pre-∙ : (d : ℕ⁺) (t u : Trace) → ((pre d t) ∙ u) ≡ pre d (t ∙ u)
pre-∙ d ε           u = refl
pre-∙ d (op o t)    u = refl
pre-∙ d (del e o t) u = refl
pre-∙ d (fin e)     u = pre-+⁺ d e u

∙-assoc : (s t u : Trace) → ((s ∙ t) ∙ u) ≡ (s ∙ (t ∙ u))
∙-assoc ε         t u = refl
∙-assoc (op o s)  t u = cong (op o) (∙-assoc s t u)
∙-assoc (del d o s) t u = cong (del d o) (∙-assoc s t u)
∙-assoc (fin d)   t u = pre-∙ d t u

-- the timed-trace monoid is conical: a product is the
-- empty trace only if both factors are the empty trace

∙-conicalˡ : {s t : Trace} → (s ∙ t) ≡ ε → s ≡ ε
∙-conicalˡ {ε}                 _  = refl
∙-conicalˡ {op _ _}            ()
∙-conicalˡ {del _ _ _}         ()
∙-conicalˡ {fin _} {ε}         ()
∙-conicalˡ {fin _} {op _ _}    ()
∙-conicalˡ {fin _} {del _ _ _} ()
∙-conicalˡ {fin _} {fin _}     ()

∙-conicalʳ : {s t : Trace} → (s ∙ t) ≡ ε → t ≡ ε
∙-conicalʳ {ε}                 eq = eq
∙-conicalʳ {op _ _}            ()
∙-conicalʳ {del _ _ _}         ()
∙-conicalʳ {fin _} {ε}         ()
∙-conicalʳ {fin _} {op _ _}    ()
∙-conicalʳ {fin _} {del _ _ _} ()
∙-conicalʳ {fin _} {fin _}     ()

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

-- pure delays are a monoid homomorphism: adding durations corresponds
-- to sequencing the pure delays

⟨⟩-hom : (m n : ℕ) → ⟨ m + n ⟩ ≡ (⟨ m ⟩ ∙ ⟨ n ⟩)
⟨⟩-hom zero    n       = refl
⟨⟩-hom (suc m) zero    = cong (λ z → fin (1+ z)) (+-identityʳ m)
⟨⟩-hom (suc m) (suc n) = cong fin (sym (1+-+⁺ m n))

of-nat : ℕ → NeTraces
of-nat n = mkNe [ ⟨ n ⟩ ] tt

of-nat-zero : of-nat 0 ≡ u
of-nat-zero = refl

of-nat-plus : {m n : ℕ} → of-nat (m + n) ≡ (of-nat m · of-nat n)
of-nat-plus {m} {n} =
  eqNe {of-nat (m + n)} {of-nat m · of-nat n} (cong [_] (⟨⟩-hom m n))

------------------------------------------------------------------------
-- Traces have decidable equality.

module WithDecEq (_≟ₒ_ : DecidableEquality Op) where

  -- decidable (structural) equality of timed traces

  _≟ᵀ_ : DecidableEquality Trace
  ε         ≟ᵀ ε           = yes refl
  ε         ≟ᵀ op _ _      = no λ ()
  ε         ≟ᵀ del _ _ _   = no λ ()
  ε         ≟ᵀ fin _       = no λ ()
  op _ _    ≟ᵀ ε           = no λ ()
  op o s    ≟ᵀ op o' s'    with o ≟ₒ o' | s ≟ᵀ s'
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ { refl → ¬p refl }
  ... | _        | no ¬q    = no λ { refl → ¬q refl }
  op _ _    ≟ᵀ del _ _ _   = no λ ()
  op _ _    ≟ᵀ fin _       = no λ ()
  del _ _ _ ≟ᵀ ε           = no λ ()
  del _ _ _ ≟ᵀ op _ _      = no λ ()
  del d o s ≟ᵀ del d' o' s' with d ≟⁺ d' | o ≟ₒ o' | s ≟ᵀ s'
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p    | _        | _        = no λ { refl → ¬p refl }
  ... | _        | no ¬q    | _        = no λ { refl → ¬q refl }
  ... | _        | _        | no ¬r    = no λ { refl → ¬r refl }
  del _ _ _ ≟ᵀ fin _       = no λ ()
  fin _     ≟ᵀ ε           = no λ ()
  fin _     ≟ᵀ op _ _      = no λ ()
  fin _     ≟ᵀ del _ _ _   = no λ ()
  fin d     ≟ᵀ fin d'      with d ≟⁺ d'
  ... | yes refl = yes refl
  ... | no ¬p    = no λ { refl → ¬p refl }

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
  ... | yes eq = yes (eqNe eq)
  ... | no ¬eq = no λ p → ¬eq (cong traces p)
