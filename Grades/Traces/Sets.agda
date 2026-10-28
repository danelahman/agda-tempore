------------------------------------------------------------------------
-- Non-empty finite sets of timed traces, and their monoid structure.  --
--                                                                     --
-- Every trace-based grade is built from the same carrier: a non-empty  --
-- finite set of timed traces, read as a set of alternative runs. The    --
-- monoid is the language product, which sequences each trace of one     --
-- set with each trace of the other, with unit `{ ε }`. The grades       --
-- differ in the *order* they put on this carrier -- that is what the    --
-- modules under `Grades.Examples.Traces` do -- and the two-sided       --
-- grades there pair two such sets, as a floor and a cap.                --
--                                                                     --
-- A set is represented *canonically*: the underlying list is strictly  --
-- increasing for the lexicographic order `_<ᵀ_` on traces, so it       --
-- neither repeats a trace nor records the order the members were       --
-- written in. Two sets with the same members are therefore equal, and  --
-- the operations normalise their results with `nf`. This is why the    --
-- file takes the alphabet's order as a parameter: the carrier itself   --
-- depends on it.                                                       --
--                                                                     --
-- Deciding membership -- hence any order phrased through it -- needs   --
-- decidable equality of operation symbols, which the `WithDecEq`       --
-- submodule takes as a parameter rather than the whole file.           --
--                                                                     --
-- The timed traces themselves are re-exported from `Traces.Base`.      --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Decidable; DecidableEquality; Transitive; Trichotomous;
         Tri; tri<; tri≈; tri>)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Sets
  {D : Duration} (T : TimeDomain D) (Op : Set) (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base
  using (List; []; _∷_; [_]; _++_; map; cartesianProductWith)
open import Data.List.Properties
  using (++-identityʳ; map-++; map-id; map-cong;
         cartesianProductWith-distribʳ-++)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻;
         ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness; map′)

-- the timed traces the sets are made of

open import Grades.Traces.Base T Op public

open import Grades.Durations.Monus T using (Carrier; 0ᴰ; _+ᴰ_; <-irrefl)

-- and the order that puts them in a canonical sequence

open import Grades.Traces.Lexicographic T Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans public
  using (_<ᵀ_; <ᵀ-trans; <ᵀ-cmp; _<ᵀ?_)

------------------------------------------------------------------------
-- Proof irrelevance of a decided proposition
--
-- Both the canonical form below and the orders of the trace grades are
-- stated as `True` of a decision, which is `⊤` or `⊥`.

True-irr : {A : Set} (a? : Dec A) (p q : True a?) → p ≡ q
True-irr (yes _) _  _ = refl
True-irr (no  _) ()

------------------------------------------------------------------------
-- The lexicographic order is strict

<ᵀ-irrefl : {s : Trace} → s <ᵀ s → ⊥
<ᵀ-irrefl {s} p with <ᵀ-cmp s s
... | tri< _  ¬q _ = ¬q refl
... | tri≈ ¬p _  _ = ¬p p
... | tri> _  ¬q _ = ¬q refl

<ᵀ-asym : {s t : Trace} → s <ᵀ t → t <ᵀ s → ⊥
<ᵀ-asym p q = <ᵀ-irrefl (<ᵀ-trans p q)

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

------------------------------------------------------------------------
-- Canonical lists of traces
--
-- `v <* xs` puts `v` strictly below the head of `xs`, and a list is
-- canonical when each of its elements sits strictly below the rest.
-- Being *strictly* increasing, a canonical list also repeats nothing,
-- so it names its members and nothing else.

infix 4 _<*_

_<*_ : Trace → List Trace → Set
v <* []      = ⊤
v <* (x ∷ _) = True (v <ᵀ? x)

Sorted : List Trace → Set
Sorted []       = ⊤
Sorted (x ∷ xs) = (x <* xs) × Sorted xs

-- both are `True` of a decision, pointwise, hence proof-irrelevant

<*-irr : (v : Trace) (xs : List Trace) → (p q : v <* xs) → p ≡ q
<*-irr v []      tt tt = refl
<*-irr v (x ∷ _) p  q  = True-irr (v <ᵀ? x) p q

Sorted-irr : (xs : List Trace) → (p q : Sorted xs) → p ≡ q
Sorted-irr []       tt      tt        = refl
Sorted-irr (x ∷ xs) (b , s) (b' , s') =
  cong₂ _,_ (<*-irr x xs b b') (Sorted-irr xs s s')

-- on a canonical list the bound on the head bounds every member

<*-∈ : {v : Trace} {xs : List Trace}
     → v <* xs → Sorted xs → {w : Trace} → w ∈ xs → v <ᵀ w
<*-∈ {v} {x ∷ xs} b _       (here refl) = toWitness b
<*-∈ {v} {x ∷ xs} b (b' , s) (there m)  = <ᵀ-trans (toWitness b) (<*-∈ b' s m)

------------------------------------------------------------------------
-- A canonical list is determined by its members
--
-- This is what makes the representation canonical, and everything
-- below rests on it: trichotomy pins down the two heads, and the two
-- tails then have the same members in turn.

-- the two heads agree, since each sits in the other list and a member
-- other than the head is strictly above it

heads-≡ : {x y : Trace} {xs ys : List Trace}
        → y <* ys → Sorted ys → x <* xs → Sorted xs
        → x ∈ (y ∷ ys) → y ∈ (x ∷ xs) → x ≡ y
heads-≡ by sy bx sx (here eq)  _         = eq
heads-≡ by sy bx sx (there mx) (here eq) = sym eq
heads-≡ by sy bx sx (there mx) (there my) =
  ⊥-elim (<ᵀ-asym (<*-∈ bx sx my) (<*-∈ by sy mx))

-- and once they do, a member of one tail is a member of the other

tails-∈ : {x : Trace} {xs ys : List Trace}
        → x <* xs → Sorted xs
        → ({w : Trace} → w ∈ (x ∷ xs) → w ∈ (x ∷ ys))
        → {w : Trace} → w ∈ xs → w ∈ ys
tails-∈ bx sx f m with f (there m)
... | here refl = ⊥-elim (<ᵀ-irrefl (<*-∈ bx sx m))
... | there m'  = m'

sorted-ext : (xs ys : List Trace) → Sorted xs → Sorted ys
           → ({w : Trace} → w ∈ xs → w ∈ ys)
           → ({w : Trace} → w ∈ ys → w ∈ xs)
           → xs ≡ ys
sorted-ext []       []       _        _        _ _ = refl
sorted-ext []       (y ∷ ys) _        _        _ g with g (here refl)
... | ()
sorted-ext (x ∷ xs) []       _        _        f _ with f (here refl)
... | ()
sorted-ext (x ∷ xs) (y ∷ ys) (bx , sx) (by , sy) f g
  with heads-≡ by sy bx sx (f (here refl)) (g (here refl))
... | refl =
      cong (x ∷_) (sorted-ext xs ys sx sy (tails-∈ bx sx f) (tails-∈ by sy g))

------------------------------------------------------------------------
-- Normalisation
--
-- Insertion sort, dropping an element already present. The comparison
-- is passed to `insert-tri` as an argument rather than scrutinised in
-- place, so that every fact about `insert` splits the same three ways.

mutual

  insert : Trace → List Trace → List Trace
  insert w []       = w ∷ []
  insert w (x ∷ xs) = insert-tri w x xs (<ᵀ-cmp w x)

  insert-tri : (w x : Trace) (xs : List Trace)
             → Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w) → List Trace
  insert-tri w x xs (tri< _ _ _) = w ∷ x ∷ xs
  insert-tri w x xs (tri≈ _ _ _) = x ∷ xs
  insert-tri w x xs (tri> _ _ _) = x ∷ insert w xs

nf : List Trace → List Trace
nf []       = []
nf (x ∷ xs) = insert x (nf xs)

------------------------------------------------------------------------
-- What normalisation preserves

-- insertion keeps a list non-empty

insert-tri-ne : (w x : Trace) (xs : List Trace)
              → (c : Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w))
              → NonEmpty (insert-tri w x xs c)
insert-tri-ne w x xs (tri< _ _ _) = tt
insert-tri-ne w x xs (tri≈ _ _ _) = tt
insert-tri-ne w x xs (tri> _ _ _) = tt

insert-ne : (w : Trace) (xs : List Trace) → NonEmpty (insert w xs)
insert-ne w []       = tt
insert-ne w (x ∷ xs) = insert-tri-ne w x xs (<ᵀ-cmp w x)

nf-ne : (xs : List Trace) → NonEmpty xs → NonEmpty (nf xs)
nf-ne []       ()
nf-ne (x ∷ xs) _ = insert-ne x (nf xs)

-- a bound below the inserted element and below the list bounds the
-- result

insert-tri-<* : {v w x : Trace} {xs : List Trace}
              → v <ᵀ w → v <* (x ∷ xs)
              → (c : Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w))
              → v <* insert-tri w x xs c
insert-tri-<* p b (tri< _ _ _) = fromWitness p
insert-tri-<* p b (tri≈ _ _ _) = b
insert-tri-<* p b (tri> _ _ _) = b

insert-<* : {v w : Trace} {xs : List Trace}
          → v <ᵀ w → v <* xs → v <* insert w xs
insert-<* {v} {w} {[]}     p b = fromWitness p
insert-<* {v} {w} {x ∷ xs} p b = insert-tri-<* p b (<ᵀ-cmp w x)

-- insertion keeps a list canonical

mutual

  insert-sorted : (w : Trace) (xs : List Trace)
                → Sorted xs → Sorted (insert w xs)
  insert-sorted w []       _ = tt , tt
  insert-sorted w (x ∷ xs) s = insert-tri-sorted w x xs (<ᵀ-cmp w x) s

  insert-tri-sorted : (w x : Trace) (xs : List Trace)
                    → (c : Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w))
                    → Sorted (x ∷ xs) → Sorted (insert-tri w x xs c)
  insert-tri-sorted w x xs (tri< p _ _) (b , s) = fromWitness p , b , s
  insert-tri-sorted w x xs (tri≈ _ _ _) (b , s) = b , s
  insert-tri-sorted w x xs (tri> _ _ r) (b , s) =
    insert-<* {x} {w} {xs} r b , insert-sorted w xs s

nf-sorted : (xs : List Trace) → Sorted (nf xs)
nf-sorted []       = tt
nf-sorted (x ∷ xs) = insert-sorted x (nf xs) (nf-sorted xs)

------------------------------------------------------------------------
-- Normalisation keeps the members, and only them

insert-tri-∈ˡ : (w x : Trace) (xs : List Trace)
              → (c : Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w))
              → w ∈ insert w xs
              → w ∈ insert-tri w x xs c
insert-tri-∈ˡ w x xs (tri< _ _ _)    rec = here refl
insert-tri-∈ˡ w x xs (tri≈ _ refl _) rec = here refl
insert-tri-∈ˡ w x xs (tri> _ _ _)    rec = there rec

insert-∈ˡ : (w : Trace) (xs : List Trace) → w ∈ insert w xs
insert-∈ˡ w []       = here refl
insert-∈ˡ w (x ∷ xs) = insert-tri-∈ˡ w x xs (<ᵀ-cmp w x) (insert-∈ˡ w xs)

insert-tri-∈ʳ : {v : Trace} (w x : Trace) (xs : List Trace)
              → (c : Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w))
              → ({u : Trace} → u ∈ xs → u ∈ insert w xs)
              → v ∈ (x ∷ xs) → v ∈ insert-tri w x xs c
insert-tri-∈ʳ w x xs (tri< _ _ _) g m         = there m
insert-tri-∈ʳ w x xs (tri≈ _ _ _) g m         = m
insert-tri-∈ʳ w x xs (tri> _ _ _) g (here eq) = here eq
insert-tri-∈ʳ w x xs (tri> _ _ _) g (there m) = there (g m)

insert-∈ʳ : {v w : Trace} {xs : List Trace} → v ∈ xs → v ∈ insert w xs
insert-∈ʳ {v} {w} {[]}     ()
insert-∈ʳ {v} {w} {x ∷ xs} m =
  insert-tri-∈ʳ w x xs (<ᵀ-cmp w x) (λ {u} → insert-∈ʳ {u} {w} {xs}) m

mutual

  insert-∈⁻ : {v w : Trace} {xs : List Trace}
            → v ∈ insert w xs → (v ≡ w) ⊎ (v ∈ xs)
  insert-∈⁻ {v} {w} {[]}     (here eq)  = inj₁ eq
  insert-∈⁻ {v} {w} {[]}     (there ())
  insert-∈⁻ {v} {w} {x ∷ xs} m          = insert-tri-∈⁻ w x xs (<ᵀ-cmp w x) m

  insert-tri-∈⁻ : {v : Trace} (w x : Trace) (xs : List Trace)
                → (c : Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w))
                → v ∈ insert-tri w x xs c → (v ≡ w) ⊎ (v ∈ (x ∷ xs))
  insert-tri-∈⁻ w x xs (tri< _ _ _) (here eq) = inj₁ eq
  insert-tri-∈⁻ w x xs (tri< _ _ _) (there m) = inj₂ m
  insert-tri-∈⁻ w x xs (tri≈ _ _ _) m         = inj₂ m
  insert-tri-∈⁻ w x xs (tri> _ _ _) (here eq) = inj₂ (here eq)
  insert-tri-∈⁻ w x xs (tri> _ _ _) (there m) with insert-∈⁻ m
  ... | inj₁ eq = inj₁ eq
  ... | inj₂ m' = inj₂ (there m')

nf-∈⁺ : {v : Trace} {xs : List Trace} → v ∈ xs → v ∈ nf xs
nf-∈⁺ {v} {[]}     ()
nf-∈⁺ {v} {x ∷ xs} (here refl) = insert-∈ˡ v (nf xs)
nf-∈⁺ {v} {x ∷ xs} (there m)   = insert-∈ʳ (nf-∈⁺ m)

nf-∈⁻ : {v : Trace} {xs : List Trace} → v ∈ nf xs → v ∈ xs
nf-∈⁻ {v} {[]}     ()
nf-∈⁻ {v} {x ∷ xs} m with insert-∈⁻ m
... | inj₁ eq = here eq
... | inj₂ m' = there (nf-∈⁻ m')

------------------------------------------------------------------------
-- Normalisation is the identity on canonical lists

insert-tri-front : (w x : Trace) (xs : List Trace)
                 → (c : Tri (w <ᵀ x) (w ≡ x) (x <ᵀ w))
                 → w <* (x ∷ xs) → insert-tri w x xs c ≡ w ∷ x ∷ xs
insert-tri-front w x xs (tri< _ _ _)    b = refl
insert-tri-front w x xs (tri≈ _ refl _) b = ⊥-elim (<ᵀ-irrefl (toWitness b))
insert-tri-front w x xs (tri> _ _ r)    b = ⊥-elim (<ᵀ-asym (toWitness b) r)

insert-front : (w : Trace) (xs : List Trace)
             → w <* xs → insert w xs ≡ w ∷ xs
insert-front w []       b = refl
insert-front w (x ∷ xs) b = insert-tri-front w x xs (<ᵀ-cmp w x) b

nf-sorted-id : (xs : List Trace) → Sorted xs → nf xs ≡ xs
nf-sorted-id []       _       = refl
nf-sorted-id (x ∷ xs) (b , s) =
  trans (cong (insert x) (nf-sorted-id xs s)) (insert-front x xs b)

------------------------------------------------------------------------
-- The load-bearing lemma: a normal form is determined by its members

nf-ext : {xs ys : List Trace}
       → ({w : Trace} → w ∈ xs → w ∈ ys)
       → ({w : Trace} → w ∈ ys → w ∈ xs)
       → nf xs ≡ nf ys
nf-ext {xs} {ys} f g =
  sorted-ext (nf xs) (nf ys) (nf-sorted xs) (nf-sorted ys)
    (λ m → nf-∈⁺ (f (nf-∈⁻ m)))
    (λ m → nf-∈⁺ (g (nf-∈⁻ m)))

------------------------------------------------------------------------
-- Sets of traces
--
-- A grade is a non-empty (finite) set of timed traces, represented by
-- the canonical list of its members. The side conditions are implicit,
-- reducing to `⊤` at a concrete list.

record NeTraces : Set where
  constructor neTraces
  field
    traces     : List Trace
    {sorted}   : Sorted traces
    {nonempty} : NonEmpty traces

open NeTraces public

-- two sets of traces are equal as soon as their underlying lists are
-- (canonicity and non-emptiness are both irrelevant)

ne-ext : {P Q : NeTraces} → traces P ≡ traces Q → P ≡ Q
ne-ext {neTraces xs {p} {q}} {neTraces .xs {p'} {q'}} refl =
  cong₂ (λ p q → neTraces xs {p} {q}) (Sorted-irr xs p p') (NonEmpty-irr xs q q')

-- the set a non-empty list of traces denotes: its normal form

neSet : (xs : List Trace) → NonEmpty xs → NeTraces
neSet xs ne = neTraces (nf xs) {nf-sorted xs} {nf-ne xs ne}

------------------------------------------------------------------------
-- Monoid structure on sets of traces: the language product with unit { ε }

infixl 7 _·ˢ_

-- elementwise sequencing of two lists of timed traces

_·ˢ_ : List Trace → List Trace → List Trace
xs ·ˢ ys = cartesianProductWith _∙_ xs ys

-- the language product of two non-empty lists of traces is non-empty

·ˢ-ne : {xs ys : List Trace} → NonEmpty xs → NonEmpty ys → NonEmpty (xs ·ˢ ys)
·ˢ-ne {[]}     ()    _
·ˢ-ne {_ ∷ _}  {[]}  _  ()
·ˢ-ne {_ ∷ _}  {_ ∷ _} _ _ = tt

-- the unit is the singleton set containing the empty trace

u : NeTraces
u = neTraces [ ε ]

infixl 7 _·_

_·_ : NeTraces → NeTraces → NeTraces
P · Q = neSet (traces P ·ˢ traces Q) (·ˢ-ne (nonempty P) (nonempty Q))

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

------------------------------------------------------------------------
-- Membership transported across the operations
--
-- The language product and concatenation are both elementwise, so each
-- sends "the same members" to "the same members" -- which is all
-- `nf-ext` asks for.

·ˢ-∈ : {xs xs' ys ys' : List Trace}
     → ({w : Trace} → w ∈ xs → w ∈ xs')
     → ({w : Trace} → w ∈ ys → w ∈ ys')
     → {w : Trace} → w ∈ (xs ·ˢ ys) → w ∈ (xs' ·ˢ ys')
·ˢ-∈ {xs} {xs'} {ys} {ys'} f g m
  with ∈-cartesianProductWith⁻ _∙_ xs ys m
... | a , b , a∈ , b∈ , refl = ∈-cartesianProductWith⁺ _∙_ (f a∈) (g b∈)

++-∈ : {xs xs' ys ys' : List Trace}
     → ({w : Trace} → w ∈ xs → w ∈ xs')
     → ({w : Trace} → w ∈ ys → w ∈ ys')
     → {w : Trace} → w ∈ (xs ++ ys) → w ∈ (xs' ++ ys')
++-∈ {xs} {xs'} f g m with ∈-++⁻ xs m
... | inj₁ m₁ = ∈-++⁺ˡ (f m₁)
... | inj₂ m₂ = ∈-++⁺ʳ xs' (g m₂)

-- normalising an argument of either operation leaves the normal form
-- of the result alone

nf-·ˢ-nfˡ : (xs ys : List Trace) → nf (nf xs ·ˢ ys) ≡ nf (xs ·ˢ ys)
nf-·ˢ-nfˡ xs ys =
  nf-ext {nf xs ·ˢ ys} {xs ·ˢ ys}
    (·ˢ-∈ {nf xs} {xs} {ys} {ys} (λ {w} → nf-∈⁻ {w} {xs}) (λ m → m))
    (·ˢ-∈ {xs} {nf xs} {ys} {ys} (λ {w} → nf-∈⁺ {w} {xs}) (λ m → m))

nf-·ˢ-nfʳ : (xs ys : List Trace) → nf (xs ·ˢ nf ys) ≡ nf (xs ·ˢ ys)
nf-·ˢ-nfʳ xs ys =
  nf-ext {xs ·ˢ nf ys} {xs ·ˢ ys}
    (·ˢ-∈ {xs} {xs} {nf ys} {ys} (λ m → m) (λ {w} → nf-∈⁻ {w} {ys}))
    (·ˢ-∈ {xs} {xs} {ys} {nf ys} (λ m → m) (λ {w} → nf-∈⁺ {w} {ys}))

nf-++-nf : (xs ys : List Trace) → nf (nf xs ++ nf ys) ≡ nf (xs ++ ys)
nf-++-nf xs ys =
  nf-ext {nf xs ++ nf ys} {xs ++ ys}
    (++-∈ {nf xs} {xs} {nf ys} {ys}
          (λ {w} → nf-∈⁻ {w} {xs}) (λ {w} → nf-∈⁻ {w} {ys}))
    (++-∈ {xs} {nf xs} {ys} {nf ys}
          (λ {w} → nf-∈⁺ {w} {xs}) (λ {w} → nf-∈⁺ {w} {ys}))

------------------------------------------------------------------------
-- The monoid laws
--
-- Each is the corresponding law on the underlying lists, sandwiched
-- between two normalisations that `nf-ext` sees through.

·-identityʳ : (P : NeTraces) → (P · u) ≡ P
·-identityʳ P =
  ne-ext (trans (cong nf (·ˢ-identityʳ (traces P)))
                (nf-sorted-id (traces P) (sorted P)))

·-identityˡ : (P : NeTraces) → (u · P) ≡ P
·-identityˡ P =
  ne-ext (trans (cong nf (·ˢ-identityˡ (traces P)))
                (nf-sorted-id (traces P) (sorted P)))

·-assoc : (P Q R : NeTraces) → ((P · Q) · R) ≡ (P · (Q · R))
·-assoc P Q R =
  ne-ext
    (trans (nf-·ˢ-nfˡ (traces P ·ˢ traces Q) (traces R))
           (trans (cong nf (·ˢ-assoc (traces P) (traces Q) (traces R)))
                  (sym (nf-·ˢ-nfʳ (traces P) (traces Q ·ˢ traces R)))))

------------------------------------------------------------------------
-- Zero-product property of the unit

-- the only element of the unit is the empty trace

∈-[ε]⁻ : {a : Trace} → a ∈ [ ε ] → a ≡ ε
∈-[ε]⁻ (here px) = px
∈-[ε]⁻ (there ())

-- a non-empty set of traces has a witnessing trace

neHead : (xs : List Trace) → NonEmpty xs → Σ Trace (_∈ xs)
neHead (y ∷ _) _ = y , here refl
neHead []      ()

-- a canonical non-empty list whose members are all empty is the unit's

all-ε : (xs : List Trace) → Sorted xs → NonEmpty xs
      → ({w : Trace} → w ∈ xs → w ≡ ε) → xs ≡ [ ε ]
all-ε xs s ne h =
  trans (sym (nf-sorted-id xs s)) (nf-ext to from)
  where
    to : {w : Trace} → w ∈ xs → w ∈ [ ε ]
    to m = here (h m)

    from : {w : Trace} → w ∈ [ ε ] → w ∈ xs
    from {w} m with neHead xs ne
    ... | y , y∈xs = subst (_∈ xs) (trans (h y∈xs) (sym (∈-[ε]⁻ m))) y∈xs

-- if a language product is the unit, then so are both factors: each
-- member pairs with a member of the other factor, the pair is empty,
-- and the trace monoid is conical

·-zero-productˡ : {P Q : NeTraces} → (P · Q) ≡ u → P ≡ u
·-zero-productˡ {P} {Q} eq =
  ne-ext (all-ε (traces P) (sorted P) (nonempty P) step)
  where
    step : {w : Trace} → w ∈ traces P → w ≡ ε
    step {w} m with neHead (traces Q) (nonempty Q)
    ... | y , y∈Q =
          ∙-conicalˡ {w} {y}
            (∈-[ε]⁻ (subst ((w ∙ y) ∈_) (cong traces eq)
                       (nf-∈⁺ (∈-cartesianProductWith⁺ _∙_ m y∈Q))))

·-zero-productʳ : {P Q : NeTraces} → (P · Q) ≡ u → Q ≡ u
·-zero-productʳ {P} {Q} eq =
  ne-ext (all-ε (traces Q) (sorted Q) (nonempty Q) step)
  where
    step : {w : Trace} → w ∈ traces Q → w ≡ ε
    step {w} m with neHead (traces P) (nonempty P)
    ... | x , x∈P =
          ∙-conicalʳ {x} {w}
            (∈-[ε]⁻ (subst ((x ∙ w) ∈_) (cong traces eq)
                       (nf-∈⁺ (∈-cartesianProductWith⁺ _∙_ x∈P m))))

------------------------------------------------------------------------
-- Union of sets of traces
--
-- The members of both, which is the normal form of the concatenation:
-- membership in `xs ++ ys` splits, so this is a join for any order
-- phrased through membership.

infixl 6 _∪ˢ_

_∪ˢ_ : List Trace → List Trace → List Trace
xs ∪ˢ ys = nf (xs ++ ys)

-- the concatenation of two lists is non-empty as soon as the left one
-- is; the right argument is taken for uniformity with `·ˢ-ne`

++-ne : {xs ys : List Trace} → NonEmpty xs → NonEmpty ys → NonEmpty (xs ++ ys)
++-ne {[]}    ()  _
++-ne {_ ∷ _} _   _ = tt

infixl 6 _∪_

_∪_ : NeTraces → NeTraces → NeTraces
P ∪ Q = neSet (traces P ++ traces Q) (++-ne (nonempty P) (nonempty Q))

-- membership in a union is membership in one of the two

∪ˢ-∈ˡ : {w : Trace} {xs ys : List Trace} → w ∈ xs → w ∈ (xs ∪ˢ ys)
∪ˢ-∈ˡ m = nf-∈⁺ (∈-++⁺ˡ m)

∪ˢ-∈ʳ : {w : Trace} (xs : List Trace) {ys : List Trace}
      → w ∈ ys → w ∈ (xs ∪ˢ ys)
∪ˢ-∈ʳ xs m = nf-∈⁺ (∈-++⁺ʳ xs m)

∪ˢ-∈⁻ : {w : Trace} (xs : List Trace) {ys : List Trace}
      → w ∈ (xs ∪ˢ ys) → (w ∈ xs) ⊎ (w ∈ ys)
∪ˢ-∈⁻ xs m = ∈-++⁻ xs (nf-∈⁻ m)

-- the language product distributes over unions on both sides, on the
-- nose: the two sides have the same members, and a normal form is
-- determined by its members

·ˢ-distribʳ-++ : (xs ys zs : List Trace)
               → ((xs ++ ys) ·ˢ zs) ≡ ((xs ·ˢ zs) ++ (ys ·ˢ zs))
·ˢ-distribʳ-++ = cartesianProductWith-distribʳ-++ _∙_

-- on the left the two sides only permute each other

∈-·ˢ-++ˡ : {w : Trace} {xs ys zs : List Trace}
         → w ∈ (xs ·ˢ (ys ++ zs)) → w ∈ ((xs ·ˢ ys) ++ (xs ·ˢ zs))
∈-·ˢ-++ˡ {w} {xs} {ys} {zs} m
  with ∈-cartesianProductWith⁻ _∙_ xs (ys ++ zs) m
... | a , b , a∈xs , b∈ , refl with ∈-++⁻ ys b∈
...   | inj₁ b∈ys = ∈-++⁺ˡ (∈-cartesianProductWith⁺ _∙_ a∈xs b∈ys)
...   | inj₂ b∈zs = ∈-++⁺ʳ (xs ·ˢ ys) (∈-cartesianProductWith⁺ _∙_ a∈xs b∈zs)

∈-·ˢ-++ˡ⁻ : {w : Trace} {xs ys zs : List Trace}
          → w ∈ ((xs ·ˢ ys) ++ (xs ·ˢ zs)) → w ∈ (xs ·ˢ (ys ++ zs))
∈-·ˢ-++ˡ⁻ {w} {xs} {ys} {zs} m with ∈-++⁻ (xs ·ˢ ys) m
... | inj₁ m₁ = ·ˢ-∈ {xs} {xs} {ys} {ys ++ zs} (λ m' → m') ∈-++⁺ˡ m₁
... | inj₂ m₂ = ·ˢ-∈ {xs} {xs} {zs} {ys ++ zs} (λ m' → m') (∈-++⁺ʳ ys) m₂

·-distribˡ-∪ : (P Q R : NeTraces) → (P · (Q ∪ R)) ≡ ((P · Q) ∪ (P · R))
·-distribˡ-∪ P Q R =
  ne-ext
    (trans (nf-·ˢ-nfʳ (traces P) (traces Q ++ traces R))
           (trans (nf-ext (λ {w} → ∈-·ˢ-++ˡ {w} {traces P} {traces Q} {traces R})
                          (λ {w} → ∈-·ˢ-++ˡ⁻ {w} {traces P} {traces Q} {traces R}))
                  (sym (nf-++-nf (traces P ·ˢ traces Q) (traces P ·ˢ traces R)))))

·-distribʳ-∪ : (P Q R : NeTraces) → ((P ∪ Q) · R) ≡ ((P · R) ∪ (Q · R))
·-distribʳ-∪ P Q R =
  ne-ext
    (trans (nf-·ˢ-nfˡ (traces P ++ traces Q) (traces R))
           (trans (cong nf (·ˢ-distribʳ-++ (traces P) (traces Q) (traces R)))
                  (sym (nf-++-nf (traces P ·ˢ traces R) (traces Q ·ˢ traces R)))))

------------------------------------------------------------------------
-- Inclusion of durations as pure delays
--
-- A duration `τ` becomes the singleton set containing the pure delay of
-- duration `τ`, which is what a grade's `of-dur` asks for.

of-dur : Carrier → NeTraces
of-dur τ = neTraces [ ⟨ τ ⟩ ]

of-dur-zero : of-dur 0ᴰ ≡ u
of-dur-zero = ne-ext {of-dur 0ᴰ} {u} (cong [_] (⟨⟩-zero 0ᴰ <-irrefl))

of-dur-plus : {m n : Carrier} → of-dur (m +ᴰ n) ≡ (of-dur m · of-dur n)
of-dur-plus {m} {n} =
  ne-ext {of-dur (m +ᴰ n)} {of-dur m · of-dur n} (cong [_] (⟨⟩-hom m n))

------------------------------------------------------------------------
-- What decidable equality of operation symbols buys
--
-- Membership in a finite set of traces becomes decidable, and with it
-- the set-level lift `liftˢ` that every trace grade's order is an
-- instance of, and the subset preorder `_⊑_` on the underlying lists
-- (the lift at equality).

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

  -- the lift is antitone in list inclusion of the source and monotone
  -- in list inclusion of the target

  liftˢ-⊆ˡ : {R : Trace → Trace → Set} → {R? : Decidable R}
           → {xs ys zs : List Trace}
           → ({w : Trace} → w ∈ ys → w ∈ xs)
           → liftˢ R R? xs zs → liftˢ R R? ys zs
  liftˢ-⊆ˡ sub p s m = p s (fromWitness (sub (toWitness m)))

  liftˢ-⊆ʳ : {R : Trace → Trace → Set} → {R? : Decidable R}
           → {xs ys zs : List Trace}
           → ({w : Trace} → w ∈ ys → w ∈ zs)
           → liftˢ R R? xs ys → liftˢ R R? xs zs
  liftˢ-⊆ʳ {R} sub p s m with find (toWitness (p s m))
  ... | y , y∈ys , sRy =
        fromWitness (Any.map (λ eq → subst (R s) eq sRy) (sub y∈ys))

  -- normalising either side leaves the lift alone, the members being
  -- the same

  liftˢ-nfˡ : {R : Trace → Trace → Set} → {R? : Decidable R}
            → {xs ys : List Trace}
            → liftˢ R R? xs ys → liftˢ R R? (nf xs) ys
  liftˢ-nfˡ = liftˢ-⊆ˡ nf-∈⁻

  liftˢ-nfˡ⁻ : {R : Trace → Trace → Set} → {R? : Decidable R}
             → {xs ys : List Trace}
             → liftˢ R R? (nf xs) ys → liftˢ R R? xs ys
  liftˢ-nfˡ⁻ = liftˢ-⊆ˡ nf-∈⁺

  liftˢ-nfʳ : {R : Trace → Trace → Set} → {R? : Decidable R}
            → {xs ys : List Trace}
            → liftˢ R R? xs ys → liftˢ R R? xs (nf ys)
  liftˢ-nfʳ = liftˢ-⊆ʳ nf-∈⁺

  -- which is how the monotonicity of the raw language product is read
  -- at the normalising one the sets carry

  liftˢ-· : {R : Trace → Trace → Set} → (R? : Decidable R)
          → ({a a' b b' : Trace} → R a a' → R b b' → R (a ∙ b) (a' ∙ b'))
          → {xs xs' ys ys' : List Trace}
          → liftˢ R R? xs xs' → liftˢ R R? ys ys'
          → liftˢ R R? (nf (xs ·ˢ ys)) (nf (xs' ·ˢ ys'))
  liftˢ-· R? mono p q = liftˢ-nfʳ (liftˢ-nfˡ (liftˢ-·ˢ R? mono p q))

  ----------------------------------------------------------------------
  -- The union is a join for the lift
  --
  -- Membership in a union splits, so it is a least upper bound
  -- whenever the relation lifted is reflexive.

  liftˢ-∪-ubˡ : {R : Trace → Trace → Set} → (R? : Decidable R)
              → ((s : Trace) → R s s)
              → {xs ys : List Trace} → liftˢ R R? xs (xs ∪ˢ ys)
  liftˢ-∪-ubˡ R? rfl = liftˢ-⊆ʳ ∪ˢ-∈ˡ (liftˢ-refl R? rfl)

  liftˢ-∪-ubʳ : {R : Trace → Trace → Set} → (R? : Decidable R)
              → ((s : Trace) → R s s)
              → (xs : List Trace) → {ys : List Trace}
              → liftˢ R R? ys (xs ∪ˢ ys)
  liftˢ-∪-ubʳ R? rfl xs = liftˢ-⊆ʳ (∪ˢ-∈ʳ xs) (liftˢ-refl R? rfl)

  liftˢ-∪-lub : {R : Trace → Trace → Set} → {R? : Decidable R}
              → {xs ys zs : List Trace}
              → liftˢ R R? xs zs → liftˢ R R? ys zs → liftˢ R R? (xs ∪ˢ ys) zs
  liftˢ-∪-lub {xs = xs} p q s m with ∪ˢ-∈⁻ xs (toWitness m)
  ... | inj₁ s∈xs = p s (fromWitness s∈xs)
  ... | inj₂ s∈ys = q s (fromWitness s∈ys)

  -- the orders built from the lift are proof-irrelevant, pointwise --
  -- which is every trace grade's `≾-irrelevant`, one endpoint at a time

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

  -- at equality the lift is literally list inclusion: a trace related
  -- to *some* member of the right-hand list is one of its members

  ⊑-∈ : {xs ys : List Trace} → xs ⊑ ys → {w : Trace} → w ∈ xs → w ∈ ys
  ⊑-∈ p m = toWitness (p _ (fromWitness m))

  -- so mutual inclusion is equality of members, and on canonical lists
  -- that is equality

  ⊑-antisym : {xs ys : List Trace} → Sorted xs → Sorted ys
            → xs ⊑ ys → ys ⊑ xs → xs ≡ ys
  ⊑-antisym {xs} {ys} sx sy p q = sorted-ext xs ys sx sy (⊑-∈ p) (⊑-∈ q)

  -- the language product is monotone in both arguments

  ⊑-· : {xs xs' ys ys' : List Trace}
      → xs ⊑ xs' → ys ⊑ ys' → nf (xs ·ˢ ys) ⊑ nf (xs' ·ˢ ys')
  ⊑-· = liftˢ-· _≟ᵀ_ (cong₂ _∙_)

  -- the union is the join for the subset preorder

  ⊑-∪-ubˡ : {xs ys : List Trace} → xs ⊑ (xs ∪ˢ ys)
  ⊑-∪-ubˡ = liftˢ-∪-ubˡ _≟ᵀ_ (λ _ → refl)

  ⊑-∪-ubʳ : (xs : List Trace) → {ys : List Trace} → ys ⊑ (xs ∪ˢ ys)
  ⊑-∪-ubʳ = liftˢ-∪-ubʳ _≟ᵀ_ (λ _ → refl)

  ⊑-∪-lub : {xs ys zs : List Trace} → xs ⊑ zs → ys ⊑ zs → (xs ∪ˢ ys) ⊑ zs
  ⊑-∪-lub = liftˢ-∪-lub

  -- normalising either side leaves it alone

  ⊑-nfˡ⁻ : {xs ys : List Trace} → nf xs ⊑ ys → xs ⊑ ys
  ⊑-nfˡ⁻ = liftˢ-nfˡ⁻

  infix 5 _⊑?_

  _⊑?_ : (xs ys : List Trace) → Dec (xs ⊑ ys)
  _⊑?_ = liftˢ? _≟ᵀ_
