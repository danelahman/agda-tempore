-----------------------------------------------------------------------------
-- Antichains of timed traces, and the grade structure they carry.         --
--                                                                         --
-- The grades that lift a trace order to sets of traces order them by      --
-- a closure: `P ≾ Q` says every member of `P` has a member of `Q`         --
-- below it, so two sets with the same closure are ordered both ways       --
-- without being the same set. The normal form that repairs this is        --
-- the antichain of the `≼`-minimal members, composed with the             --
-- canonical sorting `nf` of `Traces.Sets`:                                --
--                                                                         --
--   n xs = nf (mins xs)                                                   --
--                                                                         --
-- `mins` drops every member that has another member strictly below        --
-- it, `nf` sorts what is left and removes duplicates, and `n` is the      --
-- composite. It is idempotent, it preserves non-emptiness, and it         --
-- leaves the closure alone, so a sorted reduced list is determined by     --
-- its closure and mutually-ordered sets normalise to the same list.       --
--                                                                         --
-- The order comes in as a `TracePartialOrder` rather than a `TraceOrder`, --
-- because the two handednesses are both needed: a grade that closes       --
-- upward is this module at the order, one that closes downward is it      --
-- at `flipᵖ` of the order. The unit facts of a `TraceOrder` have no       --
-- converse, and nothing here asks for them.                               --
--                                                                         --
-- `_◃_` is membership in the closure: `x ◃ xs` holds when some member     --
-- of `xs` sits `≼`-below `x`. Everything is phrased through it, since     --
-- it is the invariant the reduction preserves and the order reads.        --
--                                                                         --
-- The antichains carry a grade: the carrier `Antichain`, the language     --
-- product with unit `{ ε }`, the order                                    --
--                                                                         --
--   P ≾ Q   iff   every member of `P` lies in the closure of `Q`          --
--                                                                         --
-- and the union as its join. One definition of the order serves           --
-- both handednesses: at the order it reads "each member of `P` has        --
-- a member of `Q` below it", and at `flipᵖ` of the order it reads         --
-- "above", which is the other grade. It is a partial order,               --
-- antisymmetry being `reduced-ext`, which is what the reduction is        --
-- for. Of `Traces.Sets` only the list-level machinery is used.            --
-----------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Decidable; DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

import Grades.Traces.Order

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Reduced
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (P : Grades.Traces.Order.TracePartialOrder T Op) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻;
         ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _→-dec_)

-- the timed traces, their canonical sorting, and the list-level
-- language product; the set-level monoid of `Traces.Sets` is left out,
-- the antichains carrying their own

open import Grades.Traces.Sets T Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans public
  hiding (NeTraces; neTraces; traces; sorted; nonempty; ne-ext; neSet;
          𝟏; _·_; _∪_; ·-identityˡ; ·-identityʳ; ·-assoc;
          ·-distribˡ-∪; ·-distribʳ-∪; ·-zero-productˡ; ·-zero-productʳ;
          ι; ι-zero; ι-plus)

open WithDecEq _≟ₒ_ public

open import Grades.Durations.Monus T using (Carrier; 0ᴰ; _+ᴰ_; <-irrefl)

open Grades.Traces.Order.TracePartialOrder P

------------------------------------------------------------------------
-- Closure membership
--
-- `x ◃ xs` reads "`x` is in the closure of `xs`": some member of `xs`
-- sits `≼`-below `x`. It is the grade's order, one member at a time,
-- and the reduction below shrinks a list keeping it fixed.

infix 4 _◃_

_◃_ : Trace → List Trace → Set
x ◃ xs = Any (_≼ x) xs

-- a member of `xs` below `x` puts `x` in the closure

◃-intro : {x y : Trace} {xs : List Trace} → y ∈ xs → y ≼ x → x ◃ xs
◃-intro {x} m p = Any.map (λ eq → subst (_≼ x) eq p) m

-- so a member is in the closure, by reflexivity

◃-∈ : {x : Trace} {xs : List Trace} → x ∈ xs → x ◃ xs
◃-∈ {x} m = ◃-intro m (≼-refl x)

-- and the closure is monotone in list inclusion

◃-⊆ : {xs ys : List Trace}
    → ({w : Trace} → w ∈ xs → w ∈ ys)
    → {v : Trace} → v ◃ xs → v ◃ ys
◃-⊆ f p with find p
... | y , y∈xs , y≼v = ◃-intro (f y∈xs) y≼v

------------------------------------------------------------------------
-- The reduction
--
-- Insertion of `w` into a list, dropping whichever of `w` and the
-- members it meets is the larger. The two decisions are passed to
-- `ins-dec` as arguments rather than scrutinised in place, so that
-- every fact about `ins` splits the same three ways.

mutual

  ins : Trace → List Trace → List Trace
  ins w []       = w ∷ []
  ins w (x ∷ xs) = ins-dec w x xs (x ≼? w) (w ≼? x)

  ins-dec : (w x : Trace) (xs : List Trace)
          → Dec (x ≼ w) → Dec (w ≼ x) → List Trace
  ins-dec w x xs (yes _) _       = x ∷ xs
  ins-dec w x xs (no _) (yes _)  = ins w xs
  ins-dec w x xs (no _) (no _)   = x ∷ ins w xs

-- the antichain of minimal members, by the insert-fold

mins : List Trace → List Trace
mins []       = []
mins (x ∷ xs) = ins x (mins xs)

------------------------------------------------------------------------
-- The reduction only removes members

mutual

  ins-∈⁻ : {v w : Trace} {xs : List Trace}
         → v ∈ ins w xs → (v ≡ w) ⊎ (v ∈ xs)
  ins-∈⁻ {v} {w} {[]}     (here eq)  = inj₁ eq
  ins-∈⁻ {v} {w} {[]}     (there ())
  ins-∈⁻ {v} {w} {x ∷ xs} m          = ins-dec-∈⁻ w x xs (x ≼? w) (w ≼? x) m

  ins-dec-∈⁻ : {v : Trace} (w x : Trace) (xs : List Trace)
             → (c : Dec (x ≼ w)) (d : Dec (w ≼ x))
             → v ∈ ins-dec w x xs c d → (v ≡ w) ⊎ (v ∈ (x ∷ xs))
  ins-dec-∈⁻ w x xs (yes _) d       m         = inj₂ m
  ins-dec-∈⁻ w x xs (no _) (yes _)  m         with ins-∈⁻ m
  ... | inj₁ eq = inj₁ eq
  ... | inj₂ m' = inj₂ (there m')
  ins-dec-∈⁻ w x xs (no _) (no _)   (here eq) = inj₂ (here eq)
  ins-dec-∈⁻ w x xs (no _) (no _)   (there m) with ins-∈⁻ m
  ... | inj₁ eq = inj₁ eq
  ... | inj₂ m' = inj₂ (there m')

mins-⊆ : {x : Trace} {xs : List Trace} → x ∈ mins xs → x ∈ xs
mins-⊆ {x} {[]}     ()
mins-⊆ {x} {y ∷ ys} m with ins-∈⁻ {x} {y} {mins ys} m
... | inj₁ eq = here eq
... | inj₂ m' = there (mins-⊆ m')

------------------------------------------------------------------------
-- Every member is covered
--
-- The inserted element is in the closure of the result: it survives,
-- or is dropped for something below it.

mutual

  ins-◃ˡ : (w : Trace) (xs : List Trace) → w ◃ ins w xs
  ins-◃ˡ w []       = here (≼-refl w)
  ins-◃ˡ w (x ∷ xs) = ins-dec-◃ˡ w x xs (x ≼? w) (w ≼? x)

  ins-dec-◃ˡ : (w x : Trace) (xs : List Trace)
             → (c : Dec (x ≼ w)) (d : Dec (w ≼ x))
             → w ◃ ins-dec w x xs c d
  ins-dec-◃ˡ w x xs (yes p) d      = here p
  ins-dec-◃ˡ w x xs (no _) (yes _) = ins-◃ˡ w xs
  ins-dec-◃ˡ w x xs (no _) (no _)  = there (ins-◃ˡ w xs)

-- and insertion never loses a closure member: a dropped element is
-- dropped only because the inserted one is below it

mutual

  ins-◃ʳ : (w : Trace) {v : Trace} (xs : List Trace) → v ◃ xs → v ◃ ins w xs
  ins-◃ʳ w []       ()
  ins-◃ʳ w (x ∷ xs) p = ins-dec-◃ʳ w x xs (x ≼? w) (w ≼? x) p

  ins-dec-◃ʳ : (w x : Trace) {v : Trace} (xs : List Trace)
             → (c : Dec (x ≼ w)) (d : Dec (w ≼ x))
             → v ◃ (x ∷ xs) → v ◃ ins-dec w x xs c d
  ins-dec-◃ʳ w x xs (yes _) d       p         = p
  ins-dec-◃ʳ w x xs (no _) (yes q)  (here r)  =
    Any.map (λ z≼w → ≼-trans z≼w (≼-trans q r)) (ins-◃ˡ w xs)
  ins-dec-◃ʳ w x xs (no _) (yes _)  (there p) = ins-◃ʳ w xs p
  ins-dec-◃ʳ w x xs (no _) (no _)   (here r)  = here r
  ins-dec-◃ʳ w x xs (no _) (no _)   (there p) = there (ins-◃ʳ w xs p)

mins-cover : {x : Trace} {xs : List Trace} → x ∈ xs → x ◃ mins xs
mins-cover {x} {[]}     ()
mins-cover {x} {y ∷ ys} (here refl) = ins-◃ˡ x (mins ys)
mins-cover {x} {y ∷ ys} (there m)   = ins-◃ʳ y (mins ys) (mins-cover m)

------------------------------------------------------------------------
-- The reduction leaves the closure alone

mins-◃ : {x : Trace} {xs : List Trace} → x ◃ mins xs → x ◃ xs
mins-◃ {x} {xs} = ◃-⊆ (λ {w} → mins-⊆ {w} {xs})

mins-◃⁻ : {x : Trace} {xs : List Trace} → x ◃ xs → x ◃ mins xs
mins-◃⁻ p with find p
... | y , y∈xs , y≼x = Any.map (λ z≼y → ≼-trans z≼y y≼x) (mins-cover y∈xs)

------------------------------------------------------------------------
-- Reducedness
--
-- A list is reduced when no member is strictly below another, which
-- given `≼-antisym` makes it an antichain. It is `True` of a decision,
-- hence proof-irrelevant; the proofs use the membership form
-- `Reducedᵐ`.

Reducedᵐ : List Trace → Set
Reducedᵐ xs = {x y : Trace} → x ∈ xs → y ∈ xs → y ≼ x → x ≼ y

reduced? : (xs : List Trace)
         → Dec (All (λ x → All (λ y → y ≼ x → x ≼ y) xs) xs)
reduced? xs = all? (λ x → all? (λ y → (y ≼? x) →-dec (x ≼? y)) xs) xs

Reduced : List Trace → Set
Reduced xs = True (reduced? xs)

Reduced-irr : (xs : List Trace) → (p q : Reduced xs) → p ≡ q
Reduced-irr xs = True-irr (reduced? xs)

reduced-to : {xs : List Trace} → Reduced xs → Reducedᵐ xs
reduced-to r mx my = All.lookup (All.lookup (toWitness r) mx) my

reduced-from : {xs : List Trace} → Reducedᵐ xs → Reduced xs
reduced-from f =
  fromWitness (All.tabulate (λ mx → All.tabulate (λ my → f mx my)))

------------------------------------------------------------------------
-- The reduction is reduced
--
-- The incomparable case of the insertion is the one with content: the
-- head survives, and it is incomparable with `w` by the case
-- hypotheses and with the rest by the invariant.

ins-red-incomp : (w x : Trace) (xs : List Trace)
               → ¬ (x ≼ w) → ¬ (w ≼ x)
               → Reducedᵐ (x ∷ xs) → Reducedᵐ (ins w xs)
               → Reducedᵐ (x ∷ ins w xs)
ins-red-incomp w x xs ¬p ¬q r rec (here refl) (here refl) le = ≼-refl x
ins-red-incomp w x xs ¬p ¬q r rec (here refl) (there mv)  le
  with ins-∈⁻ {_} {w} {xs} mv
... | inj₁ refl = ⊥-elim (¬q le)
... | inj₂ mv'  = r (here refl) (there mv') le
ins-red-incomp w x xs ¬p ¬q r rec (there mu)  (here refl) le
  with ins-∈⁻ {_} {w} {xs} mu
... | inj₁ refl = ⊥-elim (¬p le)
... | inj₂ mu'  = r (there mu') (here refl) le
ins-red-incomp w x xs ¬p ¬q r rec (there mu)  (there mv)  le = rec mu mv le

mutual

  ins-red : (w : Trace) (xs : List Trace) → Reducedᵐ xs → Reducedᵐ (ins w xs)
  ins-red w []       r (here refl) (here refl) le = ≼-refl w
  ins-red w []       r (here refl) (there ())  le
  ins-red w []       r (there ())  mv          le
  ins-red w (x ∷ xs) r = ins-dec-red w x xs (x ≼? w) (w ≼? x) r

  ins-dec-red : (w x : Trace) (xs : List Trace)
              → (c : Dec (x ≼ w)) (d : Dec (w ≼ x))
              → Reducedᵐ (x ∷ xs) → Reducedᵐ (ins-dec w x xs c d)
  ins-dec-red w x xs (yes _) d       r = r
  ins-dec-red w x xs (no _) (yes _)  r =
    ins-red w xs (λ mu mv → r (there mu) (there mv))
  ins-dec-red w x xs (no ¬p) (no ¬q) r =
    ins-red-incomp w x xs ¬p ¬q r
      (ins-red w xs (λ mu mv → r (there mu) (there mv)))

mins-reducedᵐ : (xs : List Trace) → Reducedᵐ (mins xs)
mins-reducedᵐ []       ()
mins-reducedᵐ (x ∷ xs) = ins-red x (mins xs) (mins-reducedᵐ xs)

mins-reduced : (xs : List Trace) → Reduced (mins xs)
mins-reduced xs = reduced-from (mins-reducedᵐ xs)

------------------------------------------------------------------------
-- The reduction keeps a set non-empty

mutual

  ins-ne : (w : Trace) (xs : List Trace) → NonEmpty (ins w xs)
  ins-ne w []       = tt
  ins-ne w (x ∷ xs) = ins-dec-ne w x xs (x ≼? w) (w ≼? x)

  ins-dec-ne : (w x : Trace) (xs : List Trace)
             → (c : Dec (x ≼ w)) (d : Dec (w ≼ x))
             → NonEmpty (ins-dec w x xs c d)
  ins-dec-ne w x xs (yes _) d      = tt
  ins-dec-ne w x xs (no _) (yes _) = ins-ne w xs
  ins-dec-ne w x xs (no _) (no _)  = tt

mins-ne : (xs : List Trace) → NonEmpty xs → NonEmpty (mins xs)
mins-ne []       ()
mins-ne (x ∷ xs) _ = ins-ne x (mins xs)

------------------------------------------------------------------------
-- Canonicity
--
-- A sorted, reduced list is determined by its closure; this spends
-- `≼-antisym` and makes the normalised carrier antisymmetric:
-- `x ∈ xs` gives some `y ∈ ys` below
-- it, which in turn gives some `x' ∈ xs` below `y`; reducedness of
-- `xs` turns `x' ≼ x` into `x ≼ x'`, hence `x ≼ y`, and antisymmetry
-- identifies them.

reduced-extᵐ : (xs ys : List Trace)
             → Sorted xs → Sorted ys → Reducedᵐ xs → Reducedᵐ ys
             → ({v : Trace} → v ◃ xs → v ◃ ys)
             → ({v : Trace} → v ◃ ys → v ◃ xs)
             → xs ≡ ys
reduced-extᵐ xs ys sx sy rx ry f g = sorted-ext xs ys sx sy to from
  where
    to : {w : Trace} → w ∈ xs → w ∈ ys
    to m with find (f (◃-∈ m))
    ... | y , y∈ys , y≼w with find (g (◃-∈ y∈ys))
    ...   | x' , x'∈xs , x'≼y =
            subst (_∈ ys)
              (sym (≼-antisym
                     (≼-trans (rx m x'∈xs (≼-trans x'≼y y≼w)) x'≼y) y≼w))
              y∈ys

    from : {w : Trace} → w ∈ ys → w ∈ xs
    from m with find (g (◃-∈ m))
    ... | x , x∈xs , x≼w with find (f (◃-∈ x∈xs))
    ...   | y' , y'∈ys , y'≼x =
            subst (_∈ xs)
              (sym (≼-antisym
                     (≼-trans (ry m y'∈ys (≼-trans y'≼x x≼w)) y'≼x) x≼w))
              x∈xs

reduced-ext : (xs ys : List Trace)
            → Sorted xs → Sorted ys → Reduced xs → Reduced ys
            → ({v : Trace} → v ◃ xs → v ◃ ys)
            → ({v : Trace} → v ◃ ys → v ◃ xs)
            → xs ≡ ys
reduced-ext xs ys sx sy rx ry =
  reduced-extᵐ xs ys sx sy (reduced-to rx) (reduced-to ry)

------------------------------------------------------------------------
-- The closure is compatible with the two operations
--
-- Both are stated as maps between closures of related lists, which is
-- what the normalisation laws below consume. `mono-∙` is spent in the
-- first: a member of the product decomposes, each factor is pulled
-- down, and the two witnesses recombine.

◃-·ˢ : {xs xs' ys ys' : List Trace}
     → ({v : Trace} → v ◃ xs → v ◃ xs')
     → ({v : Trace} → v ◃ ys → v ◃ ys')
     → {v : Trace} → v ◃ (xs ·ˢ ys) → v ◃ (xs' ·ˢ ys')
◃-·ˢ {xs} {xs'} {ys} {ys'} f g p with find p
... | w , w∈ , w≼v with ∈-cartesianProductWith⁻ _∙_ xs ys w∈
...   | a , b , a∈xs , b∈ys , refl
        with find (f (◃-∈ a∈xs)) | find (g (◃-∈ b∈ys))
...     | a' , a'∈ , a'≼a | b' , b'∈ , b'≼b =
          ◃-intro (∈-cartesianProductWith⁺ _∙_ a'∈ b'∈)
                  (≼-trans (mono-∙ a'≼a b'≼b) w≼v)

◃-++ : {xs xs' ys ys' : List Trace}
     → ({v : Trace} → v ◃ xs → v ◃ xs')
     → ({v : Trace} → v ◃ ys → v ◃ ys')
     → {v : Trace} → v ◃ (xs ++ ys) → v ◃ (xs' ++ ys')
◃-++ {xs} {xs'} f g p with find p
... | w , w∈ , w≼v with ∈-++⁻ xs w∈
...   | inj₁ m₁ = ◃-⊆ ∈-++⁺ˡ (f (◃-intro m₁ w≼v))
...   | inj₂ m₂ = ◃-⊆ (∈-++⁺ʳ xs') (g (◃-intro m₂ w≼v))

-- the reduction's own instances

mins-·ˢ : (xs ys : List Trace) {v : Trace}
        → v ◃ (mins xs ·ˢ mins ys) → v ◃ (xs ·ˢ ys)
mins-·ˢ xs ys = ◃-·ˢ (λ {v} → mins-◃ {v} {xs}) (λ {v} → mins-◃ {v} {ys})

mins-·ˢ⁻ : (xs ys : List Trace) {v : Trace}
         → v ◃ (xs ·ˢ ys) → v ◃ (mins xs ·ˢ mins ys)
mins-·ˢ⁻ xs ys = ◃-·ˢ (λ {v} → mins-◃⁻ {v} {xs}) (λ {v} → mins-◃⁻ {v} {ys})

mins-++ : (xs ys : List Trace) {v : Trace}
        → v ◃ (mins xs ++ mins ys) → v ◃ (xs ++ ys)
mins-++ xs ys = ◃-++ (λ {v} → mins-◃ {v} {xs}) (λ {v} → mins-◃ {v} {ys})

mins-++⁻ : (xs ys : List Trace) {v : Trace}
         → v ◃ (xs ++ ys) → v ◃ (mins xs ++ mins ys)
mins-++⁻ xs ys = ◃-++ (λ {v} → mins-◃⁻ {v} {xs}) (λ {v} → mins-◃⁻ {v} {ys})

------------------------------------------------------------------------
-- The canonical sorting sees none of this
--
-- `nf` keeps the members and only them, so both reducedness and the
-- closure transport across it.

nf-◃ : {v : Trace} {xs : List Trace} → v ◃ nf xs → v ◃ xs
nf-◃ {v} {xs} = ◃-⊆ (λ {w} → nf-∈⁻ {w} {xs})

nf-◃⁻ : {v : Trace} {xs : List Trace} → v ◃ xs → v ◃ nf xs
nf-◃⁻ {v} {xs} = ◃-⊆ (λ {w} → nf-∈⁺ {w} {xs})

nf-reducedᵐ : {xs : List Trace} → Reducedᵐ xs → Reducedᵐ (nf xs)
nf-reducedᵐ r mu mv = r (nf-∈⁻ mu) (nf-∈⁻ mv)

nf-reduced : {xs : List Trace} → Reduced xs → Reduced (nf xs)
nf-reduced r = reduced-from (nf-reducedᵐ (reduced-to r))

------------------------------------------------------------------------
-- The normal form
--
-- The antichain of the minimal members, held in the canonical sorted
-- order. This is the map a normalised carrier of sets of traces is
-- built from.

n : List Trace → List Trace
n xs = nf (mins xs)

n-sorted : (xs : List Trace) → Sorted (n xs)
n-sorted xs = nf-sorted (mins xs)

n-reduced : (xs : List Trace) → Reduced (n xs)
n-reduced xs = nf-reduced (mins-reduced xs)

n-ne : (xs : List Trace) → NonEmpty xs → NonEmpty (n xs)
n-ne xs ne = nf-ne (mins xs) (mins-ne xs ne)

n-◃ : (xs : List Trace) {v : Trace} → v ◃ n xs → v ◃ xs
n-◃ xs p = mins-◃ (nf-◃ p)

n-◃⁻ : (xs : List Trace) {v : Trace} → v ◃ xs → v ◃ n xs
n-◃⁻ xs p = nf-◃⁻ (mins-◃⁻ p)

-- the normal form only ever removes members

n-∈⁻ : {v : Trace} {xs : List Trace} → v ∈ n xs → v ∈ xs
n-∈⁻ {v} {xs} m = mins-⊆ {v} {xs} (nf-∈⁻ {v} {mins xs} m)

-- `nf` is determined by its members, `n` by its closure

n-ext : {xs ys : List Trace}
      → ({v : Trace} → v ◃ xs → v ◃ ys)
      → ({v : Trace} → v ◃ ys → v ◃ xs)
      → n xs ≡ n ys
n-ext {xs} {ys} f g =
  reduced-ext (n xs) (n ys)
    (n-sorted xs) (n-sorted ys) (n-reduced xs) (n-reduced ys)
    (λ {v} p → n-◃⁻ ys (f (n-◃ xs p)))
    (λ {v} p → n-◃⁻ xs (g (n-◃ ys p)))

-- so it is the identity on a list that is already sorted and reduced,
-- and idempotent because its output is

n-reduced-id : (xs : List Trace) → Sorted xs → Reduced xs → n xs ≡ xs
n-reduced-id xs s r =
  reduced-ext (n xs) xs (n-sorted xs) s (n-reduced xs) r
    (λ {v} → n-◃ xs) (λ {v} → n-◃⁻ xs)

n-idem : (xs : List Trace) → n (n xs) ≡ n xs
n-idem xs = n-reduced-id (n xs) (n-sorted xs) (n-reduced xs)

------------------------------------------------------------------------
-- Normalisation is compatible with the monoid structure
--
-- These are the shapes the associativity and unit laws of the grade are
-- proved at: normalising a factor before multiplying leaves the normal
-- form of the result alone.

n-·ˢ : (xs ys : List Trace) → n (n xs ·ˢ n ys) ≡ n (xs ·ˢ ys)
n-·ˢ xs ys =
  reduced-ext (n (n xs ·ˢ n ys)) (n (xs ·ˢ ys))
    (n-sorted (n xs ·ˢ n ys)) (n-sorted (xs ·ˢ ys))
    (n-reduced (n xs ·ˢ n ys)) (n-reduced (xs ·ˢ ys)) to from
  where
    to : {v : Trace} → v ◃ n (n xs ·ˢ n ys) → v ◃ n (xs ·ˢ ys)
    to p =
      n-◃⁻ (xs ·ˢ ys)
        (◃-·ˢ (λ {v} → n-◃ xs) (λ {v} → n-◃ ys) (n-◃ (n xs ·ˢ n ys) p))

    from : {v : Trace} → v ◃ n (xs ·ˢ ys) → v ◃ n (n xs ·ˢ n ys)
    from p =
      n-◃⁻ (n xs ·ˢ n ys)
        (◃-·ˢ (λ {v} → n-◃⁻ xs) (λ {v} → n-◃⁻ ys) (n-◃ (xs ·ˢ ys) p))

-- normalising one factor at a time, which is the shape associativity
-- is read at, both factors of a product of antichains already being
-- normal

n-·ˢ-nˡ : (xs ys : List Trace) → n (n xs ·ˢ ys) ≡ n (xs ·ˢ ys)
n-·ˢ-nˡ xs ys =
  n-ext {n xs ·ˢ ys} {xs ·ˢ ys}
    (◃-·ˢ {n xs} {xs} {ys} {ys} (λ {v} → n-◃ xs) (λ {v} p → p))
    (◃-·ˢ {xs} {n xs} {ys} {ys} (λ {v} → n-◃⁻ xs) (λ {v} p → p))

n-·ˢ-nʳ : (xs ys : List Trace) → n (xs ·ˢ n ys) ≡ n (xs ·ˢ ys)
n-·ˢ-nʳ xs ys =
  n-ext {xs ·ˢ n ys} {xs ·ˢ ys}
    (◃-·ˢ {xs} {xs} {n ys} {ys} (λ {v} p → p) (λ {v} → n-◃ ys))
    (◃-·ˢ {xs} {xs} {ys} {n ys} (λ {v} p → p) (λ {v} → n-◃⁻ ys))

n-++ : (xs ys : List Trace) → n (n xs ++ n ys) ≡ n (xs ++ ys)
n-++ xs ys =
  reduced-ext (n (n xs ++ n ys)) (n (xs ++ ys))
    (n-sorted (n xs ++ n ys)) (n-sorted (xs ++ ys))
    (n-reduced (n xs ++ n ys)) (n-reduced (xs ++ ys)) to from
  where
    to : {v : Trace} → v ◃ n (n xs ++ n ys) → v ◃ n (xs ++ ys)
    to p =
      n-◃⁻ (xs ++ ys)
        (◃-++ (λ {v} → n-◃ xs) (λ {v} → n-◃ ys) (n-◃ (n xs ++ n ys) p))

    from : {v : Trace} → v ◃ n (xs ++ ys) → v ◃ n (n xs ++ n ys)
    from p =
      n-◃⁻ (n xs ++ n ys)
        (◃-++ (λ {v} → n-◃⁻ xs) (λ {v} → n-◃⁻ ys) (n-◃ (xs ++ ys) p))

-- the unit laws hold on the nose already, the language product with
-- `{ ε }` being the identity on lists

n-identityʳ : (xs : List Trace) → n (xs ·ˢ [ ε ]) ≡ n xs
n-identityʳ xs = cong n (·ˢ-identityʳ xs)

n-identityˡ : (xs : List Trace) → n ([ ε ] ·ˢ xs) ≡ n xs
n-identityˡ xs = cong n (·ˢ-identityˡ xs)

------------------------------------------------------------------------
-- Antichains of timed traces
--
-- A grade is a non-empty finite set of traces cut down to its
-- `≼`-minimal members, held in the canonical sorted order. All three
-- side conditions are `True` of a decision, hence proof-irrelevant and
-- implicit: at a concrete list they reduce to `⊤`, so an antichain is
-- written by its underlying list alone.

record Antichain : Set where
  constructor antichain
  field
    traces     : List Trace
    {sorted}   : Sorted traces
    {reduced}  : Reduced traces
    {nonempty} : NonEmpty traces

open Antichain public

-- two antichains are equal as soon as their underlying lists are

ac-ext : {P Q : Antichain} → traces P ≡ traces Q → P ≡ Q
ac-ext {antichain xs {s} {r} {ne}} {antichain .xs {s'} {r'} {ne'}} refl =
  cong₃ (λ s r ne → antichain xs {s} {r} {ne})
    (Sorted-irr xs s s') (Reduced-irr xs r r') (NonEmpty-irr xs ne ne')

-- the antichain a non-empty list of traces denotes: its normal form

acSet : (xs : List Trace) → NonEmpty xs → Antichain
acSet xs ne =
  antichain (n xs) {n-sorted xs} {n-reduced xs} {n-ne xs ne}

-- a singleton is an antichain already, nothing being below anything
-- else in it

singleton-reduced : (t : Trace) → Reduced [ t ]
singleton-reduced t = reduced-from step
  where
    step : Reducedᵐ [ t ]
    step (here refl) (here refl) le = ≼-refl t
    step (here refl) (there ())  le
    step (there ())  mv          le

singleton : Trace → Antichain
singleton t = antichain [ t ] {reduced = singleton-reduced t}

------------------------------------------------------------------------
-- Monoid structure: the language product with unit { ε }
--
-- Each law is the corresponding law on the underlying lists, sandwiched
-- between normalisations that `n` sees through. The factors of a
-- product are antichains already, which is why the one-sided
-- normalisation lemmas are the ones associativity reads.

infixl 7 _·_

_·_ : Antichain → Antichain → Antichain
P · Q = acSet (traces P ·ˢ traces Q) (·ˢ-ne (nonempty P) (nonempty Q))

𝟏 : Antichain
𝟏 = singleton ε

·-identityʳ : (P : Antichain) → (P · 𝟏) ≡ P
·-identityʳ P =
  ac-ext (trans (n-identityʳ (traces P))
                (n-reduced-id (traces P) (sorted P) (reduced P)))

·-identityˡ : (P : Antichain) → (𝟏 · P) ≡ P
·-identityˡ P =
  ac-ext (trans (n-identityˡ (traces P))
                (n-reduced-id (traces P) (sorted P) (reduced P)))

·-assoc : (P Q R : Antichain) → ((P · Q) · R) ≡ (P · (Q · R))
·-assoc P Q R =
  ac-ext
    (trans (n-·ˢ-nˡ (traces P ·ˢ traces Q) (traces R))
           (trans (cong n (·ˢ-assoc (traces P) (traces Q) (traces R)))
                  (sym (n-·ˢ-nʳ (traces P) (traces Q ·ˢ traces R)))))

------------------------------------------------------------------------
-- The order
--
-- `P ≾ Q` says every member of `P` lies in the closure of `Q`: some
-- member of `Q` sits `≼`-below each member of `P`. At `flipᵖ` of the
-- order that reads "above", so this one definition, with every law
-- proved of it, serves a grade of either handedness.
--
-- It is `Sets.liftˢ` at the converse comparison, so that the lift's
-- decidability, proof-irrelevance and antitonicity in the source apply
-- to it unchanged.

infix 4 _≽_

_≽_ : Trace → Trace → Set
s ≽ t = t ≼ s

_≽?_ : Decidable _≽_
s ≽? t = t ≼? s

≽-trans : {s t v : Trace} → s ≽ t → t ≽ v → s ≽ v
≽-trans p q = ≼-trans q p

infix 5 _≾ˢ_

_≾ˢ_ : List Trace → List Trace → Set
_≾ˢ_ = liftˢ _≽_ _≽?_

-- at this relation the lift is closure membership, one member of the
-- left-hand list at a time

≾ˢ-◃ : {xs ys : List Trace} → xs ≾ˢ ys → {v : Trace} → v ∈ xs → v ◃ ys
≾ˢ-◃ {xs} {ys} p {v} m = toWitness (p v (fromWitness m))

◃-≾ˢ : {xs ys : List Trace} → ({v : Trace} → v ∈ xs → v ◃ ys) → xs ≾ˢ ys
◃-≾ˢ f s m = fromWitness (f (toWitness m))

-- and members in a closure compose to closures included, by one step of
-- transitivity

◃-trans : {xs ys : List Trace}
        → ({w : Trace} → w ∈ xs → w ◃ ys)
        → {v : Trace} → v ◃ xs → v ◃ ys
◃-trans f p with find p
... | y , y∈xs , y≼v = Any.map (λ z≼y → ≼-trans z≼y y≼v) (f y∈xs)

infix 5 _≾_

_≾_ : Antichain → Antichain → Set
P ≾ Q = traces P ≾ˢ traces Q

≾-refl : {P : Antichain} → P ≾ P
≾-refl {P} = liftˢ-refl _≽?_ ≼-refl {traces P}

≾-trans : {P Q R : Antichain} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {P} {Q} {R} =
  liftˢ-trans _≽?_ ≽-trans {traces P} {traces Q} {traces R}

------------------------------------------------------------------------
-- Antisymmetry
--
-- Mutual `≾` is mutual closure inclusion, by one step of `◃-trans`
-- each way, and a sorted reduced list is determined by its closure.
-- The un-reduced carrier of `Traces.Sets` lacks this law.

≾-antisym : {P Q : Antichain} → P ≾ Q → Q ≾ P → P ≡ Q
≾-antisym {P} {Q} p q =
  ac-ext
    (reduced-ext (traces P) (traces Q)
       (sorted P) (sorted Q) (reduced P) (reduced Q)
       (◃-trans {traces P} {traces Q} (λ {w} → ≾ˢ-◃ p {w}))
       (◃-trans {traces Q} {traces P} (λ {w} → ≾ˢ-◃ q {w})))

------------------------------------------------------------------------
-- The language product is monotone in each argument
--
-- Normalising either side leaves the order alone: the source only loses
-- members, and the target keeps its closure. So the monotonicity of the
-- raw language product is read at the normalising one the antichains
-- carry.

≾ˢ-nˡ : {xs ys : List Trace} → xs ≾ˢ ys → n xs ≾ˢ ys
≾ˢ-nˡ {xs} {ys} = liftˢ-⊆ˡ (λ {w} → n-∈⁻ {w} {xs})

≾ˢ-nʳ : {xs ys : List Trace} → xs ≾ˢ ys → xs ≾ˢ n ys
≾ˢ-nʳ {xs} {ys} p = ◃-≾ˢ {xs} {n ys} (λ {v} m → n-◃⁻ ys (≾ˢ-◃ p m))

≾ˢ-· : {xs xs' ys ys' : List Trace}
     → xs ≾ˢ xs' → ys ≾ˢ ys' → n (xs ·ˢ ys) ≾ˢ n (xs' ·ˢ ys')
≾ˢ-· {xs} {xs'} {ys} {ys'} p q =
  ≾ˢ-nʳ {n (xs ·ˢ ys)} {xs' ·ˢ ys'}
    (≾ˢ-nˡ {xs ·ˢ ys} {xs' ·ˢ ys'} (liftˢ-·ˢ _≽?_ mono-∙ p q))

·-monoˡ : {C P Q : Antichain} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≾ˢ-· {traces P} {traces Q} {traces C} {traces C} rel (≾-refl {C})

·-monoʳ : {C P Q : Antichain} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≾ˢ-· {traces C} {traces C} {traces P} {traces Q} (≾-refl {C}) rel

------------------------------------------------------------------------
-- The order is decidable and proof-irrelevant
--
-- Both are `liftˢ`'s, the relation lifted being decided and the lift
-- being stated as `True` of a decision.

infix 5 _≾?_

_≾?_ : (P Q : Antichain) → Dec (P ≾ Q)
P ≾? Q = liftˢ? _≽?_ (traces P) (traces Q)

≾-irrelevant : {P Q : Antichain} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- Binary joins
--
-- The two member lists concatenated and reduced. A member of either
-- lies in the closure of the union, which is the upper-bound half; a
-- member of the union is a member of one of the two, which is the
-- least-upper-bound half.

infixl 6 _⊔_

_⊔_ : Antichain → Antichain → Antichain
P ⊔ Q = acSet (traces P ++ traces Q) (++-ne (nonempty P) (nonempty Q))

⊔-ubˡ : (P Q : Antichain) → P ≾ (P ⊔ Q)
⊔-ubˡ P Q =
  ◃-≾ˢ {traces P} {n (traces P ++ traces Q)}
    (λ {v} m → n-◃⁻ (traces P ++ traces Q) (◃-∈ (∈-++⁺ˡ m)))

⊔-ubʳ : (P Q : Antichain) → Q ≾ (P ⊔ Q)
⊔-ubʳ P Q =
  ◃-≾ˢ {traces Q} {n (traces P ++ traces Q)}
    (λ {v} m → n-◃⁻ (traces P ++ traces Q) (◃-∈ (∈-++⁺ʳ (traces P) m)))

⊔-lub : {P Q R : Antichain} → P ≾ R → Q ≾ R → (P ⊔ Q) ≾ R
⊔-lub {P} {Q} {R} p q = ◃-≾ˢ {n (traces P ++ traces Q)} {traces R} step
  where
    step : {v : Trace} → v ∈ n (traces P ++ traces Q) → v ◃ traces R
    step {v} m with ∈-++⁻ (traces P) (n-∈⁻ {v} {traces P ++ traces Q} m)
    ... | inj₁ m₁ = ≾ˢ-◃ p m₁
    ... | inj₂ m₂ = ≾ˢ-◃ q m₂

-- the language product distributes over the join on the nose: the two
-- sides have the same closure, and an antichain is determined by its
-- closure

·-distribˡ-⊔ : (C P Q : Antichain) → (C · (P ⊔ Q)) ≡ ((C · P) ⊔ (C · Q))
·-distribˡ-⊔ C P Q =
  ac-ext (n-ext {cs ·ˢ n (ps ++ qs)} {n (cs ·ˢ ps) ++ n (cs ·ˢ qs)} to from)
  where
    cs = traces C
    ps = traces P
    qs = traces Q

    to : {v : Trace}
       → v ◃ (cs ·ˢ n (ps ++ qs))
       → v ◃ (n (cs ·ˢ ps) ++ n (cs ·ˢ qs))
    to p =
      ◃-++ {cs ·ˢ ps} {n (cs ·ˢ ps)} {cs ·ˢ qs} {n (cs ·ˢ qs)}
           (λ {w} → n-◃⁻ (cs ·ˢ ps)) (λ {w} → n-◃⁻ (cs ·ˢ qs))
           (◃-⊆ (λ {w} → ∈-·ˢ-++ˡ {w} {cs} {ps} {qs})
                (◃-·ˢ {cs} {cs} {n (ps ++ qs)} {ps ++ qs}
                      (λ {w} r → r) (λ {w} → n-◃ (ps ++ qs)) p))

    from : {v : Trace}
         → v ◃ (n (cs ·ˢ ps) ++ n (cs ·ˢ qs))
         → v ◃ (cs ·ˢ n (ps ++ qs))
    from p =
      ◃-·ˢ {cs} {cs} {ps ++ qs} {n (ps ++ qs)}
           (λ {w} r → r) (λ {w} → n-◃⁻ (ps ++ qs))
           (◃-⊆ (λ {w} → ∈-·ˢ-++ˡ⁻ {w} {cs} {ps} {qs})
                (◃-++ {n (cs ·ˢ ps)} {cs ·ˢ ps} {n (cs ·ˢ qs)} {cs ·ˢ qs}
                      (λ {w} → n-◃ (cs ·ˢ ps)) (λ {w} → n-◃ (cs ·ˢ qs)) p))

·-distribʳ-⊔ : (C P Q : Antichain) → ((P ⊔ Q) · C) ≡ ((P · C) ⊔ (Q · C))
·-distribʳ-⊔ C P Q =
  ac-ext (n-ext {n (ps ++ qs) ·ˢ cs} {n (ps ·ˢ cs) ++ n (qs ·ˢ cs)} to from)
  where
    cs = traces C
    ps = traces P
    qs = traces Q

    split : ((ps ++ qs) ·ˢ cs) ≡ ((ps ·ˢ cs) ++ (qs ·ˢ cs))
    split = ·ˢ-distribʳ-++ ps qs cs

    to : {v : Trace}
       → v ◃ (n (ps ++ qs) ·ˢ cs)
       → v ◃ (n (ps ·ˢ cs) ++ n (qs ·ˢ cs))
    to {v} p =
      ◃-++ {ps ·ˢ cs} {n (ps ·ˢ cs)} {qs ·ˢ cs} {n (qs ·ˢ cs)}
           (λ {w} → n-◃⁻ (ps ·ˢ cs)) (λ {w} → n-◃⁻ (qs ·ˢ cs))
           (subst (v ◃_) split
             (◃-·ˢ {n (ps ++ qs)} {ps ++ qs} {cs} {cs}
                   (λ {w} → n-◃ (ps ++ qs)) (λ {w} r → r) p))

    from : {v : Trace}
         → v ◃ (n (ps ·ˢ cs) ++ n (qs ·ˢ cs))
         → v ◃ (n (ps ++ qs) ·ˢ cs)
    from {v} p =
      ◃-·ˢ {ps ++ qs} {n (ps ++ qs)} {cs} {cs}
           (λ {w} → n-◃⁻ (ps ++ qs)) (λ {w} r → r)
           (subst (v ◃_) (sym split)
             (◃-++ {n (ps ·ˢ cs)} {ps ·ˢ cs} {n (qs ·ˢ cs)} {qs ·ˢ cs}
                   (λ {w} → n-◃ (ps ·ˢ cs)) (λ {w} → n-◃ (qs ·ˢ cs)) p))

------------------------------------------------------------------------
-- Inclusion of durations as pure delays
--
-- A duration `τ` becomes the singleton antichain containing the pure
-- delay of duration `τ`, which is what a grade's `ι` asks for.

ι : Carrier → Antichain
ι τ = singleton ⟨ τ ⟩

ι-zero : ι 0ᴰ ≡ 𝟏
ι-zero = ac-ext {ι 0ᴰ} {𝟏} (cong [_] (⟨⟩-zero 0ᴰ <-irrefl))

ι-plus : {m k : Carrier} → ι (m +ᴰ k) ≡ (ι m · ι k)
ι-plus {m} {k} =
  ac-ext {ι (m +ᴰ k)} {ι m · ι k} (cong [_] (⟨⟩-hom m k))
