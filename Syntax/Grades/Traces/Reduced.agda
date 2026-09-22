------------------------------------------------------------------------
-- Antichain normal forms for finite sets of timed traces.             --
--                                                                     --
-- The grades that lift a trace order to sets of traces order them by  --
-- a closure: `P ≾ Q` says every member of `P` has a member of `Q`     --
-- below it, so two sets with the same closure are ordered both ways   --
-- without being the same set. The normal form that repairs this is    --
-- the antichain of the `≼`-minimal members, taken on top of the       --
-- canonical sorting `nf` that `Traces.Sets` already supplies:         --
--                                                                    --
--   n xs = nf (mins xs)                                               --
--                                                                    --
-- `mins` drops every member that has another member strictly below    --
-- it, `nf` sorts what is left and removes duplicates, and `n` is the  --
-- composite. It is idempotent, it preserves non-emptiness, and it     --
-- leaves the closure alone, so a sorted reduced list is determined by --
-- its closure and mutually-ordered sets normalise to the same list.   --
--                                                                    --
-- The order comes in as a `TracePartialOrder` rather than a `TraceOrder`, --
-- because the two handednesses are both needed: a grade that closes   --
-- upward is this module at the order, one that closes downward is it  --
-- at `flipᵖ` of the order. The unit facts of a `TraceOrder` have no    --
-- converse, and nothing here asks for them.                           --
--                                                                    --
-- `_◃_` is membership in the closure: `x ◃ xs` holds when some member --
-- of `xs` sits `≼`-below `x`. Everything is phrased through it, since --
-- it is the invariant the reduction preserves and the order reads.    --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

import Syntax.Grades.Traces.Order

module Syntax.Grades.Traces.Reduced
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (P : Syntax.Grades.Traces.Order.TracePartialOrder Op) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻;
         ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All as All using (All; all?)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _→-dec_)

-- the carrier, its canonical sorting, and the language product

open import Syntax.Grades.Traces.Sets Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans public

open WithDecEq _≟ₒ_ public

open Syntax.Grades.Traces.Order.TracePartialOrder P

------------------------------------------------------------------------
-- Closure membership
--
-- `x ◃ xs` reads "`x` is in the closure of `xs`": some member of `xs`
-- sits `≼`-below `x`. This is the whole content of the grade's order,
-- one endpoint at a time, and the reduction below is exactly the map
-- that keeps it fixed while shrinking the list.

infix 4 _◃_

_◃_ : Trace → List Trace → Set
x ◃ xs = Any (_≼ x) xs

-- a witness below `x` inside `xs` is what it takes

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
-- The inserted element is always in the closure of the result: either
-- it survives, or it was dropped in favour of something below it.

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
-- A list is reduced when no member is strictly below another: in the
-- presence of `≼-antisym` that says it is an antichain. It is stated
-- as `True` of a decision, hence proof-irrelevant, with the membership
-- form `Reducedᵐ` as the working formulation.

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
-- A sorted, reduced list is determined by its closure. This is where
-- `≼-antisym` is spent, and it is the statement that makes the
-- normalised carrier antisymmetric: `x ∈ xs` gives some `y ∈ ys` below
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

n-idem : (xs : List Trace) → n (n xs) ≡ n xs
n-idem xs =
  reduced-ext (n (n xs)) (n xs)
    (n-sorted (n xs)) (n-sorted xs) (n-reduced (n xs)) (n-reduced xs)
    (λ {v} p → n-◃ (n xs) p)
    (λ {v} p → n-◃⁻ (n xs) p)

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
