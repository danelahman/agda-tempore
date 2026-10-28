------------------------------------------------------------------------
-- The downward closure of a regular language under a letter order.   --
--                                                                    --
-- Given a relation `R` on letters, `↓ L` holds the words that lie    --
-- letter by letter `R`-below some word of `L`. It is a subset        --
-- construction: state `S` stands for the words lying below a word    --
-- accepted from one of the states in `S`, and a letter `a` moves     --
-- each state along every letter above `a`.                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; z≤n)

module Grades.Regular.Closure (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.List.Base using (List; []; _∷_; map; concatMap; length; tabulate)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Properties using (length-map)
open import Data.List.Membership.Propositional using (find; lose)
  renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-allFin)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any
import Data.Nat.Base
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Grades.Regular.Automaton k
open import Grades.Regular.Basics k using (T-subst; _∘⇔_)
open import Grades.Regular.Canonical k
open import Grades.Regular.Canonicity k
  using (canon-idempotent; normalise-wf; normalise-accepts)
open import Grades.Regular.Explore k using (explore-wf)
open import Grades.Regular.Operations k using (fromList)
open import Grades.Regular.Constructions.Base k

open Equivalence using (to; from)

module _ (R : Letter → Letter → Bool) where

  -- the letters above a letter

  above : Letter → List Letter → List Letter
  above a []       = []
  above a (b ∷ bs) = if R a b then b ∷ above a bs else above a bs

  ∈-above⁺ : ∀ a {b} bs → T (R a b) → b ∈ˡ bs → b ∈ˡ above a bs
  ∈-above⁺ a {b} (c ∷ bs) r (here refl) with R a c
  ... | true  = here refl
  ∈-above⁺ a {b} (c ∷ bs) () (here refl) | false
  ∈-above⁺ a (c ∷ bs) r (there b∈) with R a c
  ... | true  = there (∈-above⁺ a bs r b∈)
  ... | false = ∈-above⁺ a bs r b∈

  ∈-above⁻ : ∀ a {b} bs → b ∈ˡ above a bs → T (R a b)
  ∈-above⁻ a (c ∷ bs) b∈ with R a c in e
  ∈-above⁻ a (c ∷ bs) (here refl) | true = subst T (sym e) _
  ∈-above⁻ a (c ∷ bs) (there b∈)  | true = ∈-above⁻ a bs b∈
  ∈-above⁻ a (c ∷ bs) b∈          | false = ∈-above⁻ a bs b∈

  -- letter by letter below

  Below : Word → Word → Set
  Below = Pointwise (λ a b → T (R a b))

  -- the letters above each letter, tabulated once, so that a closure
  -- computes them once

  above-table : List (List Letter)
  above-table = map (λ a → above a letters) letters

  aboveᵗ : List (List Letter) → Letter → List Letter
  aboveᵗ t a = lookupOr [] t (toℕ a)

  aboveᵗ-correct : ∀ a → aboveᵗ above-table a ≡ above a letters
  aboveᵗ-correct a = lookup-tabulate (λ b → b) a
    where
      lookup-tabulate : ∀ {m} (g : Fin m → Letter) (i : Fin m)
                      → lookupOr [] (map (λ b → above b letters) (tabulate g)) (toℕ i)
                        ≡ above (g i) letters
      lookup-tabulate g zero    = refl
      lookup-tabulate g (suc i) = lookup-tabulate (λ j → g (suc j)) i

  module CloseWith (t : List (List Letter)) (L : DFA) where

    step : List ℕ → Letter → List ℕ
    step S a = fromList (concatMap (λ q → map (next L q) (aboveᵗ t a)) S)

    closure : Automaton
    closure = record
      { State = List ℕ
      ; _≟_   = _==ⁿ_
      ; start = 0 ∷ []
      ; δ     = step
      ; final = any (isFinal L)
      ; bound = 2 Data.Nat.Base.^ size L
      }

  module Close (L : DFA) = CloseWith above-table L

  ↓ : DFA → DFA
  ↓ L = normalise (CloseWith.closure above-table L)

  ----------------------------------------------------------------------
  -- Correctness

  module _ (L : DFA) where

    private
      open Close L
      open Automaton closure using (δ*)

      _∈[_] : Word → ℕ → Set
      u ∈[ q ] = T (isFinal L (run L q u))

      Sem : List ℕ → Word → Set
      Sem S w = Any (λ q → ∃ λ v → Below w v × v ∈[ q ]) S

      cm⁻ : ∀ {P : ℕ → Set} (f : ℕ → List ℕ) S → Any P (concatMap f S) → Any (λ q → Any P (f q)) S
      cm⁻ f S x = Any.map⁻ (Any.concat⁻ (map f S) x)

      cm⁺ : ∀ {P : ℕ → Set} (f : ℕ → List ℕ) {S} → Any (λ q → Any P (f q)) S → Any P (concatMap f S)
      cm⁺ f x = Any.concat⁺ (Any.map⁺ x)

      step⁻ : ∀ S a {w} → Sem (step S a) w → Sem S (a ∷ w)
      step⁻ S a {w} x with find (any-fromList⁻ _ x)
      ... | p , p∈ , v , wv , v∈ with find (cm⁻ {P = _≡ p} (λ q → map (next L q) (aboveᵗ above-table a)) S (lose p∈ refl))
      ...   | q , q∈ , m with find (Any.map⁻ {f = next L q} m)
      ...     | b , b∈ , e = lose q∈ (b ∷ v , ∈-above⁻ a letters (subst (b ∈ˡ_) (aboveᵗ-correct a) b∈) ∷ wv , subst (λ r → v ∈[ r ]) (sym e) v∈)

      step⁺ : ∀ S a {w} → Sem S (a ∷ w) → Sem (step S a) w
      step⁺ S a {w} x with find x
      ... | q , q∈ , (b ∷ v) , (r ∷ wv) , v∈ =
        any-fromList⁺ (concatMap f S)
          (Any.map (λ {r′} e → v , wv , subst (λ z → v ∈[ z ]) (sym e) v∈) hit)
        where
          f : ℕ → List ℕ
          f q′ = map (next L q′) (aboveᵗ above-table a)
          hit : Any (_≡ next L q b) (concatMap f S)
          hit = cm⁺ {P = _≡ next L q b} f
                  (lose q∈ (Any.map⁺ {f = next L q} (lose (subst (b ∈ˡ_) (sym (aboveᵗ-correct a)) (∈-above⁺ a letters r (∈-allFin b))) refl)))

      accepts-from : ∀ S w → T (any (isFinal L) (δ* S w)) ⇔ Sem S w
      accepts-from S [] = mk⇔ to′ from′
        where
          to′ : T (any (isFinal L) S) → Sem S []
          to′ t = Any.map (λ fin → [] , [] , fin) (T-any⁻ (isFinal L) S t)
          from′ : Sem S [] → T (any (isFinal L) S)
          from′ x = T-any⁺ (isFinal L) (Any.map (λ { ([] , [] , fin) → fin }) x)
      accepts-from S (a ∷ w) =
        mk⇔ (λ t → step⁻ S a (to (accepts-from (step S a) w) t))
            (λ x → from (accepts-from (step S a) w) (step⁺ S a x))

    accepts-closure : ∀ w → T (Automaton.accepts (Close.closure L) w) ⇔ (∃ λ v → Below w v × v ∈ L)
    accepts-closure w =
      mk⇔ (λ t → single (to (accepts-from (0 ∷ []) w) t))
          (λ x → from (accepts-from (0 ∷ []) w) (here x))
      where
        single : Sem (0 ∷ []) w → ∃ λ v → Below w v × v ∈ L
        single (here x) = x

  ----------------------------------------------------------------------
  -- Lawfulness: `Good` sets are strictly increasing and in range

  module _ (L : DFA) (wf : WellFormed L) where

    private
      open Close L

      Good : List ℕ → Set
      Good S = Increasing S × All (_< size L) S

      good-δ : ∀ {S} a → Good S → Good (step S a)
      good-δ {S} a (_ , S<) =
        fromList-increasing (concatMap (λ q → map (next L q) (aboveᵗ above-table a)) S) ,
        fromList-all (concatMap (λ q → map (next L q) (aboveᵗ above-table a)) S) (all-concatMap S S<)
        where
          all-concatMap : ∀ S → All (_< size L) S
                        → All (_< size L) (concatMap (λ q → map (next L q) (aboveᵗ above-table a)) S)
          all-concatMap []      []         = []
          all-concatMap (q ∷ S) (q< ∷ S<) =
            AllP.++⁺ (all-map (aboveᵗ above-table a)) (all-concatMap S S<)
            where
              all-map : ∀ bs → All (_< size L) (map (next L q) bs)
              all-map []       = []
              all-map (b ∷ bs) = next-< L wf q< b ∷ all-map bs

      enum : List (List ℕ)
      enum = subsets (range 0 (size L))

      length-enum : length enum ≡ 2 Data.Nat.Base.^ size L
      length-enum = trans (length-subsets (range 0 (size L)))
                          (cong (2 Data.Nat.Base.^_) (length-range 0 (size L)))

      cover : ∀ {S} → Good S → S ∈ˡ enum
      cover (inc , S<) = ∈-subsets 0 (size L) inc (All.map (λ _ → z≤n) S<) S<

    lawful-closure : Lawful (Close.closure L)
    lawful-closure =
      lawful-exact (Close.closure L) (λ {S} {S′} → ==ⁿ-sound S S′) ==ⁿ-refl Good
        (([] ∷ []) , (proj₁ wf ∷ [])) good-δ enum (≤-reflexive length-enum) cover

  ----------------------------------------------------------------------
  -- The closure on tables

  module _ {L : DFA} (wfL : WellFormed L) where

    private
      A  = Close.closure L
      LA = lawful-closure L wfL

    ↓-wf : WellFormed (↓ L)
    ↓-wf = normalise-wf A LA

    ↓-canonical : canon (↓ L) ≡ ↓ L
    ↓-canonical = canon-idempotent (explore A) (explore-wf A LA)

    ∈-↓ : ∀ w → w ∈ ↓ L ⇔ (∃ λ v → Below w v × v ∈ L)
    ∈-↓ w = accepts-closure L w ∘⇔ T-subst (normalise-accepts A LA w)
