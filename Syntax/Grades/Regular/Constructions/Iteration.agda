------------------------------------------------------------------------
-- Kleene star: the set construction is lawful, and its language is   --
-- the iteration of the language.                                     --
--                                                                    --
-- State `nothing` stands for `L *`; state `just S` for               --
-- `⋃_{q ∈ S} L_q · L *`. The sets built are closed: `0 ∈ S` whenever --
-- some member is final, which lets `S` restart after a completed     --
-- factor.                                                            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _≤_; _<_; z≤n; s≤s)

module Syntax.Grades.Regular.Constructions.Iteration (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (length-map)
open import Data.List.Membership.Propositional using (find; lose)
  renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
import Data.Nat.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Operations k
  using (insert; fromList; iteration; module Iteration)
open import Syntax.Grades.Regular.Constructions.Base k

------------------------------------------------------------------------
-- Iterated membership

data _∈*_ (w : Word) (L : DFA) : Set where
  none : w ≡ [] → w ∈* L
  more : ∀ u v → w ≡ u ++ v → u ∈ L → v ∈* L → w ∈* L

module _ (L : DFA) where

  private
    I : Automaton
    I = iteration L

    open Automaton I using (δ*)
    open Iteration L using (close; accepting; same)

    _∈[_] : Word → ℕ → Set
    u ∈[ q ] = T (isFinal L (run L q u))

    -- words `u ++ v` with `u` accepted from `q` and `v` iterated

    Tail : Word → ℕ → Set
    Tail w q = ∃₂ λ u v → w ≡ u ++ v × u ∈[ q ] × v ∈* L

    Sem : Maybe (List ℕ) → Word → Set
    Sem nothing  w = w ∈* L
    Sem (just S) w = Any (Tail w) S

    Closed : List ℕ → Set
    Closed S = Any (λ q → T (isFinal L q)) S → 0 ∈ˡ S

    closed-close : ∀ X → Closed (close X)
    closed-close X with any (isFinal L) X in e
    ... | true  = λ _ → ∈-insert⁺ˡ 0 X
    ... | false = λ a → ⊥-elim (T-false e (T-any⁺ (isFinal L) a))

    -- the first factor of a non-empty iterated word is non-empty

    star-derivative : ∀ {a w} → (a ∷ w) ∈* L → Tail w (next L 0 a)
    star-derivative (none ())
    star-derivative (more []      v refl u∈ v*) = star-derivative v*
    star-derivative (more (b ∷ u) v refl u∈ v*) = u , v , refl , u∈ , v*

    tail-star : ∀ {a w} → Tail w (next L 0 a) → (a ∷ w) ∈* L
    tail-star {a} (u , v , eq , u∈ , v*) = more (a ∷ u) v (cong (a ∷_) eq) u∈ v*

    -- closing a set does not change what it stands for

    sem-close : ∀ X w → Sem (just (close X)) w ⇔ Sem (just X) w
    sem-close X w with any (isFinal L) X in e
    ... | false = mk⇔ (λ x → x) (λ x → x)
    ... | true  = mk⇔ to (any-insert⁺ʳ 0 X)
      where
      to : Any (Tail w) (insert 0 X) → Any (Tail w) X
      to x with any-insert⁻ 0 X x
      ... | inj₂ y = y
      ... | inj₁ (u , v , eq , u∈ , v*) =
        Any.map (λ fin → [] , w , refl , fin , more u v eq u∈ v*)
                (T-any⁻ (isFinal L) X (T-true e))

    -- the transition on `just S` is the derivative

    derivative : ∀ S a w → Closed S
               → Sem (just (fromList (map (λ q → next L q a) S))) w ⇔ Sem (just S) (a ∷ w)
    derivative S a w cl = mk⇔ to from
      where
      to : Any (Tail w) (fromList (map (λ q → next L q a) S)) → Any (Tail (a ∷ w)) S
      to x = Any.map (λ { (u , v , eq , u∈ , v*) → a ∷ u , v , cong (a ∷_) eq , u∈ , v* })
                     (Any.map⁻ (any-fromList⁻ (map (λ q → next L q a) S) x))

      from : Any (Tail (a ∷ w)) S → Any (Tail w) (fromList (map (λ q → next L q a) S))
      from x = any-fromList⁺ (map (λ q → next L q a) S) (Any.map⁺ (go (find x)))
        where
        go : (∃ λ q → q ∈ˡ S × Tail (a ∷ w) q) → Any (λ q → Tail w (next L q a)) S
        go (q , q∈ , (b ∷ u) , v , refl , u∈ , v*) = lose q∈ (u , v , refl , u∈ , v*)
        go (q , q∈ , []      , v , refl , fin , v*) =
          lose (cl (lose q∈ fin)) (star-derivative v*)

    accepts-just : ∀ S → Closed S → ∀ w → T (accepting (δ* (just S) w)) ⇔ Sem (just S) w
    accepts-just S cl [] = mk⇔ to from
      where
      to : T (any (isFinal L) S) → Any (Tail []) S
      to t = Any.map (λ fin → [] , [] , refl , fin , none refl) (T-any⁻ (isFinal L) S t)

      from : Any (Tail []) S → T (any (isFinal L) S)
      from x = T-any⁺ (isFinal L)
                 (Any.map (λ { ([] , v , _ , fin , _) → fin ; (b ∷ u , v , () , _) }) x)
    accepts-just S cl (a ∷ w) =
      let S′  = fromList (map (λ q → next L q a) S)
          ih  = accepts-just (close S′) (closed-close S′) w
          cls = sem-close S′ w
          der = derivative S a w cl
      in mk⇔ (λ t → Equivalence.to der (Equivalence.to cls (Equivalence.to ih t)))
             (λ x → Equivalence.from ih (Equivalence.from cls (Equivalence.from der x)))

    accepts-nothing : ∀ w → T (accepting (δ* nothing w)) ⇔ (w ∈* L)
    accepts-nothing [] = mk⇔ (λ _ → none refl) (λ _ → tt)
    accepts-nothing (a ∷ w) =
      let X   = next L 0 a ∷ []
          ih  = accepts-just (close X) (closed-close X) w
          cls = sem-close X w
      in mk⇔ (λ t → single (Equivalence.to cls (Equivalence.to ih t)))
             (λ x → Equivalence.from ih (Equivalence.from cls (here (star-derivative x))))
      where
      single : Any (Tail w) (next L 0 a ∷ []) → (a ∷ w) ∈* L
      single (here t) = tail-star t

  accepts-iteration′ : ∀ w → T (Automaton.accepts I w) ⇔ (w ∈* L)
  accepts-iteration′ = accepts-nothing

accepts-iteration : ∀ L → WellFormed L → ∀ w
                  → T (Automaton.accepts (iteration L) w) ⇔ w ∈* L
accepts-iteration L _ = accepts-iteration′ L

------------------------------------------------------------------------
-- Lawfulness: `Good` sets are strictly increasing and in range

module _ (L : DFA) (wf : WellFormed L) where

  private
    I : Automaton
    I = iteration L

    open Iteration L using (close; same)

    Good : Maybe (List ℕ) → Set
    Good nothing  = ⊤
    Good (just S) = Increasing S × All (_< size L) S

    0<L : 0 < size L
    0<L = proj₁ wf

    good-close : ∀ {X} → Increasing X → All (_< size L) X → Good (just (close X))
    good-close {X} inc X< with any (isFinal L) X
    ... | true  = insert-increasing 0 X inc , insert-all 0 X 0<L X<
    ... | false = inc , X<

    good-δ : ∀ {s} a → Good s → Good (Automaton.δ I s a)
    good-δ {nothing} a _ = good-close ([] ∷ []) (next-< L wf 0<L a ∷ [])
    good-δ {just S}  a (inc , S<) =
      good-close (fromList-increasing (map (λ q → next L q a) S))
        (fromList-all (map (λ q → next L q a) S)
          (All.map⁺ (All.map (λ q< → next-< L wf q< a) S<)))

    same⇒≡ : ∀ {s t} → T (same s t) → s ≡ t
    same⇒≡ {nothing} {nothing} _ = refl
    same⇒≡ {just S}  {just T}  t = cong just (==ⁿ-sound S T t)

    same-refl : ∀ s → T (same s s)
    same-refl nothing  = tt
    same-refl (just S) = ==ⁿ-refl S

    enum : List (Maybe (List ℕ))
    enum = nothing ∷ map just (subsets (range 0 (size L)))

    length-enum : length enum ≡ suc (2 Data.Nat.Base.^ size L)
    length-enum =
      cong suc (trans (length-map just (subsets (range 0 (size L))))
                 (trans (length-subsets (range 0 (size L)))
                        (cong (2 Data.Nat.Base.^_) (length-range 0 (size L)))))

    cover : ∀ {s} → Good s → s ∈ˡ enum
    cover {nothing} _          = here refl
    cover {just S}  (inc , S<) =
      there (∈-map⁺ just (∈-subsets 0 (size L) inc (All.map (λ _ → z≤n) S<) S<))

  lawful-iteration′ : Lawful I
  lawful-iteration′ =
    lawful-exact I same⇒≡ same-refl Good tt good-δ
      enum (≤-reflexive length-enum) cover

lawful-iteration : ∀ L → WellFormed L → Lawful (iteration L)
lawful-iteration = lawful-iteration′
