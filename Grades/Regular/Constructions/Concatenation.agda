-------------------------------------------------------------------------
-- Concatenation: the subset construction is lawful, and its language  --
-- is the product of languages.                                        --
--                                                                     --
-- State `(p , S)` stands for `L_p · M ∪ ⋃_{q ∈ S} M_q`; the invariant --
-- `0 ∈ S` whenever `p` is final lets `S` absorb the case where the    --
-- `L`-part is empty.                                                  --
-------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _≤_; _<_; z≤n; s≤s)

module Grades.Regular.Constructions.Concatenation (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; T)
open import Data.Bool.Properties using (T-∧)
open import Data.List.Base using (List; []; _∷_; _++_; map)
import Data.List.Base
import Data.Nat.Base
open import Data.List.Membership.Propositional using (lose)
  renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.AllPairs using ([])
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≤-reflexive)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Grades.Regular.Automaton k
open import Grades.Regular.Operations k
  using (insert; fromList; concatenation; module Concatenation)
open import Grades.Regular.Constructions.Base k

module _ (L M : DFA) where

  private
    C : Automaton
    C = concatenation (automaton L) M

    open Automaton C using (δ*)
    open Concatenation (automaton L) M using (enter)

    -- acceptance from a state of a table

    _∈[_]_ : Word → DFA → ℕ → Set
    u ∈[ D ] p = T (isFinal D (run D p u))

    State = ℕ × List ℕ

    Sem : State → Word → Set
    Sem (p , S) w = (∃₂ λ u v → w ≡ u ++ v × u ∈[ L ] p × v ∈[ M ] 0)
                  ⊎ Any (λ q → w ∈[ M ] q) S

    Inv : State → Set
    Inv (p , S) = T (isFinal L p) → 0 ∈ˡ S

    inv-enter : ∀ p S → Inv (enter p S)
    inv-enter p S with isFinal L p
    ... | true  = λ _ → ∈-insert⁺ˡ 0 S
    ... | false = λ ()

    any-enter⁻ : ∀ {P : ℕ → Set} p S → Any P (proj₂ (enter p S))
               → (T (isFinal L p) × P 0) ⊎ Any P S
    any-enter⁻ p S a with isFinal L p
    ... | false = inj₂ a
    ... | true with any-insert⁻ 0 S a
    ...   | inj₁ p0 = inj₁ (_ , p0)
    ...   | inj₂ aS = inj₂ aS

    any-enter⁺ : ∀ {P : ℕ → Set} p S → Any P S → Any P (proj₂ (enter p S))
    any-enter⁺ p S a with isFinal L p
    ... | false = a
    ... | true  = any-insert⁺ʳ 0 S a

    -- the successors of a set of states, as a set

    step : List ℕ → Letter → List ℕ
    step S a = fromList (map (λ q → next M q a) S)

    any-step⁻ : ∀ {w} S a → Any (λ q → w ∈[ M ] q) (step S a)
              → Any (λ q → (a ∷ w) ∈[ M ] q) S
    any-step⁻ S a x = Any.map⁻ (any-fromList⁻ (map (λ q → next M q a) S) x)

    any-step⁺ : ∀ {w} S a → Any (λ q → (a ∷ w) ∈[ M ] q) S
              → Any (λ q → w ∈[ M ] q) (step S a)
    any-step⁺ S a x = any-fromList⁺ (map (λ q → next M q a) S) (Any.map⁺ x)

    -- the transition is the derivative

    derivative : ∀ p S a w → Inv (p , S)
               → Sem (enter (next L p a) (step S a)) w ⇔ Sem (p , S) (a ∷ w)
    derivative p S a w inv = mk⇔ to from
      where
      to : Sem (enter (next L p a) (step S a)) w → Sem (p , S) (a ∷ w)
      to (inj₁ (u , v , refl , u∈ , v∈)) = inj₁ (a ∷ u , v , refl , u∈ , v∈)
      to (inj₂ x) with any-enter⁻ (next L p a) (step S a) x
      ... | inj₁ (fin , w∈) = inj₁ (a ∷ [] , w , refl , fin , w∈)
      ... | inj₂ y          = inj₂ (any-step⁻ {w = w} S a y)

      from : Sem (p , S) (a ∷ w) → Sem (enter (next L p a) (step S a)) w
      from (inj₁ ([]    , v , refl , u∈ , v∈)) =
        inj₂ (any-enter⁺ (next L p a) (step S a)
               (any-step⁺ {w = w} S a (lose (inv u∈) v∈)))
      from (inj₁ (b ∷ u , v , refl , u∈ , v∈)) = inj₁ (u , v , refl , u∈ , v∈)
      from (inj₂ x) =
        inj₂ (any-enter⁺ (next L p a) (step S a) (any-step⁺ {w = w} S a x))

    accepts-from : ∀ p S → Inv (p , S) → ∀ w
                 → T (Automaton.final C (δ* (p , S) w)) ⇔ Sem (p , S) w
    accepts-from p S inv [] = mk⇔ to from
      where
      to : T (Automaton.final C (p , S)) → Sem (p , S) []
      to t = inj₂ (T-any⁻ (isFinal M) S t)

      from : Sem (p , S) [] → T (Automaton.final C (p , S))
      from (inj₁ ([] , [] , refl , u∈ , v∈)) = T-any⁺ (isFinal M) (lose (inv u∈) v∈)
      from (inj₂ x) = T-any⁺ (isFinal M) x
    accepts-from p S inv (a ∷ w)
      with enter (next L p a) (step S a) in e
    ... | (p′ , S′) =
      let ih  = accepts-from p′ S′ (subst-inv e) w
          der = derivative p S a w inv
      in mk⇔ (λ t → Equivalence.to der (subst-sem e (Equivalence.to ih t)))
             (λ s → Equivalence.from ih (subst-sem′ e (Equivalence.from der s)))
      where
      subst-inv : ∀ {s} → enter (next L p a) (step S a) ≡ s → Inv s
      subst-inv refl = inv-enter (next L p a) (step S a)
      subst-sem : ∀ {s} → enter (next L p a) (step S a) ≡ s → Sem s w
                → Sem (enter (next L p a) (step S a)) w
      subst-sem refl x = x
      subst-sem′ : ∀ {s} → enter (next L p a) (step S a) ≡ s
                 → Sem (enter (next L p a) (step S a)) w → Sem s w
      subst-sem′ refl x = x

  accepts-concatenation′ : ∀ w
    → T (Automaton.accepts C w) ⇔ (∃₂ λ u v → w ≡ u ++ v × u ∈ L × v ∈ M)
  accepts-concatenation′ w =
    let acc = accepts-from 0 (proj₂ (enter 0 [])) (inv-enter 0 []) w in
    mk⇔ (λ t → to (Equivalence.to acc t)) (λ x → Equivalence.from acc (inj₁ x))
    where
    to : Sem (enter 0 []) w → ∃₂ λ u v → w ≡ u ++ v × u ∈ L × v ∈ M
    to (inj₁ x) = x
    to (inj₂ x) with any-enter⁻ 0 [] x
    ... | inj₁ (fin , w∈) = [] , w , refl , fin , w∈
    ... | inj₂ ()

accepts-concatenation : ∀ L M → WellFormed L → WellFormed M → ∀ w
  → T (Automaton.accepts (concatenation (automaton L) M) w)
    ⇔ (∃₂ λ u v → w ≡ u ++ v × u ∈ L × v ∈ M)
accepts-concatenation L M _ _ = accepts-concatenation′ L M

------------------------------------------------------------------------
-- Lawfulness: `Good` states are a state of `L` and a set of states of
-- `M`, strictly increasing

module _ (L M : DFA) (wfL : WellFormed L) (wfM : WellFormed M) where

  private
    C : Automaton
    C = concatenation (automaton L) M

    open Concatenation (automaton L) M using (enter)

    Good : ℕ × List ℕ → Set
    Good s = proj₁ s < size L × Increasing (proj₂ s) × All (_< size M) (proj₂ s)

    0<M : 0 < size M
    0<M = proj₁ wfM

    good-enter : ∀ {p S} → p < size L → Increasing S → All (_< size M) S
               → Good (enter p S)
    good-enter {p} {S} p< inc S< with isFinal L p
    ... | true  = p< , insert-increasing 0 S inc , insert-all 0 S 0<M S<
    ... | false = p< , inc , S<

    good-δ : ∀ {s} a → Good s → Good (Automaton.δ C s a)
    good-δ {p , S} a (p< , inc , S<) =
      good-enter (next-< L wfL p< a)
        (fromList-increasing (map (λ q → next M q a) S))
        (fromList-all (map (λ q → next M q a) S)
          (All.map⁺ (All.map (λ q< → next-< M wfM q< a) S<)))

    ≟⇒≡ : ∀ {s t} → T (Automaton._≟_ C s t) → s ≡ t
    ≟⇒≡ {p , S} {p′ , S′} t =
      cong₂ _,_ (≡ᵇ⇒≡ p p′ (proj₁ (Equivalence.to T-∧ t)))
                (==ⁿ-sound S S′ (proj₂ (Equivalence.to T-∧ t)))

    ≟-refl′ : ∀ s → T (Automaton._≟_ C s s)
    ≟-refl′ (p , S) = Equivalence.from T-∧ (≡ᵇ-refl p , ==ⁿ-refl S)

    enum : List (ℕ × List ℕ)
    enum = pairs (range 0 (size L)) (subsets (range 0 (size M)))

    length-enum : Data.List.Base.length enum ≡ size L Data.Nat.Base.* 2 Data.Nat.Base.^ size M
    length-enum =
      trans (length-pairs (range 0 (size L)) (subsets (range 0 (size M))))
            (cong₂ Data.Nat.Base._*_ (length-range 0 (size L))
              (trans (length-subsets (range 0 (size M)))
                     (cong (2 Data.Nat.Base.^_) (length-range 0 (size M)))))

    cover : ∀ {s} → Good s → s ∈ˡ enum
    cover {p , S} (p< , inc , S<) =
      Any.map (λ { {x , y} (p≡x , S≡y) → cong₂ _,_ p≡x S≡y })
        (any-pairs (∈-range 0 (size L) z≤n p<)
                   (∈-subsets 0 (size M) inc (All.map (λ _ → z≤n) S<) S<))

  lawful-concatenation′ : Lawful C
  lawful-concatenation′ =
    lawful-exact C ≟⇒≡ ≟-refl′ Good
      (good-enter (proj₁ wfL) [] []) good-δ
      enum (≤-reflexive length-enum) cover

lawful-concatenation : ∀ L M → WellFormed L → WellFormed M
                     → Lawful (concatenation (automaton L) M)
lawful-concatenation = lawful-concatenation′
