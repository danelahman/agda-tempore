------------------------------------------------------------------------
-- The decision procedures are correct.                               --
--                                                                    --
-- `counterexample L M` returns a word exactly when `L ⊈ M`, and the  --
-- word it returns is in `L` and not in `M`; so `_⊆ᵇ_` decides        --
-- inclusion. Non-emptiness, well-formedness and equality of tables   --
-- are decided alongside.                                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _*_; _≡ᵇ_; z≤n; s≤s)

module Syntax.Grades.Regular.Decide (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; not; _∧_; if_then_else_)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base
  using (List; []; _∷_; _++_; _∷ʳ_; length; map; reverse; replicate; upTo; cartesianProduct)
open import Data.List.Properties
  using (length-++; length-map; length-upTo; length-replicate; unfold-reverse; ++-assoc; ++-identityʳ; ≡-dec)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-upTo⁺; ∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.Maybe.Base using (Maybe; just; nothing; is-nothing)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤-refl; ≤-reflexive; +-comm; _<?_)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_; map′)

open import Syntax.Grades.Regular.Automaton k renaming (_∈_ to _∈ᴸ_)
open import Syntax.Grades.Regular.Explore k
open import Syntax.Grades.Regular.Basics k
open import Syntax.Grades.Regular.Inclusion k

------------------------------------------------------------------------
-- The product carrying words is lawful

length-cartesianProduct : ∀ {A B : Set} (xs : List A) (ys : List B)
                        → length (cartesianProduct xs ys) ≡ length xs * length ys
length-cartesianProduct []       ys = refl
length-cartesianProduct (x ∷ xs) ys =
  trans (length-++ (map (x ,_) ys))
        (cong₂ _+_ (length-map (x ,_) ys) (length-cartesianProduct xs ys))

module Witnesses (L M : DFA) (wfL : WellFormed L) (wfM : WellFormed M) where

  private
    W = witnesses L M
    module W = Automaton W

  -- a pair is the pair of states the (reversed) word leads to

  data WGood : (ℕ × ℕ) × Word → Set where
    reached : ∀ vʳ → WGood ((run L 0 (reverse vʳ) , run M 0 (reverse vʳ)) , vʳ)

  private
    pair-≡ : ∀ x y → T (W._≟_ x y) → proj₁ x ≡ proj₁ y
    pair-≡ ((p , q) , v) ((p′ , q′) , v′) t with T-∧⁻ {p ≡ᵇ p′} t
    ... | tp , tq = cong₂ _,_ (≡ᵇ⇒≡ p p′ tp) (≡ᵇ⇒≡ q q′ tq)

    ≡-pair : ∀ x y → proj₁ x ≡ proj₁ y → T (W._≟_ x y)
    ≡-pair ((p , q) , v) ((.p , .q) , v′) refl = T-∧⁺ (≡⇒≡ᵇ p p refl) (≡⇒≡ᵇ q q refl)

    bad-≡ : ∀ x y → proj₁ x ≡ proj₁ y → bad L M x ≡ bad L M y
    bad-≡ ((p , q) , v) ((.p , .q) , v′) refl = refl

    δ-≡ : ∀ x y a → proj₁ x ≡ proj₁ y → proj₁ (W.δ x a) ≡ proj₁ (W.δ y a)
    δ-≡ ((p , q) , v) ((.p , .q) , v′) a refl = refl

    run-snoc : ∀ D vʳ a → run D 0 (reverse (a ∷ vʳ)) ≡ next D (run D 0 (reverse vʳ)) a
    run-snoc D vʳ a = trans (cong (run D 0) (unfold-reverse a vʳ)) (run-++ D 0 (reverse vʳ) (a ∷ []))

    pairs : List (ℕ × ℕ)
    pairs = cartesianProduct (upTo (size L)) (upTo (size M))

    enum-w : List ((ℕ × ℕ) × Word)
    enum-w = map (_, []) pairs

    cover : ∀ {x} → WGood x → Any (λ y → T (W._≟_ x y)) enum-w
    cover (reached vʳ) =
      Any.map⁺ (Any.map (λ { refl → ≡-pair ((run L 0 (reverse vʳ) , run M 0 (reverse vʳ)) , vʳ)
                                           ((run L 0 (reverse vʳ) , run M 0 (reverse vʳ)) , []) refl })
        (∈-cartesianProductWith⁺ _,_
          (∈-upTo⁺ (run-< L wfL (reverse vʳ) (start-< L wfL)))
          (∈-upTo⁺ (run-< M wfM (reverse vʳ) (start-< M wfM)))))

  witnesses-lawful : Lawful W
  witnesses-lawful = record
    { Good       = WGood
    ; good-start = reached []
    ; good-δ     = λ { a (reached vʳ) →
                       subst (λ pq → WGood (pq , a ∷ vʳ))
                             (cong₂ _,_ (run-snoc L vʳ a) (run-snoc M vʳ a))
                             (reached (a ∷ vʳ)) }
    ; ≟-refl     = λ x → ≡-pair x x refl
    ; ≟-sym      = λ {x} {y} t → ≡-pair y x (sym (pair-≡ x y t))
    ; ≟-trans    = λ {x} {y} {z} t t′ → ≡-pair x z (trans (pair-≡ x y t) (pair-≡ y z t′))
    ; ≟-final    = λ {x} {y} _ _ t → bad-≡ x y (pair-≡ x y t)
    ; ≟-δ        = λ {x} {y} _ _ t a → ≡-pair (W.δ x a) (W.δ y a) (δ-≡ x y a (pair-≡ x y t))
    ; enum       = enum-w
    ; enum-bound = ≤-reflexive (trans (length-map _ pairs)
                     (trans (length-cartesianProduct (upTo (size L)) (upTo (size M)))
                            (cong₂ _*_ (length-upTo (size L)) (length-upTo (size M)))))
    ; enum-cover = cover
    }

  -- a discovered pair holding the empty word of `L & ~M` gives a
  -- counterexample

  good-bad : ∀ {x} → WGood x → T (bad L M x)
           → reverse (proj₂ x) ∈ᴸ L × ¬ (reverse (proj₂ x) ∈ᴸ M)
  good-bad (reached vʳ) t with T-∧⁻ t
  ... | tL , tM = tL , T-not⁻ tM

  δ*-witnesses : ∀ w → W.δ* W.start w ≡ ((run L 0 w , run M 0 w) , reverse w)
  δ*-witnesses w = trans (go w (0 , 0) []) (cong ((run L 0 w , run M 0 w) ,_) (++-identityʳ (reverse w)))
    where
    go : ∀ w (x : ℕ × ℕ) vʳ
       → W.δ* (x , vʳ) w ≡ ((run L (proj₁ x) w , run M (proj₂ x) w) , reverse w ++ vʳ)
    go []      x vʳ = refl
    go (a ∷ w) (p , q) vʳ =
      trans (go w (next L p a , next M q a) (a ∷ vʳ))
            (cong ((run L (next L p a) w , run M (next M q a) w) ,_)
                  (sym (trans (cong (_++ vʳ) (unfold-reverse a w))
                              (++-assoc (reverse w) (a ∷ []) vʳ))))

------------------------------------------------------------------------
-- Searching the discovered pairs

search-sound : ∀ L M xs {w} → search L M xs ≡ just w
             → ∃ λ x → x ∈ xs × T (bad L M x) × w ≡ reverse (proj₂ x)
search-sound L M []              ()
search-sound L M ((x , vʳ) ∷ xs) eq with bad L M (x , vʳ) in b
... | true  with eq
...   | refl = (x , vʳ) , here refl , T-true b , refl
search-sound L M ((x , vʳ) ∷ xs) eq | false with search-sound L M xs eq
... | y , y∈ , t , e = y , there y∈ , t , e

search-complete : ∀ L M xs → Any (λ x → T (bad L M x)) xs → ∃ λ w → search L M xs ≡ just w
search-complete L M ((x , vʳ) ∷ xs) (here t) = reverse vʳ , T-if (bad L M (x , vʳ)) t
search-complete L M ((x , vʳ) ∷ xs) (there h) with bad L M (x , vʳ)
... | true  = reverse vʳ , refl
... | false = search-complete L M xs h

------------------------------------------------------------------------
-- Inclusion

module _ {L M : DFA} (wfL : WellFormed L) (wfM : WellFormed M) where

  open Witnesses L M wfL wfM

  private
    W = witnesses L M
    D = proj₁ (Explore.discover W)

  counterexample-sound : ∀ {w} → counterexample L M ≡ just w → w ∈ᴸ L × ¬ (w ∈ᴸ M)
  counterexample-sound eq with search-sound L M D eq
  ... | x , x∈ , t , refl = good-bad (All.lookup (discover-good W witnesses-lawful) x∈) t

  counterexample-complete : ∀ {w} → w ∈ᴸ L → ¬ (w ∈ᴸ M) → ∃ λ v → counterexample L M ≡ just v
  counterexample-complete {w} w∈L w∉M =
    search-complete L M D
      (Any.map (λ {x} t → bad-≟ x t) (discover-cover W witnesses-lawful w))
    where
    bad-start : T (bad L M ((run L 0 w , run M 0 w) , reverse w))
    bad-start = T-∧⁺ w∈L (T-not⁺ w∉M)

    bad-≟ : ∀ x → T (Automaton._≟_ W (Automaton.δ* W (Automaton.start W) w) x) → T (bad L M x)
    bad-≟ ((p , q) , v) t rewrite δ*-witnesses w with T-∧⁻ {run L 0 w ≡ᵇ p} t
    ... | tp , tq = subst₂ (λ p q → T (bad L M ((p , q) , v))) (≡ᵇ⇒≡ _ _ tp) (≡ᵇ⇒≡ _ _ tq) bad-start

  ⊆ᵇ-sound : T (L ⊆ᵇ M) → L ⊆ M
  ⊆ᵇ-sound t w w∈L with accepts M w in e
  ... | true  = tt
  ... | false with counterexample-complete {w} w∈L (λ w∈M → subst T e w∈M)
  ...   | v , eq rewrite eq = ⊥-elim t

  ⊆ᵇ-complete : L ⊆ M → T (L ⊆ᵇ M)
  ⊆ᵇ-complete sub with counterexample L M in eq
  ... | nothing = tt
  ... | just w with counterexample-sound eq
  ...   | w∈L , w∉M = w∉M (sub w w∈L)

  _⊆?_ : Dec (L ⊆ M)
  _⊆?_ with L ⊆ᵇ M in eq
  ... | true  = yes (⊆ᵇ-sound (subst T (sym eq) tt))
  ... | false = no λ sub → subst T eq (⊆ᵇ-complete sub)

------------------------------------------------------------------------
-- Non-emptiness

∅ᴰ : DFA
∅ᴰ = dfa (replicate k 0 ∷ []) (false ∷ [])

∅ᴰ-wf : WellFormed ∅ᴰ
∅ᴰ-wf = s≤s z≤n , refl , (length-replicate k , all-zero k) ∷ []
  where
  all-zero : ∀ n → All (_< 1) (replicate n 0)
  all-zero zero    = []
  all-zero (suc n) = s≤s z≤n ∷ all-zero n

∉∅ᴰ : ∀ w → ¬ (w ∈ᴸ ∅ᴰ)
∉∅ᴰ w = subst (λ p → ¬ T (isFinal ∅ᴰ p)) (sym (stays w)) λ ()
  where
  zero-at : ∀ n i → replicate n 0 ! i ≡ 0
  zero-at zero    i       = refl
  zero-at (suc n) zero    = refl
  zero-at (suc n) (suc i) = zero-at n i

  stays : ∀ w → run ∅ᴰ 0 w ≡ 0
  stays []      = refl
  stays (a ∷ w) rewrite zero-at k (toℕ a) = stays w

nonempty? : (D : DFA) → WellFormed D → Dec (∃ λ w → w ∈ᴸ D)
nonempty? D wf with counterexample D ∅ᴰ in eq
... | just w  = yes (w , proj₁ (counterexample-sound wf ∅ᴰ-wf eq))
... | nothing = no λ (w , w∈D) →
  case (counterexample-complete wf ∅ᴰ-wf {w} w∈D (∉∅ᴰ w)) of λ { (v , eq′) → just≢nothing (trans (sym eq′) eq) }
  where
  open import Function.Base using (case_of_)
  just≢nothing : ∀ {v : Word} → just v ≢ nothing
  just≢nothing ()

------------------------------------------------------------------------
-- Well-formedness and equality of tables

wellFormed? : (D : DFA) → Dec (WellFormed D)
wellFormed? D =
  (0 <? size D) ×-dec (length (finals D) ℕ.≟ size D)
  ×-dec All.all? (λ r → (length r ℕ.≟ k) ×-dec All.all? (_<? size D) r) (rows D)

_≟ᴰ_ : DecidableEquality DFA
dfa rs fs ≟ᴰ dfa rs′ fs′ =
  map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl })
       (≡-dec (≡-dec ℕ._≟_) rs rs′ ×-dec ≡-dec Bool._≟_ fs fs′)
