------------------------------------------------------------------------
-- Canonical tables are canonical.                                     --
--                                                                     --
-- The quotient of a well-formed table is lawful and compares states   --
-- by language, so `canon` preserves the language (`canon-accepts`),   --
-- and two quotients with the same language explore in lockstep        --
-- (`canonicity`). A reduced automaton already explores to its         --
-- canonical table (`explore-canonical`).                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; _≡ᵇ_; z≤n; s≤s)

module Syntax.Grades.Regular.Canonicity (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; map; length; upTo; applyUpTo)
open import Data.List.Properties using (length-map; length-applyUpTo)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤-refl; ≤-reflexive)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality

open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Canonical k
open import Syntax.Grades.Regular.Explore k
open import Syntax.Grades.Regular.Moore k using (moore-sound; moore-complete)

------------------------------------------------------------------------
-- Tables

module _ (D : DFA) (wf : WellFormed D) where

  private
    rows-ok : ∀ {p} → p < size D → ∃ λ r → lookupOr [] (rows D) p ≡ r × length r ≡ k × All (_< size D) r
    rows-ok {p} lt = go (rows D) (proj₂ (proj₂ wf)) lt
      where
      go : ∀ rs → All (λ r → length r ≡ k × All (_< size D) r) rs → ∀ {p} → p < length rs
         → ∃ λ r → lookupOr [] rs p ≡ r × length r ≡ k × All (_< size D) r
      go (r ∷ rs) (ok ∷ oks) {zero}  _         = r , refl , ok
      go (r ∷ rs) (ok ∷ oks) {suc p} (s≤s lt) = go rs oks lt

    entry-< : ∀ {r} → All (_< size D) r → ∀ {i} → i < length r → r ! i < size D
    entry-< (x<n ∷ _)   {zero}  _         = x<n
    entry-< (_   ∷ all) {suc i} (s≤s lt) = entry-< all lt

  next-< : ∀ {p} a → p < size D → next D p a < size D
  next-< a lt with rows-ok lt
  ... | r , eq , len , all rewrite eq =
    entry-< all (subst (toℕ a <_) (sym len) (toℕ<n a))

  run-< : ∀ {p} w → p < size D → run D p w < size D
  run-< []      lt = lt
  run-< (a ∷ w) lt = run-< w (next-< a lt)

  start-< : 0 < size D
  start-< = proj₁ wf

------------------------------------------------------------------------
-- Language equivalence

Equiv-refl : ∀ {D p} → Equiv D p D p
Equiv-refl w = refl

Equiv-sym : ∀ {D p E q} → Equiv D p E q → Equiv E q D p
Equiv-sym e w = sym (e w)

Equiv-trans : ∀ {D p E q F r} → Equiv D p E q → Equiv E q F r → Equiv D p F r
Equiv-trans e e′ w = trans (e w) (e′ w)

Equiv-next : ∀ {D p E q} a → Equiv D p E q → Equiv D (next D p a) E (next E q a)
Equiv-next a e w = e (a ∷ w)

Equiv-final : ∀ {D p E q} → Equiv D p E q → isFinal D p ≡ isFinal E q
Equiv-final e = e []

T-≡ : ∀ {a b : Bool} → (T a → T b) → (T b → T a) → a ≡ b
T-≡ {false} {false} f g = refl
T-≡ {false} {true}  f g with g tt
... | ()
T-≡ {true}  {false} f g with f tt
... | ()
T-≡ {true}  {true}  f g = refl

------------------------------------------------------------------------
-- Positions below a bound

applyUpTo-‼ : ∀ {A : Set} (f : ℕ → A) {n i} → i < n → applyUpTo f n ‼ i ≡ just (f i)
applyUpTo-‼ f {suc n} {zero}  _         = refl
applyUpTo-‼ f {suc n} {suc i} (s≤s lt) = applyUpTo-‼ (λ j → f (suc j)) lt

------------------------------------------------------------------------
-- The quotient, for a correct refinement

module Quotient
  (moore-sound    : ∀ D → WellFormed D → ∀ {p q} → p < size D → q < size D
                  → Moore.equivalence D ! p ≡ Moore.equivalence D ! q → Equiv D p D q)
  (moore-complete : ∀ D → WellFormed D → ∀ {p q} → p < size D → q < size D
                  → Equiv D p D q → Moore.equivalence D ! p ≡ Moore.equivalence D ! q)
  where

  module _ (D : DFA) (wf : WellFormed D) where

    private
      cs = Moore.equivalence D
      Q  = quotient D

    -- a class paired with a state in it

    data QGood : ℕ × ℕ → Set where
      good : ∀ {p} → p < size D → QGood (cs ! p , p)

    δ*-quotient : ∀ p w → Automaton.δ* Q (cs ! p , p) w ≡ (cs ! run D p w , run D p w)
    δ*-quotient p []      = refl
    δ*-quotient p (a ∷ w) = δ*-quotient (next D p a) w

    quotient-accepts : ∀ w → Automaton.accepts Q w ≡ accepts D w
    quotient-accepts w rewrite δ*-quotient 0 w = refl

    private
      same⇒≡ : ∀ {c c′ : ℕ} → T (c ≡ᵇ c′) → c ≡ c′
      same⇒≡ {c} {c′} = ≡ᵇ⇒≡ c c′

      ≡⇒same : ∀ {c c′ : ℕ} → c ≡ c′ → T (c ≡ᵇ c′)
      ≡⇒same {c} {c′} = ≡⇒≡ᵇ c c′

      class-sound : ∀ {c p c′ p′} → QGood (c , p) → QGood (c′ , p′)
                  → T (c ≡ᵇ c′) → Equiv D p D p′
      class-sound (good lt) (good lt′) e = moore-sound D wf lt lt′ (same⇒≡ e)

      class-complete : ∀ {c p c′ p′} → QGood (c , p) → QGood (c′ , p′)
                     → Equiv D p D p′ → T (c ≡ᵇ c′)
      class-complete (good lt) (good lt′) e = ≡⇒same (moore-complete D wf lt lt′ e)

      enum-q : List (ℕ × ℕ)
      enum-q = map (λ p → cs ! p , p) (upTo (size D))

    quotient-lawful : Lawful Q
    quotient-lawful = record
      { Good       = QGood
      ; good-start = good (start-< D wf)
      ; good-δ     = λ { a (good lt) → good (next-< D wf a lt) }
      ; ≟-refl     = λ { (c , _) → ≡⇒same {c} refl }
      ; ≟-sym      = λ { {c , _} {c′ , _} e → ≡⇒same (sym (same⇒≡ {c} e)) }
      ; ≟-trans    = λ { {c , _} {c′ , _} {c″ , _} e e′ →
                         ≡⇒same (trans (same⇒≡ {c} e) (same⇒≡ {c′} e′)) }
      ; ≟-final    = λ g g′ e → Equiv-final {D} {_} {D} (class-sound g g′ e)
      ; ≟-δ        = λ { {_ , p} {_ , p′} g@(good lt) g′@(good lt′) e a →
                         class-complete (good (next-< D wf a lt)) (good (next-< D wf a lt′))
                           (Equiv-next {D} {p} {D} {p′} a (class-sound g g′ e)) }
      ; enum       = enum-q
      ; enum-bound = ≤-reflexive (trans (length-map _ (upTo (size D)))
                                        (length-applyUpTo (λ p → p) (size D)))
      ; enum-cover = λ { {_ , p} (good lt) →
                         ‼-Any enum-q (‼-map (λ p → cs ! p , p) (upTo (size D))
                                              (applyUpTo-‼ (λ p → p) lt))
                               (≡⇒same {cs ! p} refl) }
      }

    canon-wf : WellFormed (canon D)
    canon-wf = explore-wf Q quotient-lawful

    canon-accepts : ∀ w → accepts (canon D) w ≡ accepts D w
    canon-accepts w = trans (explore-accepts Q quotient-lawful w) (quotient-accepts w)

  ----------------------------------------------------------------------
  -- Canonicity

  canonicity : ∀ D E → WellFormed D → WellFormed E
             → (∀ w → accepts D w ≡ accepts E w) → canon D ≡ canon E
  canonicity D E wfD wfE same =
    explore-≡ (quotient D) (quotient E)
      (quotient-lawful D wfD) (quotient-lawful E wfE)
      R R-δ R-final R-≟ (good (start-< D wfD) , good (start-< E wfE) , same)
    where
    csD = Moore.equivalence D
    csE = Moore.equivalence E

    R : ℕ × ℕ → ℕ × ℕ → Set
    R (c , p) (c′ , q) = QGood D wfD (c , p) × QGood E wfE (c′ , q) × Equiv D p E q

    R-δ : ∀ {x y} a → R x y → R (Automaton.δ (quotient D) x a) (Automaton.δ (quotient E) y a)
    R-δ {_ , p} {_ , q} a (good lt , good lt′ , e) =
      good (next-< D wfD a lt) , good (next-< E wfE a lt′) , Equiv-next {D} {p} {E} {q} a e

    R-final : ∀ {x y} → R x y → Automaton.final (quotient D) x ≡ Automaton.final (quotient E) y
    R-final {_ , p} {_ , q} (_ , _ , e) = Equiv-final {D} {p} {E} {q} e

    R-≟ : ∀ {x y x′ y′} → R x y → R x′ y′
        → Automaton._≟_ (quotient D) x x′ ≡ Automaton._≟_ (quotient E) y y′
    R-≟ {_ , p₁} {_ , q₁} {_ , p₂} {_ , q₂} (good lt₁ , good lt₁′ , e₁) (good lt₂ , good lt₂′ , e₂) =
      T-≡ (λ t → ≡⇒≡ᵇ _ _ (moore-complete E wfE lt₁′ lt₂′
                    (Equiv-trans {E} {q₁} {D} {p₁} {E} {q₂} (Equiv-sym {D} {p₁} {E} {q₁} e₁)
                      (Equiv-trans {D} {p₁} {D} {p₂} {E} {q₂}
                        (moore-sound D wfD lt₁ lt₂ (≡ᵇ⇒≡ _ _ t)) e₂))))
          (λ t → ≡⇒≡ᵇ _ _ (moore-complete D wfD lt₁ lt₂
                    (Equiv-trans {D} {p₁} {E} {q₁} {D} {p₂} e₁
                      (Equiv-trans {E} {q₁} {E} {q₂} {D} {p₂}
                        (moore-sound E wfE lt₁′ lt₂′ (≡ᵇ⇒≡ _ _ t))
                        (Equiv-sym {D} {p₂} {E} {q₂} e₂)))))

  canon-idempotent : ∀ D → WellFormed D → canon (canon D) ≡ canon D
  canon-idempotent D wf =
    canonicity (canon D) D (canon-wf D wf) wf (canon-accepts D wf)

  ----------------------------------------------------------------------
  -- Normalising a lawful automaton

  normalise-wf : ∀ A → Lawful A → WellFormed (normalise A)
  normalise-wf A LA = canon-wf (explore A) (explore-wf A LA)

  normalise-accepts : ∀ A → Lawful A → ∀ w → accepts (normalise A) w ≡ Automaton.accepts A w
  normalise-accepts A LA w =
    trans (canon-accepts (explore A) (explore-wf A LA) w) (explore-accepts A LA w)

  ----------------------------------------------------------------------
  -- A reduced automaton explores to its canonical table

  explore-canonical : ∀ A (LA : Lawful A) → Reduced A LA → canon (explore A) ≡ explore A
  explore-canonical A LA red =
    explore-≡ (quotient E) A (quotient-lawful E wfE) LA
      R R-δ R-final R-≟
      (good (start-< E wfE) , Lawful.good-start LA , λ w → explore-accepts A LA w)
    where
    open Automaton A using (State; δ; δ*; final; _≟_; start)
    open Lawful LA using (Good; good-δ; ≟-sym)

    E   = explore A
    wfE = explore-wf A LA

    R : ℕ × ℕ → State → Set
    R (c , p) q = QGood E wfE (c , p) × Good q
                × (∀ w → isFinal E (run E p w) ≡ final (δ* q w))

    R-δ : ∀ {x q} a → R x q → R (Automaton.δ (quotient E) x a) (δ q a)
    R-δ a (good lt , g , e) = good (next-< E wfE a lt) , good-δ a g , λ w → e (a ∷ w)

    R-final : ∀ {x q} → R x q → Automaton.final (quotient E) x ≡ final q
    R-final (_ , _ , e) = e []

    R-≟ : ∀ {x q x′ q′} → R x q → R x′ q′ → Automaton._≟_ (quotient E) x x′ ≡ (q ≟ q′)
    R-≟ (good lt , g , e) (good lt′ , g′ , e′) =
      T-≡ (λ t → red g g′ λ w →
                   trans (sym (e w)) (trans (moore-sound E wfE lt lt′ (≡ᵇ⇒≡ _ _ t) w) (e′ w)))
          (λ t → ≡⇒≡ᵇ _ _ (moore-complete E wfE lt lt′ λ w →
                   trans (e w) (trans (≟-residual A LA g g′ t w) (sym (e′ w)))))

open Quotient moore-sound moore-complete public
