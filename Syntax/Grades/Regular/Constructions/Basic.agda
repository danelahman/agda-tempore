-------------------------------------------------------------------------
-- Tables, single words, every word, and products: lawful automata and --
-- their languages.                                                    --
-------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _*_; _∸_; _≡ᵇ_; _≤_; _<_; z≤n; s≤s)

module Syntax.Grades.Regular.Constructions.Basic (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Bool.Properties using (T-∧)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using (toℕ-injective)
import Data.Fin.Base
open import Data.List.Base using (List; []; _∷_; map; length; drop)
open import Data.List.Properties using (length-map; length-drop; ∷-injective)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Properties
  using (≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤-reflexive; ≤-antisym; *-mono-≤; ≤-trans; ∸-cancelˡ-≡)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Operations k
  using (word; everything; product; module Single)
open import Syntax.Grades.Regular.Constructions.Base k

------------------------------------------------------------------------
-- Tables

lawful-table : ∀ D → WellFormed D → Lawful (automaton D)
lawful-table D wf =
  lawful-exact (automaton D) (λ {p} {q} t → ≡ᵇ⇒≡ p q t) ≡ᵇ-refl
    (_< size D) (proj₁ wf) (λ a g → next-< D wf g a)
    (range 0 (size D)) (≤-reflexive (length-range 0 (size D)))
    (λ g → ∈-range 0 (size D) z≤n g)

accepts-table : ∀ D w → Automaton.accepts (automaton D) w ≡ accepts D w
accepts-table D w = cong (isFinal D) (δ*-table D 0 w)

------------------------------------------------------------------------
-- A single word

module _ (w : Word) where

  open Single w using (step; accepting; same)
  open Automaton (word w) using (δ*)

  private
    same⇒≡ : ∀ {p q} → T (same p q) → p ≡ q
    same⇒≡ {nothing} {nothing} _ = refl
    same⇒≡ {just i}  {just j}  t = cong just (≡ᵇ⇒≡ i j t)

    same-refl : ∀ p → T (same p p)
    same-refl nothing  = tt
    same-refl (just i) = ≡ᵇ-refl i

    WGood : Maybe ℕ → Set
    WGood nothing  = ⊤
    WGood (just i) = i ≤ length w

    ‼-< : ∀ (v : Word) {i b} → v ‼ i ≡ just b → i < length v
    ‼-< (c ∷ v) {zero}  _ = s≤s z≤n
    ‼-< (c ∷ v) {suc i} e = s≤s (‼-< v e)

    ‼-≥ : ∀ (v : Word) {i} → v ‼ i ≡ nothing → length v ≤ i
    ‼-≥ []      {i}     _  = z≤n
    ‼-≥ (c ∷ v) {suc i} e  = s≤s (‼-≥ v e)

    good-step : ∀ {p} a → WGood p → WGood (step p a)
    good-step {nothing} a _ = tt
    good-step {just i}  a g with w ‼ i in e
    ... | nothing = tt
    ... | just b with a ≟ᴸ b
    ...   | true  = ‼-< w e
    ...   | false = tt

    enum : List (Maybe ℕ)
    enum = nothing ∷ map just (range 0 (suc (length w)))

    length-enum : length enum ≡ suc (suc (length w))
    length-enum =
      cong suc (trans (length-map just (range 0 (suc (length w))))
                      (length-range 0 (suc (length w))))

    cover : ∀ {p} → WGood p → Data.List.Membership.Propositional._∈_ p enum
    cover {nothing} _ = here refl
    cover {just i}  g = there (∈-map⁺ just (∈-range 0 (suc (length w)) z≤n (s≤s g)))

  lawful-word : Lawful (word w)
  lawful-word =
    lawful-exact (word w) same⇒≡ same-refl WGood z≤n good-step
      enum (≤-reflexive length-enum) cover

  private
    δ*-nothing : ∀ v → δ* nothing v ≡ nothing
    δ*-nothing []      = refl
    δ*-nothing (a ∷ v) = δ*-nothing v

    drop-‼ : ∀ (v : Word) {i b} → v ‼ i ≡ just b → drop i v ≡ b ∷ drop (suc i) v
    drop-‼ (c ∷ v) {zero}  refl = refl
    drop-‼ (c ∷ v) {suc i} e    = drop-‼ v e

    drop-≥ : ∀ (v : Word) {i} → length v ≤ i → drop i v ≡ []
    drop-≥ []      {zero}  _        = refl
    drop-≥ []      {suc i} _        = refl
    drop-≥ (c ∷ v) {suc i} (s≤s le) = drop-≥ v le

    drop-[] : ∀ (v : Word) i → drop i v ≡ [] → length v ≤ i
    drop-[] []      i       _  = z≤n
    drop-[] (c ∷ v) (suc i) e  = s≤s (drop-[] v i e)

    ≟ᴸ-true : ∀ {a b} → (a ≟ᴸ b) ≡ true → a ≡ b
    ≟ᴸ-true e = toℕ-injective (≡ᵇ-true e)

    ≟ᴸ-false : ∀ {a b} → (a ≟ᴸ b) ≡ false → a ≢ b
    ≟ᴸ-false {a} e refl = T-false e (≡ᵇ-refl (Data.Fin.Base.toℕ a))

    -- state `just i` accepts exactly the rest of `w`

    accepts-just : ∀ i v → i ≤ length w
                 → T (accepting (δ* (just i) v)) ⇔ v ≡ drop i w
    accepts-just i [] i≤ = mk⇔
      (λ t → sym (drop-≥ w (≤-reflexive (sym (≡ᵇ⇒≡ i (length w) t)))))
      (λ e → ≡⇒≡ᵇ i (length w) (≤-antisym i≤ (drop-[] w i (sym e))))
    accepts-just i (a ∷ v) i≤ with w ‼ i in e
    ... | nothing rewrite δ*-nothing v | drop-≥ w (‼-≥ w e) = mk⇔ (λ ()) (λ ())
    ... | just b with a ≟ᴸ b in e′
    ...   | true rewrite drop-‼ w e =
      let ih = accepts-just (suc i) v (‼-< w e) in
      mk⇔ (λ t → cong₂ _∷_ (≟ᴸ-true e′) (Equivalence.to ih t))
          (λ eq → Equivalence.from ih (proj₂ (∷-injective eq)))
    ...   | false rewrite δ*-nothing v | drop-‼ w e =
      mk⇔ (λ ()) (λ eq → ≟ᴸ-false e′ (proj₁ (∷-injective eq)))

  accepts-word : ∀ v → T (Automaton.accepts (word w) v) ⇔ v ≡ w
  accepts-word v = accepts-just 0 v z≤n

  private
    nothing-rejects : ∀ v → accepting (δ* nothing v) ≡ false
    nothing-rejects v rewrite δ*-nothing v = refl

    accepts-rest : ∀ i → i ≤ length w → T (accepting (δ* (just i) (drop i w)))
    accepts-rest i i≤ = Equivalence.from (accepts-just i (drop i w) i≤) refl

    true≢false : ∀ {b} → T b → b ≡ false → ⊥
    true≢false t e = T-false e t

  reduced-word : Reduced (word w) lawful-word
  reduced-word {nothing} {nothing} _  _  _   = tt
  reduced-word {just i}  {nothing} gi _  res =
    true≢false (accepts-rest i gi) (trans (res (drop i w)) (nothing-rejects (drop i w)))
  reduced-word {nothing} {just j}  _  gj res =
    true≢false (accepts-rest j gj) (trans (sym (res (drop j w))) (nothing-rejects (drop j w)))
  reduced-word {just i}  {just j}  gi gj res =
    ≡⇒≡ᵇ i j (∸-cancelˡ-≡ gi gj
      (trans (sym (length-drop i w)) (trans (cong length drops) (length-drop j w))))
    where
    -- `drop i w` is accepted from `just j`, so it is `drop j w`
    drops : drop i w ≡ drop j w
    drops = Equivalence.to (accepts-just j (drop i w) gj)
              (subst T (res (drop i w)) (accepts-rest i gi))

------------------------------------------------------------------------
-- Every word

lawful-everything : Lawful everything
lawful-everything =
  lawful-exact everything (λ _ → refl) (λ _ → tt) (λ _ → ⊤) tt (λ _ _ → tt)
    (tt ∷ []) (s≤s z≤n) (λ _ → here refl)

reduced-everything : Reduced everything lawful-everything
reduced-everything _ _ _ = tt

accepts-everything : ∀ v → Automaton.accepts everything v ≡ true
accepts-everything v = refl

------------------------------------------------------------------------
-- Products

module _ (f : Bool → Bool → Bool) (A B : Automaton) (LA : Lawful A) (LB : Lawful B) where

  private
    module A  = Automaton A
    module B  = Automaton B
    module LA = Lawful LA
    module LB = Lawful LB
    open Automaton (product f A B) using (_≟_)

    ∧-intro : ∀ {x y} → T x → T y → T (x ∧ y)
    ∧-intro tx ty = Equivalence.from T-∧ (tx , ty)

    ∧-l : ∀ {x y} → T (x ∧ y) → T x
    ∧-l t = proj₁ (Equivalence.to T-∧ t)

    ∧-r : ∀ {x y} → T (x ∧ y) → T y
    ∧-r t = proj₂ (Equivalence.to T-∧ t)

  lawful-product : Lawful (product f A B)
  lawful-product = record
    { Good       = λ s → LA.Good (proj₁ s) × LB.Good (proj₂ s)
    ; good-start = LA.good-start , LB.good-start
    ; good-δ     = λ a g → LA.good-δ a (proj₁ g) , LB.good-δ a (proj₂ g)
    ; ≟-refl     = λ s → ∧-intro (LA.≟-refl (proj₁ s)) (LB.≟-refl (proj₂ s))
    ; ≟-sym      = λ t → ∧-intro (LA.≟-sym (∧-l t)) (LB.≟-sym (∧-r t))
    ; ≟-trans    = λ t u → ∧-intro (LA.≟-trans (∧-l t) (∧-l u))
                                   (LB.≟-trans (∧-r t) (∧-r u))
    ; ≟-final    = λ g h t → cong₂ f (LA.≟-final (proj₁ g) (proj₁ h) (∧-l t))
                                     (LB.≟-final (proj₂ g) (proj₂ h) (∧-r t))
    ; ≟-δ        = λ g h t a → ∧-intro (LA.≟-δ (proj₁ g) (proj₁ h) (∧-l t) a)
                                       (LB.≟-δ (proj₂ g) (proj₂ h) (∧-r t) a)
    ; enum       = pairs LA.enum LB.enum
    ; enum-bound = ≤-trans (≤-reflexive (length-pairs LA.enum LB.enum))
                           (*-mono-≤ LA.enum-bound LB.enum-bound)
    ; enum-cover = λ g → Any.map (λ { {x , y} (tx , ty) → ∧-intro tx ty })
                                 (any-pairs (LA.enum-cover (proj₁ g))
                                            (LB.enum-cover (proj₂ g)))
    }
