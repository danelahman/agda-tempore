------------------------------------------------------------------------
-- Breadth-first exploration is correct.                               --
--                                                                     --
-- For a lawful automaton, `explore` returns a well-formed table with  --
-- the automaton's language: the discovered states are pairwise        --
-- `≟`-distinct, so there are at most `bound` of them and the fuel     --
-- suffices, and row `j` sends each letter to a state `≟`-equal to the --
-- successor of the `j`-th discovered state.                           --
--                                                                     --
-- Exploration decides only through `≟`, `δ` and `final`, so two       --
-- automata related by a relation respecting all three explore to the  --
-- same table (`explore-≡`).                                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; _+_; z≤n; s≤s)

module Syntax.Grades.Regular.Explore (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Base as Fin
open import Data.List.Base using (List; []; _∷_; _++_; length; map; tabulate; allFin)
open import Data.List.Properties using (length-++; length-map; length-tabulate; ++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.List.Relation.Binary.Pointwise.Properties using (Pointwise-length)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
import Data.Maybe.Relation.Binary.Pointwise as Maybeʳ
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-antisym; +-suc; +-identityʳ; m≤m+n; m≤n+m; <-≤-trans)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality

open import Syntax.Grades.Regular.Automaton k

------------------------------------------------------------------------
-- Lists by position

module _ {A : Set} where

  ‼-++ : (xs ys : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → (xs ++ ys) ‼ i ≡ just x
  ‼-++ []       ys {i}     ()
  ‼-++ (x ∷ xs) ys {zero}  refl = refl
  ‼-++ (x ∷ xs) ys {suc i} eq   = ‼-++ xs ys eq

  ‼-at : (xs : List A) {y : A} {ys : List A} → (xs ++ y ∷ ys) ‼ length xs ≡ just y
  ‼-at []       = refl
  ‼-at (x ∷ xs) = ‼-at xs

  ‼-< : (xs : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → i < length xs
  ‼-< []       {i}     ()
  ‼-< (x ∷ xs) {zero}  refl = s≤s z≤n
  ‼-< (x ∷ xs) {suc i} eq   = s≤s (‼-< xs eq)

  ‼-≥ : (xs : List A) {i : ℕ} → length xs ≤ i → xs ‼ i ≡ nothing
  ‼-≥ []       _         = refl
  ‼-≥ (x ∷ xs) (s≤s le) = ‼-≥ xs le

  ‼-nothing : (xs : List A) {i : ℕ} → xs ‼ i ≡ nothing → length xs ≤ i
  ‼-nothing []       _         = z≤n
  ‼-nothing (x ∷ xs) {zero}  ()
  ‼-nothing (x ∷ xs) {suc i} eq = s≤s (‼-nothing xs eq)

  ‼-exists : (xs : List A) {i : ℕ} → i < length xs → ∃ λ x → xs ‼ i ≡ just x
  ‼-exists (x ∷ xs) {zero}  _         = x , refl
  ‼-exists (x ∷ xs) {suc i} (s≤s lt) = ‼-exists xs lt

  ‼-snoc : (xs : List A) {y : A} {i : ℕ} {x : A}
         → (xs ++ y ∷ []) ‼ i ≡ just x → xs ‼ i ≡ just x ⊎ (i ≡ length xs × x ≡ y)
  ‼-snoc []       {i = zero}  refl = inj₂ (refl , refl)
  ‼-snoc []       {i = suc i} ()
  ‼-snoc (x ∷ xs) {i = zero}  refl = inj₁ refl
  ‼-snoc (x ∷ xs) {i = suc i} eq with ‼-snoc xs eq
  ... | inj₁ eq′         = inj₁ eq′
  ... | inj₂ (refl , e) = inj₂ (refl , e)

  ‼-All : {P : A → Set} {xs : List A} {i : ℕ} {x : A} → All P xs → xs ‼ i ≡ just x → P x
  ‼-All {xs = x ∷ xs} {zero}  (px ∷ _)   refl = px
  ‼-All {xs = x ∷ xs} {suc i} (_  ∷ pxs) eq   = ‼-All pxs eq

  All-‼ : {P : A → Set} (xs : List A) → (∀ {i x} → xs ‼ i ≡ just x → P x) → All P xs
  All-‼ []       h = []
  All-‼ (x ∷ xs) h = h {zero} refl ∷ All-‼ xs (λ {i} → h {suc i})

  ‼-Any : {P : A → Set} (xs : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → P x → Any P xs
  ‼-Any (x ∷ xs) {zero}  refl px = here px
  ‼-Any (x ∷ xs) {suc i} eq   px = there (‼-Any xs eq px)

  lookupOr-‼ : {d : A} (xs : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → lookupOr d xs i ≡ x
  lookupOr-‼ (x ∷ xs) {zero}  refl = refl
  lookupOr-‼ (x ∷ xs) {suc i} eq   = lookupOr-‼ xs eq

  ‼-map : {B : Set} (f : A → B) (xs : List A) {i : ℕ} {x : A}
        → xs ‼ i ≡ just x → map f xs ‼ i ≡ just (f x)
  ‼-map f (x ∷ xs) {zero}  refl = refl
  ‼-map f (x ∷ xs) {suc i} eq   = ‼-map f xs eq

  just-injective : {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

-- a row, read at a letter

pointwise-tabulate : ∀ {n} {B : Set} {P : B → ℕ → Set} (f : Fin n → B) {r : List ℕ}
                   → Pointwise P (tabulate f) r → ∀ i → P (f i) (r ! toℕ i)
pointwise-tabulate f (p ∷ ps) Fin.zero    = p
pointwise-tabulate f (p ∷ ps) (Fin.suc i) = pointwise-tabulate (λ j → f (Fin.suc j)) ps i

pointwise-All : ∀ {B C : Set} {P : B → C → Set} {Q : C → Set} {xs ys}
              → (∀ {x y} → P x y → Q y) → Pointwise P xs ys → All Q ys
pointwise-All f []       = []
pointwise-All f (p ∷ ps) = f p ∷ pointwise-All f ps

length-letters : length letters ≡ k
length-letters = length-tabulate (λ a → a)

T-true : ∀ {b} → b ≡ true → T b
T-true refl = tt

T-false : ∀ {b} → b ≡ false → ¬ T b
T-false refl ()

------------------------------------------------------------------------
-- Exploring a lawful automaton

module _ (A : Automaton) (LA : Lawful A) where

  open Automaton A hiding (accepts)
  open Lawful LA
  open Explore A hiding (explore)

  -- `≟` is a congruence for words

  good-δ* : ∀ {p} w → Good p → Good (δ* p w)
  good-δ* []      g = g
  good-δ* (a ∷ w) g = good-δ* w (good-δ a g)

  ≟-δ* : ∀ {p q} → Good p → Good q → T (p ≟ q) → ∀ w → T (δ* p w ≟ δ* q w)
  ≟-δ* gp gq e []      = e
  ≟-δ* gp gq e (a ∷ w) = ≟-δ* (good-δ a gp) (good-δ a gq) (≟-δ gp gq e a) w

  ≟-residual : ∀ {p q} → Good p → Good q → T (p ≟ q)
             → ∀ w → final (δ* p w) ≡ final (δ* q w)
  ≟-residual gp gq e w = ≟-final (good-δ* w gp) (good-δ* w gq) (≟-δ* gp gq e w)

  --------------------------------------------------------------------
  -- Pairwise distinct states are at most `bound`

  Distinct : List State → Set
  Distinct = AllPairs (λ p q → ¬ T (p ≟ q))

  private
    remove : {P : State → Set} (ys : List State) → Any P ys → List State
    remove (y ∷ ys) (here _)  = ys
    remove (y ∷ ys) (there h) = y ∷ remove ys h

    remove-length : {P : State → Set} (ys : List State) (h : Any P ys)
                  → suc (length (remove ys h)) ≡ length ys
    remove-length (y ∷ ys) (here _)  = refl
    remove-length (y ∷ ys) (there h) = cong suc (remove-length ys h)

    split : {P Q : State → Set} (ys : List State) (h : Any P ys) → Any Q ys
          → (∃ λ y → P y × Q y) ⊎ Any Q (remove ys h)
    split (y ∷ ys) (here p)  (here q)  = inj₁ (y , p , q)
    split (y ∷ ys) (here p)  (there q) = inj₂ q
    split (y ∷ ys) (there h) (here q)  = inj₂ (here q)
    split (y ∷ ys) (there h) (there q) with split ys h q
    ... | inj₁ c  = inj₁ c
    ... | inj₂ q′ = inj₂ (there q′)

  pigeonhole : ∀ {xs} ys → Distinct xs
             → All (λ x → Any (λ y → T (x ≟ y)) ys) xs → length xs ≤ length ys
  pigeonhole         ys []       []       = z≤n
  pigeonhole {x ∷ xs} ys (d ∷ ds) (h ∷ hs) =
    subst (suc (length xs) ≤_) (remove-length ys h)
          (s≤s (pigeonhole (remove ys h) ds (moved d hs)))
    where
    moved : ∀ {zs} → All (λ z → ¬ T (x ≟ z)) zs
          → All (λ z → Any (λ y → T (z ≟ y)) ys) zs
          → All (λ z → Any (λ y → T (z ≟ y)) (remove ys h)) zs
    moved []       []         = []
    moved (n ∷ ns) (h′ ∷ hs′) with split ys h h′
    ... | inj₁ (y , xy , zy) = ⊥-elim (n (≟-trans xy (≟-sym zy)))
    ... | inj₂ h″            = h″ ∷ moved ns hs′

  Inv : List State → Set
  Inv D = Distinct D × All Good D

  bounded : ∀ {D} → Inv D → length D ≤ bound
  bounded (dist , good) =
    ≤-trans (pigeonhole enum dist (All.map enum-cover good)) enum-bound

  --------------------------------------------------------------------
  -- Discovery

  -- `D` extends to `D′`

  Prefix : List State → List State → Set
  Prefix D D′ = ∃ λ e → D ++ e ≡ D′

  prefix-refl : ∀ D → Prefix D D
  prefix-refl D = [] , ++-identityʳ D

  prefix-trans : ∀ {D D′ D″} → Prefix D D′ → Prefix D′ D″ → Prefix D D″
  prefix-trans {D} (e , refl) (e′ , refl) = e ++ e′ , sym (++-assoc D e e′)

  prefix-‼ : ∀ {D D′ i p} → Prefix D D′ → D ‼ i ≡ just p → D′ ‼ i ≡ just p
  prefix-‼ {D} (e , refl) eq = ‼-++ D e eq

  prefix-length : ∀ {D D′} → Prefix D D′ → length D ≤ length D′
  prefix-length {D} (e , refl) = subst (length D ≤_) (sym (length-++ D)) (m≤m+n _ _)

  -- `i` numbers a state `≟`-equal to `q`

  Points : List State → State → ℕ → Set
  Points D q i = ∃ λ p → D ‼ i ≡ just p × T (q ≟ p)

  points-prefix : ∀ {D D′ q i} → Prefix D D′ → Points D q i → Points D′ q i
  points-prefix pre (p , eq , e) = p , prefix-‼ pre eq , e

  index-just : ∀ q D {i} → index q D ≡ just i → Points D q i
  index-just q (p ∷ ps) eq with q ≟ p in e
  index-just q (p ∷ ps) refl | true = p , refl , T-true e
  ... | false with index q ps in e′
  index-just q (p ∷ ps) refl | false | just j with index-just q ps e′
  ... | p′ , eq′ , e″ = p′ , eq′ , e″

  index-nothing : ∀ q D → index q D ≡ nothing → All (λ p → ¬ T (q ≟ p)) D
  index-nothing q []       _  = []
  index-nothing q (p ∷ ps) eq with q ≟ p in e
  ... | false with index q ps in e′
  ... | nothing = T-false e ∷ index-nothing q ps e′

  VisitSpec : List State → State → ℕ × List State → Set
  VisitSpec D q (i , D′) = Inv D′ × Prefix D D′ × Points D′ q i

  visit-spec : ∀ {q D} → Good q → Inv D → VisitSpec D q (visit q D)
  visit-spec {q} {D} gq inv with index q D in e
  ... | just i  = inv , prefix-refl D , index-just q D e
  ... | nothing =
    ( AllPairs.++⁺ (proj₁ inv) ([] ∷ [])
        (All.map (λ n → (λ pq → n (≟-sym pq)) ∷ []) (index-nothing q D e))
    , All.++⁺ (proj₂ inv) (gq ∷ []) )
    , (q ∷ [] , refl)
    , q , ‼-at D , ≟-refl q

  RowSpec : List State → State → List Letter → List ℕ × List State → Set
  RowSpec D q as (r , D′) =
    Inv D′ × Prefix D D′ × Pointwise (λ a i → Points D′ (δ q a) i) as r

  row-spec : ∀ as {q D} → Good q → Inv D → RowSpec D q as (row as q D)
  row-spec []       {q} {D} gq inv = inv , prefix-refl D , []
  row-spec (a ∷ as) {q} {D} gq inv
    with visit (δ q a) D | visit-spec (good-δ a gq) inv
  ... | i , D′ | inv′ , pre′ , pts with row as q D′ | row-spec as gq inv′
  ...   | r , D″ | inv″ , pre″ , pw =
    inv″ , prefix-trans pre′ pre″ , points-prefix pre″ pts ∷ pw

  --------------------------------------------------------------------
  -- The main loop

  -- row `j` belongs to the `j`-th discovered state

  RowOK : List State → State → List ℕ → Set
  RowOK D p r = Pointwise (λ a i → Points D (δ p a) i) letters r

  RowsOK : List State → List (List ℕ) → Set
  RowsOK D rs = ∀ {j r} → rs ‼ j ≡ just r → ∃ λ p → D ‼ j ≡ just p × RowOK D p r

  rowOK-prefix : ∀ {D D′ p r} → Prefix D D′ → RowOK D p r → RowOK D′ p r
  rowOK-prefix pre = Pointwise.map (points-prefix pre)

  record GoInv (i : ℕ) (D : List State) (rs : List (List ℕ)) : Set where
    field
      inv    : Inv D
      len    : length rs ≡ i
      within : i ≤ length D
      rowsOK : RowsOK D rs
      head   : D ‼ 0 ≡ just start

  open GoInv

  step-inv : ∀ {i D rs q r D′} → GoInv i D rs → D ‼ i ≡ just q
           → RowSpec D q letters (r , D′) → GoInv (suc i) D′ (rs ++ r ∷ [])
  step-inv {i} {D} {rs} {q} {r} {D′} g eq (inv′ , pre , pw) = record
    { inv    = inv′
    ; len    = trans (length-++ rs) (trans (+-suc (length rs) 0)
                 (cong suc (trans (+-identityʳ (length rs)) (len g))))
    ; within = <-≤-trans (‼-< D eq) (prefix-length pre)
    ; rowsOK = rows′
    ; head   = prefix-‼ pre (head g)
    }
    where
    rows′ : RowsOK D′ (rs ++ r ∷ [])
    rows′ {j} {r′} eq′ with ‼-snoc rs eq′
    ... | inj₁ old with rowsOK g old
    ...   | p , eqp , ok = p , prefix-‼ pre eqp , rowOK-prefix pre ok
    rows′ {j} {r′} eq′ | inj₂ (refl , refl) =
      q , prefix-‼ pre (subst (λ j → D ‼ j ≡ just q) (sym (len g)) eq) , pw

  -- the loop ends having processed every discovered state

  Done : List State × List (List ℕ) → Set
  Done (D , rs) = Inv D × length rs ≡ length D × RowsOK D rs × D ‼ 0 ≡ just start

  finish : ∀ {i D rs} → GoInv i D rs → length D ≤ i → Done (D , rs)
  finish g le = inv g , trans (len g) (≤-antisym (within g) le) , rowsOK g , head g

  go-spec : ∀ f {i D rs} → GoInv i D rs → bound ≤ i + f → Done (go f i D rs)
  go-spec zero       {i} {D} g b =
    finish g (≤-trans (bounded (inv g)) (subst (bound ≤_) (+-identityʳ i) b))
  go-spec (suc f) {i} {D} {rs} g b with D ‼ i in eq
  ... | nothing = finish g (‼-nothing D eq)
  ... | just q with row letters q D | row-spec letters (‼-All (proj₂ (inv g)) eq) (inv g)
  ...   | r , D′ | spec =
    go-spec f (step-inv g eq spec) (subst (bound ≤_) (+-suc i f) b)

  go-start : GoInv 0 (start ∷ []) []
  go-start = record
    { inv    = ([] ∷ []) , (good-start ∷ [])
    ; len    = refl
    ; within = z≤n
    ; rowsOK = λ ()
    ; head   = refl
    }

  discover-done : Done discover
  discover-done = go-spec bound go-start ≤-refl

  -- the fuel is irrelevant once it suffices

  go-fuel : ∀ f f′ {i D rs} → GoInv i D rs → bound ≤ i + f → bound ≤ i + f′
          → go f i D rs ≡ go f′ i D rs
  go-fuel zero    zero     g b b′ = refl
  go-fuel zero    (suc f′) {i} {D} g b b′ with D ‼ i in eq
  ... | nothing = refl
  ... | just q  = ⊥-elim (just≢nothing (trans (sym eq)
                    (‼-≥ D (≤-trans (bounded (inv g)) (subst (bound ≤_) (+-identityʳ i) b)))))
    where
    just≢nothing : ∀ {x} → just x ≢ nothing
    just≢nothing ()
  go-fuel (suc f) zero g b b′ = sym (go-fuel zero (suc f) g b′ b)
  go-fuel (suc f) (suc f′) {i} {D} {rs} g b b′ with D ‼ i in eq
  ... | nothing = refl
  ... | just q with row letters q D | row-spec letters (‼-All (proj₂ (inv g)) eq) (inv g)
  ...   | r , D′ | spec =
    go-fuel f f′ (step-inv g eq spec)
      (subst (bound ≤_) (+-suc i f) b) (subst (bound ≤_) (+-suc i f′) b′)

  explore-fuel : ∀ f → bound ≤ f → explore A ≡ table (go f 0 (start ∷ []) [])
  explore-fuel f b = cong table (go-fuel bound f go-start ≤-refl b)

  --------------------------------------------------------------------
  -- The table

  module _ {D : List State} {rs : List (List ℕ)} (done : Done (D , rs)) where

    private
      E = table (D , rs)

    -- a table state tracks the discovered state it numbers

    track : ∀ w {j p} → D ‼ j ≡ just p
          → ∃ λ p′ → D ‼ run E j w ≡ just p′ × T (δ* p w ≟ p′)
    track []      {j} {p} eq = p , eq , ≟-refl p
    track (a ∷ w) {j} {p} eq with ‼-exists rs (subst (j <_) (sym (proj₁ (proj₂ done))) (‼-< D eq))
    ... | r , eqr with proj₁ (proj₂ (proj₂ done)) eqr
    ...   | p₀ , eq₀ , ok with just-injective (trans (sym eq₀) eq)
    ...     | refl with pointwise-tabulate (λ a → a) ok a
    ...       | p₁ , eq₁ , e₁ with track w (subst (λ t → D ‼ t ≡ just p₁)
                                      (cong (_! toℕ a) (sym (lookupOr-‼ rs eqr))) eq₁)
    ...         | p′ , eq′ , e′ =
      p′ , eq′ ,
      ≟-trans (≟-δ* (good-δ a gp) gp₁ e₁ w) e′
      where
      gp  = ‼-All (proj₂ (proj₁ done)) eq
      gp₁ = ‼-All (proj₂ (proj₁ done)) eq₁

    table-wf : WellFormed E
    table-wf =
        subst (0 <_) (sym (proj₁ (proj₂ done))) (‼-< D (proj₂ (proj₂ (proj₂ done))))
      , trans (length-map final D) (sym (proj₁ (proj₂ done)))
      , All-‼ rs row-wf
      where
      row-wf : ∀ {j r} → rs ‼ j ≡ just r → length r ≡ k × All (_< length rs) r
      row-wf eqr with proj₁ (proj₂ (proj₂ done)) eqr
      ... | p , _ , ok =
          trans (sym (Pointwise-length ok)) length-letters
        , pointwise-All (λ { (_ , eqi , _) →
            subst (_ <_) (sym (proj₁ (proj₂ done))) (‼-< D eqi) }) ok

    table-accepts : ∀ w → accepts E w ≡ final (δ* start w)
    table-accepts w with track w (proj₂ (proj₂ (proj₂ done)))
    ... | p′ , eq′ , e′ =
      trans (lookupOr-‼ (map final D) (‼-map final D eq′))
            (sym (≟-final (good-δ* w good-start) (‼-All (proj₂ (proj₁ done)) eq′) e′))

    table-cover : ∀ w → Any (λ p → T (δ* start w ≟ p)) D
    table-cover w with track w (proj₂ (proj₂ (proj₂ done)))
    ... | p′ , eq′ , e′ = ‼-Any D eq′ e′

  explore-wf : WellFormed (explore A)
  explore-wf = table-wf {proj₁ discover} {proj₂ discover} discover-done

  explore-accepts : ∀ w → accepts (explore A) w ≡ Automaton.accepts A w
  explore-accepts = table-accepts {proj₁ discover} {proj₂ discover} discover-done

  discover-good : All Good (proj₁ discover)
  discover-good = proj₂ (proj₁ discover-done)

  discover-cover : ∀ w → Any (λ p → T (δ* start w ≟ p)) (proj₁ discover)
  discover-cover = table-cover {proj₁ discover} {proj₂ discover} discover-done

------------------------------------------------------------------------
-- Exploration in lockstep

module Lockstep
  (A B : Automaton)
  (R : Automaton.State A → Automaton.State B → Set)
  (R-δ     : ∀ {p q} a → R p q → R (Automaton.δ A p a) (Automaton.δ B q a))
  (R-final : ∀ {p q} → R p q → Automaton.final A p ≡ Automaton.final B q)
  (R-≟     : ∀ {p q p′ q′} → R p q → R p′ q′
           → Automaton._≟_ A p p′ ≡ Automaton._≟_ B q q′)
  where

  private
    module A = Automaton A
    module B = Automaton B
    module EA = Explore A
    module EB = Explore B

  index-ls : ∀ {q q′ D E} → R q q′ → Pointwise R D E → EA.index q D ≡ EB.index q′ E
  index-ls rq []                     = refl
  index-ls {q} {q′} rq (_∷_ {p} {p′} rp pw) rewrite R-≟ rq rp
    with q′ B.≟ p′
  ... | true  = refl
  ... | false = cong (Maybe.map suc) (index-ls rq pw)

  VisitRel : ℕ × List A.State → ℕ × List B.State → Set
  VisitRel (i , D) (j , E) = i ≡ j × Pointwise R D E

  visit-ls : ∀ {q q′ D E} → R q q′ → Pointwise R D E
           → VisitRel (EA.visit q D) (EB.visit q′ E)
  visit-ls {q} {q′} {D} {E} rq pw
    with EA.index q D | EB.index q′ E | index-ls rq pw
  ... | just i  | .(just i) | refl = refl , pw
  ... | nothing | .nothing  | refl = Pointwise-length pw , Pointwise.++⁺ pw (rq ∷ [])

  RowRel : List ℕ × List A.State → List ℕ × List B.State → Set
  RowRel (r , D) (s , E) = r ≡ s × Pointwise R D E

  row-ls : ∀ as {q q′ D E} → R q q′ → Pointwise R D E
         → RowRel (EA.row as q D) (EB.row as q′ E)
  row-ls []       rq pw = refl , pw
  row-ls (a ∷ as) {q} {q′} {D} {E} rq pw
    with EA.visit (A.δ q a) D | EB.visit (B.δ q′ a) E | visit-ls (R-δ a rq) pw
  ... | i , D′ | j , E′ | refl , pw′
    with EA.row as q D′ | EB.row as q′ E′ | row-ls as rq pw′
  ...   | r , D″ | s , E″ | refl , pw″ = refl , pw″

  ‼-ls : ∀ {D E} i → Pointwise R D E → Maybeʳ.Pointwise R (D ‼ i) (E ‼ i)
  ‼-ls i       []         = Maybeʳ.nothing
  ‼-ls zero    (rp ∷ pw) = Maybeʳ.just rp
  ‼-ls (suc i) (rp ∷ pw) = ‼-ls i pw

  GoRel : List A.State × List (List ℕ) → List B.State × List (List ℕ) → Set
  GoRel (D , rs) (E , ss) = rs ≡ ss × Pointwise R D E

  go-ls : ∀ f i {D E} rs → Pointwise R D E → GoRel (EA.go f i D rs) (EB.go f i E rs)
  go-ls zero    i rs pw = refl , pw
  go-ls (suc f) i {D} {E} rs pw with D ‼ i | E ‼ i | ‼-ls i pw
  ... | nothing | nothing | Maybeʳ.nothing = refl , pw
  ... | just q  | just q′ | Maybeʳ.just rq
    with EA.row letters q D | EB.row letters q′ E | row-ls letters rq pw
  ...   | r , D′ | s , E′ | refl , pw′ = go-ls f (suc i) (rs ++ r ∷ []) pw′

  table-ls : ∀ {x y} → GoRel x y → EA.table x ≡ EB.table y
  table-ls {D , rs} {E , .rs} (refl , pw) = cong (dfa rs) (finals-ls pw)
    where
    finals-ls : ∀ {D E} → Pointwise R D E → map A.final D ≡ map B.final E
    finals-ls []        = refl
    finals-ls (r ∷ pw) = cong₂ _∷_ (R-final r) (finals-ls pw)

  explore-ls : ∀ f → R A.start B.start
             → EA.table (EA.go f 0 (A.start ∷ []) []) ≡ EB.table (EB.go f 0 (B.start ∷ []) [])
  explore-ls f r = table-ls (go-ls f 0 [] (r ∷ []))

-- lawful automata related by a relation respecting `≟`, `δ` and
-- `final`, with related start states, explore to the same table

explore-≡ : (A B : Automaton) → Lawful A → Lawful B
          → (R : Automaton.State A → Automaton.State B → Set)
          → (∀ {p q} a → R p q → R (Automaton.δ A p a) (Automaton.δ B q a))
          → (∀ {p q} → R p q → Automaton.final A p ≡ Automaton.final B q)
          → (∀ {p q p′ q′} → R p q → R p′ q′ → Automaton._≟_ A p p′ ≡ Automaton._≟_ B q q′)
          → R (Automaton.start A) (Automaton.start B)
          → explore A ≡ explore B
explore-≡ A B LA LB R R-δ R-final R-≟ r =
  trans (explore-fuel A LA F (m≤m+n _ _))
        (trans (Lockstep.explore-ls A B R R-δ R-final R-≟ F r)
               (sym (explore-fuel B LB F (m≤n+m _ _))))
  where F = Automaton.bound A + Automaton.bound B
