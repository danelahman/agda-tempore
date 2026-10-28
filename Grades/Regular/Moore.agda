-------------------------------------------------------------------------
-- Correctness of Moore's partition refinement.                        --
--                                                                     --
-- Round `i` of `Moore.rounds` holds a leader function of agreement on --
-- words shorter than `i`: each state's class is the least state that  --
-- agrees with it. A round that changes the partition gains a fixed    --
-- point of the leader function, and there are at most `size D` of     --
-- them, so the fuel suffices and `equivalence` is a fixpoint of       --
-- `refine`, which is language equivalence.                            --
-------------------------------------------------------------------------

open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≡ᵇ_)

module Grades.Regular.Moore (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; if_then_else_; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; map; zipWith; replicate; length)
open import Data.List.Properties using (∷-injective; length-map; length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Properties
  using ( suc-injective; ≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤-refl; ≤-trans; ≤-antisym; m≤n⇒m≤1+n
        ; <-irrefl; ≤-<-trans; m≤n⇒m<n∨m≡n; +-suc; m≤m+n; +-monoʳ-≤ )
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import Grades.Regular.Automaton k
open import Grades.Regular.Canonical k
open import Grades.Regular.Basics k

------------------------------------------------------------------------
-- Booleans and lists

-- two lists of equal length that `==ⁿ` tells apart differ at a position

==ⁿ-differ : ∀ xs ys → length xs ≡ length ys → ¬ T (xs ==ⁿ ys)
           → ∃ λ p → p < length xs × xs ! p ≢ ys ! p
==ⁿ-differ []       []       _  h = ⊥-elim (h tt)
==ⁿ-differ (x ∷ xs) (y ∷ ys) eq h with x ≡ᵇ y in e
... | false = 0 , s≤s z≤n , λ x≡y → subst T e (≡⇒≡ᵇ x y x≡y)
... | true  with ==ⁿ-differ xs ys (suc-injective eq) h
...   | p , p< , ne = suc p , s≤s p< , ne

!-replicate : ∀ n p → replicate n 0 ! p ≡ 0
!-replicate zero    p       = refl
!-replicate (suc n) zero    = refl
!-replicate (suc n) (suc p) = !-replicate n p

lookup-map : ∀ {A B : Set} (f : A → B) {d : A} {e : B} xs {p}
           → p < length xs → lookupOr e (map f xs) p ≡ f (lookupOr d xs p)
lookup-map f (x ∷ xs) {zero}  _       = refl
lookup-map f (x ∷ xs) {suc p} (s≤s h) = lookup-map f xs h

lookup-zipWith : ∀ {A B C : Set} (f : A → B → C) {dA dB dC} xs ys {p}
               → p < length xs → p < length ys
               → lookupOr dC (zipWith f xs ys) p
               ≡ f (lookupOr dA xs p) (lookupOr dB ys p)
lookup-zipWith f (x ∷ xs) (y ∷ ys) {zero}  _       _       = refl
lookup-zipWith f (x ∷ xs) (y ∷ ys) {suc p} (s≤s h) (s≤s h') =
  lookup-zipWith f xs ys h h'

length-zipWith : ∀ {A B C : Set} (f : A → B → C) xs ys
               → length xs ≡ length ys → length (zipWith f xs ys) ≡ length xs
length-zipWith f []       []       _  = refl
length-zipWith f (x ∷ xs) (y ∷ ys) eq =
  cong suc (length-zipWith f xs ys (suc-injective eq))

-- lists of length `m` agreeing at every position below `m`

ext : ∀ {m} xs ys → length xs ≡ m → length ys ≡ m
    → (∀ (a : Fin m) → xs ! toℕ a ≡ ys ! toℕ a) → xs ≡ ys
ext []       []       _    _    _ = refl
ext [] (y ∷ ys) refl ()
ext (x ∷ xs) [] refl ()
ext {suc m} (x ∷ xs) (y ∷ ys) lx ly h =
  cong₂ _∷_ (h fzero)
    (ext xs ys (suc-injective lx) (suc-injective ly) (λ a → h (fsuc a)))

------------------------------------------------------------------------
-- Counting the positions below `m` that satisfy a test

count : (ℕ → Bool) → ℕ → ℕ
count P zero    = 0
count P (suc m) = if P m then suc (count P m) else count P m

count-≤ : ∀ P m → count P m ≤ m
count-≤ P zero    = z≤n
count-≤ P (suc m) with P m
... | true  = s≤s (count-≤ P m)
... | false = m≤n⇒m≤1+n (count-≤ P m)

count-mono : ∀ P Q m → (∀ {x} → x < m → T (P x) → T (Q x))
           → count P m ≤ count Q m
count-mono P Q zero    h = z≤n
count-mono P Q (suc m) h with P m in eP | Q m in eQ
... | true  | true  = s≤s (count-mono P Q m (λ x< → h (m≤n⇒m≤1+n x<)))
... | true  | false = ⊥-elim (subst T eQ (h ≤-refl (T-true eP)))
... | false | true  =
  m≤n⇒m≤1+n (count-mono P Q m (λ x< → h (m≤n⇒m≤1+n x<)))
... | false | false = count-mono P Q m (λ x< → h (m≤n⇒m≤1+n x<))

count-strict : ∀ P Q m → (∀ {x} → x < m → T (P x) → T (Q x))
             → ∀ {x} → x < m → T (Q x) → ¬ T (P x) → count P m < count Q m
count-strict P Q (suc m) h {x} (s≤s x≤m) qx ¬px
  with m≤n⇒m<n∨m≡n x≤m
... | inj₂ refl with P x in eP | Q x in eQ
...   | true  | _     = ⊥-elim (¬px tt)
...   | false | false = ⊥-elim qx
...   | false | true  = s≤s (count-mono P Q x (λ y< → h (m≤n⇒m≤1+n y<)))
count-strict P Q (suc m) h {x} (s≤s x≤m) qx ¬px
    | inj₁ x<m with P m in eP | Q m in eQ
...   | true  | true  = s≤s (count-strict P Q m h′ x<m qx ¬px)
  where h′ = λ {y} (y< : y < m) → h (m≤n⇒m≤1+n y<)
...   | true  | false = ⊥-elim (subst T eQ (h ≤-refl (T-true eP)))
...   | false | true  =
  m≤n⇒m≤1+n (count-strict P Q m (λ y< → h (m≤n⇒m≤1+n y<)) x<m qx ¬px)
...   | false | false = count-strict P Q m (λ y< → h (m≤n⇒m≤1+n y<)) x<m qx ¬px

------------------------------------------------------------------------
-- Agreement on words shorter than `i`

module Agreement (D : DFA) where

  _≈[_]_ : ℕ → ℕ → ℕ → Set
  p ≈[ zero  ] q = ⊤
  p ≈[ suc i ] q = isFinal D p ≡ isFinal D q × (∀ a → next D p a ≈[ i ] next D q a)

  ≈-down : ∀ i {p q} → p ≈[ suc i ] q → p ≈[ i ] q
  ≈-down zero    _       = tt
  ≈-down (suc i) (f , g) = f , λ a → ≈-down i (g a)

  ≈-prefix : ∀ m j {p q} → p ≈[ m + j ] q → p ≈[ m ] q
  ≈-prefix zero    j _       = tt
  ≈-prefix (suc m) j (f , g) = f , λ a → ≈-prefix m j (g a)

  Equiv⇒≈ : ∀ {p q} → Equiv D p D q → ∀ i → p ≈[ i ] q
  Equiv⇒≈ e zero    = tt
  Equiv⇒≈ e (suc i) = e [] , λ a → Equiv⇒≈ (λ w → e (a ∷ w)) i

  ≈⇒Equiv : ∀ {p q} → (∀ i → p ≈[ i ] q) → Equiv D p D q
  ≈⇒Equiv h []      = proj₁ (h 1)
  ≈⇒Equiv h (a ∷ w) = ≈⇒Equiv (λ i → proj₂ (h (suc i)) a) w

------------------------------------------------------------------------
-- The rounds of a well-formed table

module Rounds (D : DFA) (wf : WellFormed D) where

  open Moore D
  open Agreement D

  n : ℕ
  n = size D

  row : ℕ → List ℕ
  row p = lookupOr [] (rows D) p

  row-wf : ∀ {p} → p < n → length (row p) ≡ k × All (_< n) (row p)
  row-wf p< = all-lookup (proj₂ (proj₂ wf)) p<

  letter< : ∀ {p} → p < n → (a : Fin k) → toℕ a < length (row p)
  letter< p< a = subst (toℕ a <_) (sym (proj₁ (row-wf p<))) (toℕ<n a)


  -- round `i`: a leader function of agreement on words shorter than `i`

  record Inv (i : ℕ) (cs : List ℕ) : Set where
    field
      len   : length cs ≡ n
      below : ∀ {p} → p < n → cs ! p ≤ p
      idem  : ∀ {p} → p < n → cs ! (cs ! p) ≡ cs ! p
      sound : ∀ {p q} → p < n → q < n → cs ! p ≡ cs ! q → p ≈[ i ] q
      compl : ∀ {p q} → p < n → q < n → p ≈[ i ] q → cs ! p ≡ cs ! q

  inv₀ : Inv 0 (replicate n 0)
  inv₀ = record
    { len   = length-replicate n
    ; below = λ {p} _ → subst (_≤ p) (sym (!-replicate n p)) z≤n
    ; idem  = λ {p} _ → trans (!-replicate n _) (sym (!-replicate n p))
    ; sound = λ _ _ _ → tt
    ; compl = λ {p} {q} _ _ _ → trans (!-replicate n p) (sym (!-replicate n q))
    }

  -- signatures

  bit : Bool → ℕ
  bit f = if f then 1 else 0

  bit-injective : ∀ {a b} → bit a ≡ bit b → a ≡ b
  bit-injective {true}  {true}  _ = refl
  bit-injective {false} {false} _ = refl

  length-signatures : ∀ cs → length (signatures cs) ≡ n
  length-signatures cs =
    length-zipWith (signature cs) (rows D) (finals D) (sym (proj₁ (proj₂ wf)))

  signature-at : ∀ cs {p} → p < n
               → lookupOr [] (signatures cs) p
               ≡ signature cs (row p) (isFinal D p)
  signature-at cs p< =
    lookup-zipWith (signature cs) (rows D) (finals D) p<
      (subst (_ <_) (sym (proj₁ (proj₂ wf))) p<)

  module _ {i cs} (I : Inv i cs) where

    open Inv I

    signature-sound : ∀ {p q} → p < n → q < n
                    → signature cs (row p) (isFinal D p)
                    ≡ signature cs (row q) (isFinal D q)
                    → p ≈[ suc i ] q
    signature-sound {p} {q} p< q< eq =
      bit-injective (proj₁ (∷-injective eq)) , λ a →
        sound (next-< D wf p< a) (next-< D wf q< a)
          (trans (sym (lookup-map (cs !_) (row p) (letter< p< a)))
            (trans (cong (_! toℕ a) (proj₂ (∷-injective eq)))
                   (lookup-map (cs !_) (row q) (letter< q< a))))

    signature-complete : ∀ {p q} → p < n → q < n → p ≈[ suc i ] q
                       → signature cs (row p) (isFinal D p)
                       ≡ signature cs (row q) (isFinal D q)
    signature-complete {p} {q} p< q< (f , g) =
      cong₂ _∷_ (cong bit f)
        (ext (map (cs !_) (row p)) (map (cs !_) (row q))
          (trans (length-map (cs !_) (row p)) (proj₁ (row-wf p<)))
          (trans (length-map (cs !_) (row q)) (proj₁ (row-wf q<)))
          (λ a → trans (lookup-map (cs !_) (row p) (letter< p< a))
                   (trans (compl (next-< D wf p< a) (next-< D wf q< a) (g a))
                     (sym (lookup-map (cs !_) (row q) (letter< q< a))))))

  -- `first` finds the least position holding a signature

  first-spec : ∀ σ τs {p} → p < length τs → lookupOr [] τs p ≡ σ
             → first σ τs ≤ p × lookupOr [] τs (first σ τs) ≡ σ
  first-spec σ (τ ∷ τs) {zero} _ eq =
    if-case (λ r → r ≤ 0 × lookupOr [] (τ ∷ τs) r ≡ σ) (σ ==ⁿ τ)
      (λ _ → z≤n , eq)
      (λ e → ⊥-elim (subst T e (subst (λ x → T (σ ==ⁿ x)) (sym eq) (==ⁿ-refl σ))))
  first-spec σ (τ ∷ τs) {suc p} (s≤s p<) eq =
    if-case (λ r → r ≤ suc p × lookupOr [] (τ ∷ τs) r ≡ σ) (σ ==ⁿ τ)
      (λ e → z≤n , sym (==ⁿ-sound σ τ (T-true e)))
      (λ _ → let (r≤ , at) = first-spec σ τs p< eq in s≤s r≤ , at)

  -- a round preserves the invariant

  step : ∀ {i cs} → Inv i cs → Inv (suc i) (refine cs)
  step {i} {cs} I = record
    { len   = trans (length-map _ σs) (length-signatures cs)
    ; below = λ p< → subst (_≤ _) (sym (at p<)) (proj₁ (spec p<))
    ; idem  = idem′
    ; sound = λ p< q< eq →
        signature-sound I p< q<
          (trans (sym (signature-at cs p<))
            (trans (same p< q< (trans (sym (at p<)) (trans eq (at q<))))
                   (signature-at cs q<)))
    ; compl = λ p< q< h →
        trans (at p<)
          (trans (cong (λ σ → first σ σs)
                   (trans (signature-at cs p<)
                     (trans (signature-complete I p< q< h)
                            (sym (signature-at cs q<)))))
                 (sym (at q<)))
    }
    where
    σs = signatures cs

    σ : ℕ → List ℕ
    σ p = lookupOr [] σs p

    σs< : ∀ {p} → p < n → p < length σs
    σs< p< = subst (_ <_) (sym (length-signatures cs)) p<

    at : ∀ {p} → p < n → refine cs ! p ≡ first (σ p) σs
    at p< = lookup-map (λ τ → first τ σs) σs (σs< p<)

    spec : ∀ {p} → p < n → first (σ p) σs ≤ p × σ (first (σ p) σs) ≡ σ p
    spec p< = first-spec (σ _) σs (σs< p<) refl

    first< : ∀ {p} → p < n → first (σ p) σs < n
    first< p< = ≤-<-trans (proj₁ (spec p<)) p<

    same : ∀ {p q} → p < n → q < n → first (σ p) σs ≡ first (σ q) σs
         → σ p ≡ σ q
    same p< q< eq =
      trans (sym (proj₂ (spec p<))) (trans (cong σ eq) (proj₂ (spec q<)))

    idem′ : ∀ {p} → p < n → refine cs ! (refine cs ! p) ≡ refine cs ! p
    idem′ {p} p< rewrite at p< =
      trans (at (first< p<)) (cong (λ τ → first τ σs) (proj₂ (spec p<)))

  -- a round that changes the partition gains a fixed point

  μ : List ℕ → ℕ
  μ cs = count (λ p → cs ! p ≡ᵇ p) n

  grows : ∀ {i cs} → Inv i cs → ¬ T (refine cs ==ⁿ cs) → μ cs < μ (refine cs)
  grows {i} {cs} I h =
    count-strict (λ x → cs ! x ≡ᵇ x) (λ x → cs′ ! x ≡ᵇ x) n kept
      b< (≡⇒≡ᵇ _ _ (Inv.idem I′ p<)) new
    where
    cs′ = refine cs
    I′  = step I

    differ = ==ⁿ-differ cs′ cs (trans (Inv.len I′) (sym (Inv.len I))) h
    p   = proj₁ differ
    p<  = subst (p <_) (Inv.len I′) (proj₁ (proj₂ differ))
    ne  = proj₂ (proj₂ differ)
    b   = cs′ ! p
    b<  = ≤-<-trans (Inv.below I′ p<) p<

    refines : ∀ {x y} → x < n → y < n → cs′ ! x ≡ cs′ ! y → cs ! x ≡ cs ! y
    refines x< y< eq =
      Inv.compl I x< y< (≈-down i (Inv.sound I′ x< y< eq))

    new : ¬ T (cs ! b ≡ᵇ b)
    new t = ne (trans (sym (≡ᵇ⇒≡ _ _ t)) (refines b< p< (Inv.idem I′ p<)))

    kept : ∀ {x} → x < n → T (cs ! x ≡ᵇ x) → T (cs′ ! x ≡ᵇ x)
    kept {x} x< t = ≡⇒≡ᵇ _ _ (≤-antisym (Inv.below I′ x<) x≤y)
      where
      y<  = ≤-<-trans (Inv.below I′ x<) x<
      x≤y = subst (_≤ cs′ ! x)
              (trans (refines y< x< (Inv.idem I′ x<)) (≡ᵇ⇒≡ _ _ t))
              (Inv.below I y<)

  -- the rounds end at a fixpoint of `refine`

  Fix : List ℕ → Set
  Fix cs = Σ ℕ λ j → Inv j cs × refine cs ≡ cs

  rounds-fix : ∀ f {i} cs → Inv i cs → suc n ≤ f + μ cs → Fix (rounds f cs)
  rounds-fix zero cs I h = ⊥-elim (<-irrefl refl (≤-trans h (count-≤ _ n)))
  rounds-fix (suc f) {i} cs I h =
    if-case Fix (refine cs ==ⁿ cs)
      (λ e → i , I , ==ⁿ-sound _ _ (T-true e))
      (λ e → rounds-fix f (refine cs) (step I)
               (≤-trans h (subst (_≤ f + μ (refine cs)) (+-suc f (μ cs))
                 (+-monoʳ-≤ f (grows I (λ t → subst T e t))))))

  fixed : Fix equivalence
  fixed = rounds-fix (suc n) (replicate n 0) inv₀ (m≤m+n (suc n) _)

  j : ℕ
  j = proj₁ fixed

  -- at a fixpoint, every later round has the same partition

  later : ∀ d → Inv (d + j) equivalence
  later zero    = proj₁ (proj₂ fixed)
  later (suc d) = subst (Inv (suc (d + j))) (proj₂ (proj₂ fixed)) (step (later d))

------------------------------------------------------------------------
-- Language equivalence

moore-sound : ∀ D → WellFormed D → ∀ {p q} → p < size D → q < size D
            → Moore.equivalence D ! p ≡ Moore.equivalence D ! q → Equiv D p D q
moore-sound D wf p< q< eq =
  ≈⇒Equiv (λ m → ≈-prefix m j (Inv.sound (later m) p< q< eq))
  where
  open Agreement D
  open Rounds D wf

moore-complete : ∀ D → WellFormed D → ∀ {p q} → p < size D → q < size D
               → Equiv D p D q → Moore.equivalence D ! p ≡ Moore.equivalence D ! q
moore-complete D wf p< q< e = Inv.compl (later 0) p< q< (Equiv⇒≈ e j)
  where
  open Agreement D
  open Rounds D wf
