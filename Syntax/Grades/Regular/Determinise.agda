------------------------------------------------------------------------
-- Determinising a finite automaton with silent moves.                --
--                                                                    --
-- An automaton over the letters `Fin k` has states of a type with    --
-- decidable equality, silent moves that may depend on the letter to  --
-- be read next (or on the end of the word), moves reading a letter,  --
-- and accepting states. A word is accepted from a state when silent  --
-- moves before each letter, a move reading it, and silent moves at   --
-- the end reach an accepting state:                                  --
--                                                                    --
--   Acc c []       iff  c ⟶* c′ at the end, c′ accepting             --
--   Acc c (a ∷ w)  iff  c ⟶* c′ before a, c″ ∈ read a c′, Acc c″ w   --
--                                                                    --
-- When a finite list of states contains the start and is closed      --
-- under the moves, the subset construction is a lawful automaton     --
-- accepting the same words: its states are lists of states compared  --
-- as sets, a step closes a set under silent moves (saturating it at  --
-- most once per listed state) and reads the letter.                  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _^_; _≤_; _<_; z≤n; s≤s)

module Syntax.Grades.Regular.Determinise (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; filter; length)
open import Data.List.Properties using (length-++; length-map)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻; ∈-concatMap⁺; ∈-concatMap⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (Equivalence; _⇔_; mk⇔)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)

open import Syntax.Grades.Regular.Automaton k hiding (_∈_; _⊆_; accepts)
import Syntax.Grades.Regular.Automaton k as A
open import Syntax.Grades.Regular.Constructions.Base k using (T-any⁻; T-any⁺)
open import Syntax.Grades.Regular.Explore k using (explore-wf; explore-accepts)
open import Syntax.Grades.Regular.Basics k using (T-∧⁻; T-∧⁺)

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Automata with silent moves

record ENFA (C : Set) : Set where
  field
    start   : C
    silent  : Maybe Letter → C → List C
    reads   : Letter → C → List C
    accept  : C → Bool

module _ {C : Set} (N : ENFA C) where

  open ENFA N

  -- silent moves before a letter, or at the end

  data Silent* (x : Maybe Letter) : C → C → Set where
    here  : ∀ {c} → Silent* x c c
    there : ∀ {c c′ c″} → c′ ∈ silent x c → Silent* x c′ c″ → Silent* x c c″

  silent-snoc : ∀ {x c c′ c″} → Silent* x c c′ → c″ ∈ silent x c′ → Silent* x c c″
  silent-snoc here        m = there m here
  silent-snoc (there n s) m = there n (silent-snoc s m)

  Acc : C → Word → Set
  Acc c []      = Σ[ c′ ∈ C ] Silent* nothing c c′ × T (accept c′)
  Acc c (a ∷ w) = Σ[ c′ ∈ C ] Σ[ c″ ∈ C ] Silent* (just a) c c′ × c″ ∈ reads a c′ × Acc c″ w

------------------------------------------------------------------------
-- Lists without repetition

module Lists {C : Set} (_≟_ : DecidableEquality C) where

  open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

  Distinct : List C → Set
  Distinct []       = Data.Unit.Base.⊤
  Distinct (x ∷ xs) = ¬ (x ∈ xs) × Distinct xs

  -- a list without repetition is no longer than any list containing it

  private
    remove : ∀ {x} (ys : List C) → x ∈ ys → List C
    remove (y ∷ ys) (here _)  = ys
    remove (y ∷ ys) (there m) = y ∷ remove ys m

    remove-length : ∀ {x} (ys : List C) (m : x ∈ ys) → suc (length (remove ys m)) ≡ length ys
    remove-length (y ∷ ys) (here _)  = refl
    remove-length (y ∷ ys) (there m) = cong suc (remove-length ys m)

    remove-∈ : ∀ {x z} (ys : List C) (m : x ∈ ys) → z ∈ ys → z ≢ x → z ∈ remove ys m
    remove-∈ (y ∷ ys) (here refl) (here refl) ne = ⊥-elim (ne refl)
    remove-∈ (y ∷ ys) (here refl) (there n)   ne = n
    remove-∈ (y ∷ ys) (there m)   (here refl) ne = here refl
    remove-∈ (y ∷ ys) (there m)   (there n)   ne = there (remove-∈ ys m n ne)

  pigeonhole : ∀ xs ys → Distinct xs → (∀ {z} → z ∈ xs → z ∈ ys) → length xs ≤ length ys
  pigeonhole []       ys _          _   = z≤n
  pigeonhole (x ∷ xs) ys (x∉ , dxs) sub =
    subst (suc (length xs) ≤_) (remove-length ys (sub (here refl)))
      (s≤s (pigeonhole xs (remove ys (sub (here refl))) dxs
              (λ {z} m → remove-∈ ys (sub (here refl)) (sub (there m)) (λ { refl → x∉ m }))))

  -- removing repetitions

  nub : List C → List C
  nub []       = []
  nub (x ∷ xs) with x ∈? nub xs
  ... | yes _ = nub xs
  ... | no _  = x ∷ nub xs

  nub⁺ : ∀ {z} xs → z ∈ xs → z ∈ nub xs
  nub⁺ (x ∷ xs) m with x ∈? nub xs
  nub⁺ (x ∷ xs) (here refl) | yes p = p
  nub⁺ (x ∷ xs) (there m)   | yes p = nub⁺ xs m
  nub⁺ (x ∷ xs) (here refl) | no _  = here refl
  nub⁺ (x ∷ xs) (there m)   | no _  = there (nub⁺ xs m)

  nub⁻ : ∀ {z} xs → z ∈ nub xs → z ∈ xs
  nub⁻ (x ∷ xs) m with x ∈? nub xs
  nub⁻ (x ∷ xs) m          | yes _ = there (nub⁻ xs m)
  nub⁻ (x ∷ xs) (here refl) | no _ = here refl
  nub⁻ (x ∷ xs) (there m)   | no _ = there (nub⁻ xs m)

  nub-distinct : ∀ xs → Distinct (nub xs)
  nub-distinct []       = tt
  nub-distinct (x ∷ xs) with x ∈? nub xs
  ... | yes _ = nub-distinct xs
  ... | no ¬p = ¬p , nub-distinct xs

  -- inclusion and set equality, decided

  _⊆ᵇ_ : List C → List C → Bool
  xs ⊆ᵇ ys = ⌊ All.all? (_∈? ys) xs ⌋

  ⊆ᵇ⇒ : ∀ {xs ys} → T (xs ⊆ᵇ ys) → ∀ {z} → z ∈ xs → z ∈ ys
  ⊆ᵇ⇒ {xs} {ys} t = All.lookup (toWitness {a? = All.all? (_∈? ys) xs} t)

  ⇒⊆ᵇ : ∀ {xs ys} → (∀ {z} → z ∈ xs → z ∈ ys) → T (xs ⊆ᵇ ys)
  ⇒⊆ᵇ {xs} {ys} s = fromWitness {a? = All.all? (_∈? ys) xs} (All.tabulate s)

  _≈_ : List C → List C → Set
  xs ≈ ys = (∀ {z} → z ∈ xs → z ∈ ys) × (∀ {z} → z ∈ ys → z ∈ xs)

  _≈ᵇ_ : List C → List C → Bool
  xs ≈ᵇ ys = (xs ⊆ᵇ ys) ∧ (ys ⊆ᵇ xs)

  ≈ᵇ⇒ : ∀ {xs ys} → T (xs ≈ᵇ ys) → xs ≈ ys
  ≈ᵇ⇒ {xs} t with T-∧⁻ {xs ⊆ᵇ _} t
  ... | a , b = ⊆ᵇ⇒ a , ⊆ᵇ⇒ b

  ⇒≈ᵇ : ∀ {xs ys} → xs ≈ ys → T (xs ≈ᵇ ys)
  ⇒≈ᵇ (a , b) = T-∧⁺ (⇒⊆ᵇ a) (⇒⊆ᵇ b)

  -- all sublists

  sublists : List C → List (List C)
  sublists []       = [] ∷ []
  sublists (x ∷ xs) = map (x ∷_) (sublists xs) ++ sublists xs

  length-sublists : ∀ xs → length (sublists xs) ≡ 2 ^ length xs
  length-sublists []       = refl
  length-sublists (x ∷ xs) =
    trans (length-++ (map (x ∷_) (sublists xs)))
      (trans (cong (_+ length (sublists xs)) (length-map (x ∷_) (sublists xs)))
        (trans (cong (λ m → m + m) (length-sublists xs))
               (cong (2 ^ length xs +_) (sym (ℕ.+-identityʳ _)))))

  filter-sublist : ∀ (P : C → Set) (P? : ∀ c → Dec (P c)) xs → filter P? xs ∈ sublists xs
  filter-sublist P P? []       = here refl
  filter-sublist P P? (x ∷ xs) with P? x
  ... | yes _ = ∈-++⁺ˡ (∈-map⁺ (x ∷_) (filter-sublist P P? xs))
  ... | no _  = ∈-++⁺ʳ (map (x ∷_) (sublists xs)) (filter-sublist P P? xs)

------------------------------------------------------------------------
-- The subset construction

module Determinise {C : Set} (_≟_ : DecidableEquality C) (N : ENFA C)
  (univ : List C)
  (start-univ  : ENFA.start N ∈ univ)
  (silent-univ : ∀ x {c c′} → c ∈ univ → c′ ∈ ENFA.silent N x c → c′ ∈ univ)
  (reads-univ  : ∀ a {c c′} → c ∈ univ → c′ ∈ ENFA.reads N a c → c′ ∈ univ) where

  open ENFA N
  open Lists _≟_
  open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

  Good : List C → Set
  Good S = ∀ {c} → c ∈ S → c ∈ univ

  -- closing a set under silent moves

  fresh : List C → List C → List C
  fresh S = filter (λ c → ¬? (c ∈? S))

  saturate : Maybe Letter → ℕ → List C → List C
  saturate x zero    S = S
  saturate x (suc f) S with fresh S (concatMap (silent x) S)
  ... | []    = S
  ... | c ∷ _ = saturate x f (c ∷ S)

  close : Maybe Letter → List C → List C
  close x S = saturate x (suc (length univ)) (nub S)

  private
    Closed : Maybe Letter → List C → Set
    Closed x R = ∀ {c c′} → c ∈ R → c′ ∈ silent x c → c′ ∈ R

    fresh-∈ : ∀ S xs {c} → c ∈ fresh S xs → c ∈ xs × ¬ (c ∈ S)
    fresh-∈ S xs m = ∈-filter⁻ (λ c → ¬? (c ∈? S)) m

    silent-∈ : ∀ x S {c′} → c′ ∈ concatMap (silent x) S → ∃ λ c → c ∈ S × c′ ∈ silent x c
    silent-∈ x S m = find (∈-concatMap⁻ (silent x) m)

    -- saturation grows the set
    sat-⊇ : ∀ x f S {c} → c ∈ S → c ∈ saturate x f S
    sat-⊇ x zero    S m = m
    sat-⊇ x (suc f) S m with fresh S (concatMap (silent x) S)
    ... | []    = m
    ... | c ∷ _ = sat-⊇ x f (c ∷ S) (there m)

    -- and stays within what the silent moves reach
    sat-reach : ∀ x f S (P : C → Set) → (∀ {c c′} → P c → c′ ∈ silent x c → P c′)
              → All P S → All P (saturate x f S)
    sat-reach x zero    S P step ps = ps
    sat-reach x (suc f) S P step ps with fresh S (concatMap (silent x) S) in e
    ... | []    = ps
    ... | c ∷ _ = sat-reach x f (c ∷ S) P step (pc ∷ ps)
      where
        m : c ∈ fresh S (concatMap (silent x) S)
        m = subst (c ∈_) (sym e) (here refl)
        pc : P c
        pc with silent-∈ x S (proj₁ (fresh-∈ S (concatMap (silent x) S) m))
        ... | c₀ , c₀∈ , mv = step (All.lookup ps c₀∈) mv

    -- with fuel past the size of the universe, saturation closes
    sat-closed : ∀ x f S → Distinct S → Good S → length univ < length S + f
               → Closed x (saturate x f S)
    sat-closed x zero S dS gS r =
      ⊥-elim (ℕ.<-irrefl refl (ℕ.<-≤-trans (subst (length univ <_) (ℕ.+-identityʳ _) r)
                                            (pigeonhole S univ dS gS)))
    sat-closed x (suc f) S dS gS r with fresh S (concatMap (silent x) S) in e
    ... | [] = λ c∈ mv → closed c∈ mv
      where
        closed : ∀ {c c′} → c ∈ S → c′ ∈ silent x c → c′ ∈ S
        closed {c} {c′} c∈ mv with c′ ∈? S
        ... | yes p = p
        ... | no ¬p = case (subst (c′ ∈_) e (∈-filter⁺ (λ c → ¬? (c ∈? S))
                             (∈-concatMap⁺ (silent x) (lose c∈ mv)) ¬p))
          where
            case : c′ ∈ [] → c′ ∈ S
            case ()
    ... | c ∷ _ = sat-closed x f (c ∷ S) (¬c∈ , dS) good′
                    (subst (length univ <_) (ℕ.+-suc (length S) f) r)
      where
        m : c ∈ fresh S (concatMap (silent x) S)
        m = subst (c ∈_) (sym e) (here refl)
        ¬c∈ : ¬ (c ∈ S)
        ¬c∈ = proj₂ (fresh-∈ S (concatMap (silent x) S) m)
        good′ : Good (c ∷ S)
        good′ (here refl) with silent-∈ x S (proj₁ (fresh-∈ S (concatMap (silent x) S) m))
        ... | c₀ , c₀∈ , mv = silent-univ x (gS c₀∈) mv
        good′ (there n) = gS n

    reach-closed : ∀ {x R c c′} → Closed x R → c ∈ R → Silent* N x c c′ → c′ ∈ R
    reach-closed cl m here          = m
    reach-closed cl m (there mv s)  = reach-closed cl (cl m mv) s

  close-sound : ∀ x S {c′} → c′ ∈ close x S → ∃ λ c → c ∈ S × Silent* N x c c′
  close-sound x S m =
    All.lookup (sat-reach x (suc (length univ)) (nub S) (λ c′ → ∃ λ c → c ∈ S × Silent* N x c c′)
                 (λ { (c₀ , c₀∈ , s) mv → c₀ , c₀∈ , silent-snoc N s mv })
                 (All.tabulate (λ {c} c∈ → c , nub⁻ S c∈ , here))) m

  close-complete : ∀ x S → Good S → ∀ {c c′} → c ∈ S → Silent* N x c c′ → c′ ∈ close x S
  close-complete x S gS c∈ s =
    reach-closed (sat-closed x (suc (length univ)) (nub S) (nub-distinct S)
                    (λ m → gS (nub⁻ S m))
                    (ℕ.m≤n+m (suc (length univ)) (length (nub S))))
                 (sat-⊇ x _ (nub S) (nub⁺ S c∈)) s

  close-good : ∀ x S → Good S → Good (close x S)
  close-good x S gS m with close-sound x S m
  ... | c , c∈ , s = reach-univ (gS c∈) s
    where
      reach-univ : ∀ {c c′} → c ∈ univ → Silent* N x c c′ → c′ ∈ univ
      reach-univ u here         = u
      reach-univ u (there mv s) = reach-univ (silent-univ x u mv) s

  -- the automaton of sets

  step : List C → Letter → List C
  step S a = nub (concatMap (reads a) (close (just a) S))

  final : List C → Bool
  final S = any accept (close nothing S)

  subsets : Automaton
  subsets = record
    { State = List C
    ; _≟_   = _≈ᵇ_
    ; start = start ∷ []
    ; δ     = step
    ; final = final
    ; bound = 2 ^ length univ
    }

  ----------------------------------------------------------------------
  -- Steps and acceptance, by membership

  private
    step-∈ : ∀ S a {c″} → c″ ∈ step S a → ∃ λ c′ → c′ ∈ close (just a) S × c″ ∈ reads a c′
    step-∈ S a m = find (∈-concatMap⁻ (reads a) (nub⁻ _ m))

    ∈-step : ∀ S a {c′ c″} → c′ ∈ close (just a) S → c″ ∈ reads a c′ → c″ ∈ step S a
    ∈-step S a c′∈ m = nub⁺ _ (∈-concatMap⁺ (reads a) (lose c′∈ m))

  good-step : ∀ {S} a → Good S → Good (step S a)
  good-step {S} a gS m with step-∈ S a m
  ... | c′ , c′∈ , mv = reads-univ a (close-good (just a) S gS c′∈) mv

  -- closures of sets with the same members have the same members

  private
    close-≈ : ∀ x {S S′} → Good S → Good S′ → S ≈ S′ → close x S ≈ close x S′
    close-≈ x {S} {S′} gS gS′ (a , b) =
      (λ m → let (c , c∈ , s) = close-sound x S m in close-complete x S′ gS′ (a c∈) s) ,
      (λ m → let (c , c∈ , s) = close-sound x S′ m in close-complete x S gS (b c∈) s)

    any-≈ : ∀ {S S′} → S ≈ S′ → any accept S ≡ any accept S′
    any-≈ {S} {S′} (a , b) with any accept S in e | any accept S′ in e′
    ... | true  | true  = refl
    ... | false | false = refl
    ... | true  | false with find (T-any⁻ accept S (subst T (sym e) tt))
    ...   | c , c∈ , t = ⊥-elim (subst T e′ (T-any⁺ accept (lose (a c∈) t)))
    any-≈ {S} {S′} (a , b) | false | true with find (T-any⁻ accept S′ (subst T (sym e′) tt))
    ...   | c , c∈ , t = ⊥-elim (subst T e (T-any⁺ accept (lose (b c∈) t)))

  lawful : Lawful subsets
  lawful = record
    { Good       = Good
    ; good-start = λ { (here refl) → start-univ }
    ; good-δ     = good-step
    ; ≟-refl     = λ S → ⇒≈ᵇ {S} {S} ((λ m → m) , (λ m → m))
    ; ≟-sym      = λ {S} {S′} t → let (a , b) = ≈ᵇ⇒ {S} {S′} t in ⇒≈ᵇ {S′} {S} (b , a)
    ; ≟-trans    = λ {S} {S′} {S″} t u → let (a , b) = ≈ᵇ⇒ {S} {S′} t ; (c , d) = ≈ᵇ⇒ {S′} {S″} u
                                         in ⇒≈ᵇ {S} {S″} ((λ m → c (a m)) , (λ m → b (d m)))
    ; ≟-final    = λ {S} {S′} gS gS′ t → any-≈ (close-≈ nothing gS gS′ (≈ᵇ⇒ {S} {S′} t))
    ; ≟-δ        = λ {S} {S′} gS gS′ t a →
        let (p , q) = close-≈ (just a) gS gS′ (≈ᵇ⇒ {S} {S′} t) in
        ⇒≈ᵇ {step S a} {step S′ a} ((λ m → let (c′ , c′∈ , mv) = step-∈ S a m in ∈-step S′ a (p c′∈) mv) ,
             (λ m → let (c′ , c′∈ , mv) = step-∈ S′ a m in ∈-step S a (q c′∈) mv))
    ; enum       = sublists univ
    ; enum-bound = ℕ.≤-reflexive (length-sublists univ)
    ; enum-cover = λ {S} gS →
        lose (filter-sublist (_∈ S) (_∈? S) univ)
             (⇒≈ᵇ {S} {filter (_∈? S) univ}
                  ((λ m → ∈-filter⁺ (_∈? S) (gS m) m) , (λ m → proj₂ (∈-filter⁻ (_∈? S) {xs = univ} m))))
    }

  ----------------------------------------------------------------------
  -- The automaton of sets accepts the words of the automaton

  private
    Sem : List C → Word → Set
    Sem S w = Any (λ c → Acc N c w) S

    final-sem : ∀ S → Good S → T (final S) ⇔ Sem S []
    final-sem S gS = mk⇔ to′ from′
      where
        to′ : T (final S) → Sem S []
        to′ t with find (T-any⁻ accept (close nothing S) t)
        ... | c′ , c′∈ , a with close-sound nothing S c′∈
        ...   | c , c∈ , s = lose c∈ (c′ , s , a)
        from′ : Sem S [] → T (final S)
        from′ x with find x
        ... | c , c∈ , (c′ , s , a) = T-any⁺ accept (lose (close-complete nothing S gS c∈ s) a)

    step-sem : ∀ S a w → Good S → Sem (step S a) w ⇔ Sem S (a ∷ w)
    step-sem S a w gS = mk⇔ to′ from′
      where
        to′ : Sem (step S a) w → Sem S (a ∷ w)
        to′ x with find x
        ... | c″ , c″∈ , acc with step-∈ S a c″∈
        ...   | c′ , c′∈ , mv with close-sound (just a) S c′∈
        ...     | c , c∈ , s = lose c∈ (c′ , c″ , s , mv , acc)
        from′ : Sem S (a ∷ w) → Sem (step S a) w
        from′ x with find x
        ... | c , c∈ , (c′ , c″ , s , mv , acc) =
          lose (∈-step S a (close-complete (just a) S gS c∈ s) mv) acc

    accepts-sem : ∀ S w → Good S → T (Automaton.final subsets (Automaton.δ* subsets S w)) ⇔ Sem S w
    accepts-sem S []      gS = final-sem S gS
    accepts-sem S (a ∷ w) gS =
      mk⇔ (λ t → to (step-sem S a w gS) (to (accepts-sem (step S a) w (good-step a gS)) t))
          (λ x → from (accepts-sem (step S a) w (good-step a gS)) (from (step-sem S a w gS) x))

  accepts-subsets : ∀ w → T (Automaton.accepts subsets w) ⇔ Acc N start w
  accepts-subsets w =
    mk⇔ (λ t → single (to (accepts-sem (start ∷ []) w (λ { (here refl) → start-univ })) t))
        (λ x → from (accepts-sem (start ∷ []) w (λ { (here refl) → start-univ })) (here x))
    where
      single : Sem (start ∷ []) w → Acc N start w
      single (here x) = x

  -- the table

  determinised : DFA
  determinised = explore subsets

  determinised-wf : WellFormed determinised
  determinised-wf = explore-wf subsets lawful

  ∈-determinised : ∀ w → w A.∈ determinised ⇔ Acc N start w
  ∈-determinised w =
    mk⇔ (λ t → to (accepts-subsets w) (subst T (explore-accepts subsets lawful w) t))
        (λ x → subst T (sym (explore-accepts subsets lawful w)) (from (accepts-subsets w) x))
