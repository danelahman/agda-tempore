------------------------------------------------------------------------
-- Whether a state of a finite graph reaches an accepting one.        --
--                                                                    --
-- The graph has states of a type with decidable equality, the moves  --
-- from a state listed, and a finite list of states, closed under the --
-- moves for the search to be correct (`Correct`). The search keeps   --
-- the states processed and the states still to process, in the order --
-- found; it takes the next state, stops if it accepts, and otherwise --
-- queues the states it moves to that are new. Each state is          --
-- processed at most once, so one round per state of the list is fuel --
-- enough, and the search stops early when an accepting state is      --
-- found.                                                             --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; filter; length)
open import Data.List.Membership.Propositional using (_∈_)

module Grades.Regular.Reach
  {C : Set} (_≟_ : DecidableEquality C)
  (next : C → List C) (accept : C → Bool) (univ : List C) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; _+_; s≤s; z≤n)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)

open import Grades.Regular.Determinise 0 using (module Lists)
open Lists _≟_ using (Distinct; pigeonhole; nub; nub⁺; nub⁻; nub-distinct)

------------------------------------------------------------------------
-- Paths

data Path : C → C → Set where
  here  : ∀ {c} → Path c c
  there : ∀ {c c′ c″} → c′ ∈ next c → Path c′ c″ → Path c c″

Reaches : C → Set
Reaches s = Σ[ c ∈ C ] Path s c × T (accept c)

------------------------------------------------------------------------
-- The search

-- the states moved to from `c` that are not among `seen`

fresh : List C → C → List C
fresh seen c = nub (filter (λ d → ¬? (d ∈? seen)) (next c))

-- the fuel is a list, one round per element, so that it is used only
-- as far as the rounds go

search : List C → List C → List C → Bool
search []      done []         = false
search []      done (c ∷ todo) = false
search (_ ∷ f) done []         = false
search (_ ∷ f) done (c ∷ todo) =
  if accept c then true else search f (done ++ c ∷ []) (todo ++ fresh (done ++ c ∷ todo) c)

found : C → Bool
found s = search (s ∷ univ) [] (s ∷ [])

------------------------------------------------------------------------
-- Correctness, when the list of states is closed under the moves

module Correct (closed : ∀ {c c′} → c ∈ univ → c′ ∈ next c → c′ ∈ univ) where

 private
   ∈-fresh : ∀ seen c {d} → d ∈ fresh seen c → d ∈ next c × ¬ (d ∈ seen)
   ∈-fresh seen c m with ∈-filter⁻ (λ d → ¬? (d ∈? seen)) (nub⁻ _ m)
   ... | m′ , ¬m = m′ , ¬m

   fresh-∈ : ∀ seen c {d} → d ∈ next c → ¬ (d ∈ seen) → d ∈ fresh seen c
   fresh-∈ seen c m ¬m = nub⁺ _ (∈-filter⁺ (λ d → ¬? (d ∈? seen)) m ¬m)

   distinct-++ : ∀ xs {ys} → Distinct xs → Distinct ys → (∀ {z} → z ∈ xs → ¬ (z ∈ ys)) → Distinct (xs ++ ys)
   distinct-++ []       _          dy _  = dy
   distinct-++ (x ∷ xs) (x∉ , dxs) dy dj =
     (λ m → case (∈-++⁻ xs m)) , distinct-++ xs dxs dy (λ m → dj (there m))
     where
       case : _ ⊎ _ → ⊥
       case (inj₁ m) = x∉ m
       case (inj₂ m) = dj (here refl) m

   -- the order of the states seen, reassociated

   shift : ∀ (done : List C) c todo new → (done ++ c ∷ []) ++ (todo ++ new) ≡ (done ++ c ∷ todo) ++ new
   shift done c todo new =
     trans (++-assoc done (c ∷ []) (todo ++ new)) (sym (++-assoc done (c ∷ todo) new))

   ∈-shift : ∀ done c todo new {z} → z ∈ (done ++ c ∷ todo) ++ new → z ∈ (done ++ c ∷ []) ++ (todo ++ new)
   ∈-shift done c todo new = subst (_ ∈_) (sym (shift done c todo new))

   -- an invariant of the search from a start `s`: what has been seen,
   -- the states processed and those still to process, are distinct,
   -- among the states, reached from `s`; `s` has been seen; and a
   -- processed state accepts nothing and moves only to states seen

 record Inv (s : C) (done todo : List C) : Set where
   field
     distinct : Distinct (done ++ todo)
     inUniv   : ∀ {x} → x ∈ done ++ todo → x ∈ univ
     reached  : ∀ {x} → x ∈ done ++ todo → Path s x
     start    : s ∈ done ++ todo
     moves    : ∀ {d d′} → d ∈ done → d′ ∈ next d → d′ ∈ done ++ todo
     rejects  : ∀ {d} → d ∈ done → ¬ T (accept d)

 private
   path-snoc : ∀ {a x y} → Path a x → y ∈ next x → Path a y
   path-snoc here         m = there m here
   path-snoc (there m′ p) m = there m′ (path-snoc p m)

   -- the step keeps the invariant

   step-inv : ∀ {s done c todo} → Inv s done (c ∷ todo) → ¬ T (accept c)
            → Inv s (done ++ c ∷ []) (todo ++ fresh (done ++ c ∷ todo) c)
   step-inv {s} {done} {c} {todo} I ¬a = record
     { distinct = subst Distinct (sym (shift done c todo new))
                    (distinct-++ (done ++ c ∷ todo) (Inv.distinct I) (nub-distinct (filter (λ d → ¬? (d ∈? seen)) (next c)))
                       (λ m m′ → proj₂ (∈-fresh seen c m′) m))
     ; inUniv   = λ m → old-or-new m (Inv.inUniv I) (λ m′ → closed (Inv.inUniv I c∈) (proj₁ (∈-fresh seen c m′)))
     ; reached  = λ m → old-or-new m (Inv.reached I)
                          (λ m′ → path-snoc (Inv.reached I c∈) (proj₁ (∈-fresh seen c m′)))
     ; start    = ∈-shift done c todo new (∈-++⁺ˡ (Inv.start I))
     ; moves    = moves′
     ; rejects  = rejects′
     }
     where
       seen new : List C
       seen = done ++ c ∷ todo
       new  = fresh seen c

       c∈ : c ∈ seen
       c∈ = ∈-++⁺ʳ done (here refl)

       old-or-new : ∀ {P : C → Set} {z} → z ∈ (done ++ c ∷ []) ++ (todo ++ new)
                  → (∀ {x} → x ∈ seen → P x) → (∀ {x} → x ∈ new → P x) → P z
       old-or-new m old nw with ∈-++⁻ seen (subst (_ ∈_) (shift done c todo new) m)
       ... | inj₁ m′ = old m′
       ... | inj₂ m′ = nw m′

       seen⊆ : ∀ {x} → x ∈ seen → x ∈ (done ++ c ∷ []) ++ (todo ++ new)
       seen⊆ m = ∈-shift done c todo new (∈-++⁺ˡ m)

       moves′ : ∀ {d d′} → d ∈ done ++ c ∷ [] → d′ ∈ next d → d′ ∈ (done ++ c ∷ []) ++ (todo ++ new)
       moves′ {d} {d′} m m′ with ∈-++⁻ done m
       ... | inj₁ md = seen⊆ (Inv.moves I md m′)
       ... | inj₂ (here refl) with d′ ∈? seen
       ...   | yes y = seen⊆ y
       ...   | no ¬y = ∈-shift done c todo new (∈-++⁺ʳ seen (fresh-∈ seen c m′ ¬y))

       rejects′ : ∀ {d} → d ∈ done ++ c ∷ [] → ¬ T (accept d)
       rejects′ m with ∈-++⁻ done m
       ... | inj₁ md          = Inv.rejects I md
       ... | inj₂ (here refl) = ¬a

   -- a closed set with the start and no accepting state reaches none

   closed-rejects : ∀ {s done} → Inv s done [] → ¬ Reaches s
   closed-rejects {s} {done} I (c , p , a) = Inv.rejects I (go (subst (s ∈_) (++-identityʳ′ done) (Inv.start I)) p) a
     where
       ++-identityʳ′ : ∀ (xs : List C) → xs ++ [] ≡ xs
       ++-identityʳ′ = Data.List.Properties.++-identityʳ
         where import Data.List.Properties

       go : ∀ {x y} → x ∈ done → Path x y → y ∈ done
       go m here          = m
       go m (there m′ p′) = go (subst (_ ∈_) (++-identityʳ′ done) (Inv.moves I m m′)) p′

   -- the fuel suffices

   room : ∀ {s done todo} → Inv s done todo → length done ≤ length univ
   room {s} {done} {todo} I =
     ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n (length done) (length todo)) (ℕ.≤-reflexive (sym (length-++ done))))
               (pigeonhole (done ++ todo) univ (Inv.distinct I) (Inv.inUniv I))

   search-sound : ∀ {s} f done todo → Inv s done todo → T (search f done todo) → Reaches s
   search-sound []      done []         I ()
   search-sound []      done (_ ∷ _)    I ()
   search-sound (_ ∷ f) done []         I ()
   search-sound (_ ∷ f) done (c ∷ todo) I t with accept c in e
   ... | true  = c , Inv.reached I (∈-++⁺ʳ done (here refl)) , subst T (sym e) tt
   ... | false = search-sound f (done ++ c ∷ []) _ (step-inv I (λ a → subst T e a)) t

   search-complete : ∀ {s} f done todo → Inv s done todo → suc (length univ) ≤ length f + length done
                   → Reaches s → T (search f done todo)
   search-complete []      done todo I le r = ⊥-elim (ℕ.<-irrefl refl (ℕ.<-≤-trans le (room I)))
   search-complete (_ ∷ f) done []   I le r = ⊥-elim (closed-rejects I r)
   search-complete {s} (_ ∷ f) done (c ∷ todo) I le r with accept c in e
   ... | true  = tt
   ... | false =
     search-complete f (done ++ c ∷ []) _ (step-inv I (λ a → subst T e a))
       (ℕ.≤-trans le (ℕ.≤-reflexive (sym (trans (cong (length f +_) (trans (length-++ done) (ℕ.+-comm (length done) 1)))
                                                 (ℕ.+-suc (length f) (length done)))))) r

 found⇔ : ∀ {s} → s ∈ univ → (T (found s) → Reaches s) × (Reaches s → T (found s))
 found⇔ {s} s∈ =
   search-sound (s ∷ univ) [] (s ∷ []) I , search-complete (s ∷ univ) [] (s ∷ []) I (ℕ.≤-reflexive (sym (ℕ.+-identityʳ _)))
   where
     I : Inv s [] (s ∷ [])
     I = record
       { distinct = (λ ()) , tt
       ; inUniv   = λ { (here refl) → s∈ }
       ; reached  = λ { (here refl) → here }
       ; start    = here refl
       ; moves    = λ ()
       ; rejects  = λ ()
       }
