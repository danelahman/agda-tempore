------------------------------------------------------------------------
-- Realisable boxes of mode times over whole steps.                   --
--                                                                    --
-- A box of mode times bounds, by an interval of whole steps, the     --
-- time spent in each mode and the total time (`Matrix.Boxes` over    --
-- the intervals with `∞`): sequencing adds the intervals,            --
-- the join takes hulls, and the order is inclusion. A box is         --
-- realisable when some summary of a trace fits it: a time in each    --
-- mode, finitely many of them nonzero, each in the interval of its   --
-- mode, whose sum is in the total (`Realisable`, the summary a       --
-- `Witness`). So the interval of the modes not named contains `0`,   --
-- all but finitely many modes being left at once. Realisable boxes   --
-- are closed under the unit, sums, hulls, renaming and orbit joins,  --
-- and "no trace" is realisable, so they form an equivariant          --
-- sub-dioid (`times`), the entries of the mode-time matrices.        --
------------------------------------------------------------------------

module Grades.Examples.SemiDirect.ModeTimes.Boxes where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_) renaming (map to mapᴸ)
open import Data.Nat.ListAction using (sum)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to 𝟙ᵗ)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.Time.Interval
open import Grades.Matrix.Dioid using (Dioid)
open import Grades.Matrix.Modes ℕ-names using (Name; _≟ᴺ_; swap; swap-inv; swap-injective)
import Grades.Matrix.Boxes
import Grades.Matrix.Restrict
import Grades.Matrix.Nominal

open import Util.Equality

open Maps ℕ-names using (Map; _∣_; _!_; others; named; lookup; everywhere; map₂; !-map₂;
                         pointwise⁻; pointwise⁺)

module B = Grades.Matrix.Boxes ℕ-names intervals
open B public using (Box; boxes; equivariant-boxes; rename; rename-!; orbit; orbit-∈; orbit-∉)

------------------------------------------------------------------------
-- Exact times in intervals

infix 4 _∈ᵢ_

_∈ᵢ_ : ℕ → Interval∞ → Set
n ∈ᵢ i = (min i ≤ n) × (↑ n ≤∞ max i)

∈ᵢ-· : ∀ {n n' i i'} → n ∈ᵢ i → n' ∈ᵢ i' → n + n' ∈ᵢ i ·ᵢ i'
∈ᵢ-· {n} {n'} {i} {i'} (a , b) (a' , b') =
  ℕₚ.+-mono-≤ a a' , +∞-mono-≤∞ {↑ n} {↑ n'} {max i} {max i'} b b'

∈ᵢ-≾ : ∀ {n i j} → i ≾ᵢ j → n ∈ᵢ i → n ∈ᵢ j
∈ᵢ-≾ {n} {i} {j} (lo , hi) (a , b) = ℕₚ.≤-trans lo a , ≤∞-trans {↑ n} {max i} {max j} b hi

0∈𝟏ᵢ : 0 ∈ᵢ 𝟏ᵢ
0∈𝟏ᵢ = z≤n , z≤n

------------------------------------------------------------------------
-- Summaries of traces: finitely many modes with their times

Entries : Set
Entries = List (Name × ℕ)

keys : Entries → List Name
keys = mapᴸ proj₁

-- each mode listed once
Distinct : Entries → Set
Distinct []             = 𝟙ᵗ
Distinct ((s , _) ∷ es) = (s ∉ keys es) × Distinct es

record Witness : Set where
  constructor witness
  field
    entries  : Entries
    distinct : Distinct entries

open Witness public

time : Entries → Name → ℕ
time = lookup 0

total-time : Entries → ℕ
total-time es = sum (mapᴸ proj₂ es)

-- a summary fits a box when each time is in its interval and the sum
-- in the total

Fits : Witness → Map Interval∞ → Interval∞ → Set
Fits w m t = (∀ s → time (entries w) s ∈ᵢ m ! s) × (total-time (entries w) ∈ᵢ t)

Realisable : Map Interval∞ → Interval∞ → Set
Realisable m t = ∃ λ w → Fits w m t

------------------------------------------------------------------------
-- Removing a mode, and merging two summaries

private
  time-∉ : ∀ es s → s ∉ keys es → time es s ≡ 0
  time-∉ []              s _ = refl
  time-∉ ((s' , n) ∷ es) s p with s ≟ᴺ s'
  ... | yes e = ⊥-elim (p (here e))
  ... | no _  = time-∉ es s (λ q → p (there q))

remove : Name → Entries → Entries
remove s []              = []
remove s ((s' , n) ∷ es) with s ≟ᴺ s'
... | yes _ = remove s es
... | no _  = (s' , n) ∷ remove s es

private
  remove-keys : ∀ s es {r} → r ∈ keys (remove s es) → r ∈ keys es
  remove-keys s ((s' , n) ∷ es) r∈ with s ≟ᴺ s'
  ... | yes _ = there (remove-keys s es r∈)
  remove-keys s ((s' , n) ∷ es) (here e)  | no _ = here e
  remove-keys s ((s' , n) ∷ es) (there q) | no _ = there (remove-keys s es q)

  remove-gone : ∀ s es → s ∉ keys (remove s es)
  remove-gone s []              ()
  remove-gone s ((s' , n) ∷ es) r∈ with s ≟ᴺ s'
  ... | yes _ = remove-gone s es r∈
  remove-gone s ((s' , n) ∷ es) (here e)  | no ne = ne e
  remove-gone s ((s' , n) ∷ es) (there q) | no _  = remove-gone s es q

  remove-distinct : ∀ s es → Distinct es → Distinct (remove s es)
  remove-distinct s []              _       = tt
  remove-distinct s ((s' , n) ∷ es) (p , d) with s ≟ᴺ s'
  ... | yes _ = remove-distinct s es d
  ... | no _  = (λ q → p (remove-keys s es q)) , remove-distinct s es d

  remove-time : ∀ s es r → ¬ r ≡ s → time (remove s es) r ≡ time es r
  remove-time s []              r ne = refl
  remove-time s ((s' , n) ∷ es) r ne with s ≟ᴺ s'
  ... | yes refl with r ≟ᴺ s
  ...   | yes e = ⊥-elim (ne e)
  ...   | no _  = remove-time s es r ne
  remove-time s ((s' , n) ∷ es) r ne | no _ with r ≟ᴺ s'
  ...   | yes _ = refl
  ...   | no _  = remove-time s es r ne

  remove-time-s : ∀ s es → time (remove s es) s ≡ 0
  remove-time-s s es = time-∉ (remove s es) s (remove-gone s es)

  -- with each mode listed once, a mode's time is taken out by removing it
  remove-total-time : ∀ s es → Distinct es → total-time es ≡ time es s + total-time (remove s es)
  remove-total-time s []              _       = refl
  remove-total-time s ((s' , n) ∷ es) (p , d) with s ≟ᴺ s'
  ... | yes refl = cong (n +_) (trans (sym (time-∉-remove es p)) refl)
    where
      -- `s` is not listed in `es`, so removing it changes nothing
      time-∉-remove : ∀ es → s ∉ keys es → total-time (remove s es) ≡ total-time es
      time-∉-remove []              _ = refl
      time-∉-remove ((r , m) ∷ es) q with s ≟ᴺ r
      ... | yes e = ⊥-elim (q (here e))
      ... | no _  = cong (m +_) (time-∉-remove es (λ x → q (there x)))
  ... | no ne =
    trans (cong (n +_) (remove-total-time s es d))
      (trans (sym (ℕₚ.+-assoc n (time es s) _))
        (trans (cong (_+ total-time (remove s es)) (ℕₚ.+-comm n (time es s)))
               (ℕₚ.+-assoc (time es s) n _)))

merge : Entries → Entries → Entries
merge []             es' = es'
merge ((s , n) ∷ es) es' = (s , n + time es' s) ∷ merge es (remove s es')

private
  merge-keys : ∀ es es' {r} → r ∈ keys (merge es es') → (r ∈ keys es) ⊎ (r ∈ keys es')
  merge-keys []             es' r∈        = inj₂ r∈
  merge-keys ((s , n) ∷ es) es' (here e)  = inj₁ (here e)
  merge-keys ((s , n) ∷ es) es' (there q) with merge-keys es (remove s es') q
  ... | inj₁ r∈ = inj₁ (there r∈)
  ... | inj₂ r∈ = inj₂ (remove-keys s es' r∈)

  merge-distinct : ∀ es es' → Distinct es → Distinct es' → Distinct (merge es es')
  merge-distinct []             es' _       d' = d'
  merge-distinct ((s , n) ∷ es) es' (p , d) d' =
    (λ q → case (merge-keys es (remove s es') q)) ,
    merge-distinct es (remove s es') d (remove-distinct s es' d')
    where
      case : (s ∈ keys es) ⊎ (s ∈ keys (remove s es')) → _
      case (inj₁ s∈) = p s∈
      case (inj₂ s∈) = remove-gone s es' s∈

  merge-time : ∀ es es' r → Distinct es → time (merge es es') r ≡ time es r + time es' r
  merge-time []             es' r _ = refl
  merge-time ((s , n) ∷ es) es' r (p , d) with r ≟ᴺ s
  ... | yes refl = refl
  ... | no ne = trans (merge-time es (remove s es') r d) (cong (time es r +_) (remove-time s es' r ne))

  merge-total-time : ∀ es es' → Distinct es' → total-time (merge es es') ≡ total-time es + total-time es'
  merge-total-time []             es' _  = refl
  merge-total-time ((s , n) ∷ es) es' d' =
    trans (cong ((n + time es' s) +_) (merge-total-time es (remove s es') (remove-distinct s es' d')))
      (trans (ℕₚ.+-assoc n (time es' s) _)
        (trans (cong (n +_) (trans (sym (ℕₚ.+-assoc (time es' s) (total-time es) _))
                              (trans (cong (_+ total-time (remove s es')) (ℕₚ.+-comm (time es' s) (total-time es)))
                                     (ℕₚ.+-assoc (total-time es) (time es' s) _))))
          (trans (sym (ℕₚ.+-assoc n (total-time es) _))
                 (cong (n + total-time es +_) (sym (remove-total-time s es' d'))))))

------------------------------------------------------------------------
-- Renaming a summary

renameᵉ : (Name → Name) → Entries → Entries
renameᵉ σ = mapᴸ (λ (s , n) → σ s , n)

private
  rename-time : ∀ a b es r → time (renameᵉ (swap a b) es) r ≡ time es (swap a b r)
  rename-time a b []              r = refl
  rename-time a b ((s , n) ∷ es) r with r ≟ᴺ swap a b s | swap a b r ≟ᴺ s
  ... | yes _  | yes _ = refl
  ... | yes e  | no ne = ⊥-elim (ne (trans (cong (swap a b) e) (swap-inv a b s)))
  ... | no ne  | yes e = ⊥-elim (ne (trans (sym (swap-inv a b r)) (cong (swap a b) e)))
  ... | no _   | no _  = rename-time a b es r

  rename-keys : ∀ a b es {r} → r ∈ keys (renameᵉ (swap a b) es) → swap a b r ∈ keys es
  rename-keys a b ((s , n) ∷ es) (here refl) = here (swap-inv a b s)
  rename-keys a b ((s , n) ∷ es) (there q)   = there (rename-keys a b es q)

  rename-distinct : ∀ a b es → Distinct es → Distinct (renameᵉ (swap a b) es)
  rename-distinct a b []              _       = tt
  rename-distinct a b ((s , n) ∷ es) (p , d) =
    (λ q → p (subst (_∈ keys es) (swap-inv a b s) (rename-keys a b es q))) , rename-distinct a b es d

  rename-total-time : ∀ σ es → total-time (renameᵉ σ es) ≡ total-time es
  rename-total-time σ []             = refl
  rename-total-time σ ((s , n) ∷ es) = cong (n +_) (rename-total-time σ es)

------------------------------------------------------------------------
-- The realisable entries

open Dioid boxes using () renaming (Carrier to Entry; _≤_ to _≤ᵇ_)

RealisableEntry : Entry → Set
RealisableEntry nothing        = 𝟙ᵗ
RealisableEntry (just (m , t)) = Realisable m t

private
  open Grade intervals using () renaming (_≾_ to _≾ⁱ_)

  up-just : ∀ {m t m' t'} → just (m , t) ≤ᵇ just (m' , t') → Realisable m t → Realisable m' t'
  up-just {m} {t} {m'} {t'} (p , q) (w , fit , tot) =
    w , (λ s → ∈ᵢ-≾ {i = m ! s} {j = m' ! s} (pointwise⁻ _≾ⁱ_ p s) (fit s)) , ∈ᵢ-≾ {i = t} {j = t'} q tot

  realisable-⊗ : ∀ {m t m' t'} → Realisable m t → Realisable m' t' → Realisable (map₂ _·ᵢ_ m m') (t ·ᵢ t')
  realisable-⊗ {m} {t} {m'} {t'} (witness es d , fit , tot) (witness es' d' , fit' , tot') =
    witness (merge es es') (merge-distinct es es' d d') ,
    (λ s → subst₂ _∈ᵢ_ (sym (merge-time es es' s d)) (sym (!-map₂ _·ᵢ_ m m' s)) (∈ᵢ-· {i = m ! s} {i' = m' ! s} (fit s) (fit' s))) ,
    subst (_∈ᵢ t ·ᵢ t') (sym (merge-total-time es es' d')) (∈ᵢ-· {i = t} {i' = t'} tot tot')

closed : Grades.Matrix.Restrict.Closed ℕ-names equivariant-boxes RealisableEntry
closed = record
  { P-𝟘     = tt
  ; P-𝟙     = witness [] tt , (λ s → 0∈𝟏ᵢ) , 0∈𝟏ᵢ
  ; P-⊤     = witness [] tt , (λ s → z≤n , tt) , (z≤n , tt)
  ; P-⊕     = λ { {nothing} {y} _ q → subst-⊕ y q
                ; {just b} {nothing} p _ → p
                ; {just (m , t)} {just (m' , t')} p _ →
                    up-just {m} {t} {map₂ _⊔ᵢ_ m m'} {t ⊔ᵢ t'} (Dioid.⊕-ubˡ boxes (just (m , t)) (just (m' , t'))) p }
  ; P-⊗     = λ { {nothing} _ _ → tt
                ; {just _} {nothing} _ _ → tt
                ; {just (m , t)} {just (m' , t')} p q → realisable-⊗ {m} {t} {m'} {t'} p q }
  ; P-act   = λ { {x = nothing} _ → tt
                ; {a} {b} {just (m , t)} (witness es d , fit , tot) →
                    witness (renameᵉ (swap a b) es) (rename-distinct a b es d) ,
                    (λ s → subst₂ _∈ᵢ_ (sym (rename-time a b es s)) (sym (rename-! a b m s)) (fit (swap a b s))) ,
                    subst (_∈ᵢ t) (sym (rename-total-time (swap a b) es)) tot }
  ; P-orbit = λ { {A} {nothing} _ → tt
                ; {A} {just (m , t)} p →
                    up-just {m} {t} {orbit A m} {t} (⟨⟩-ub {A} (just (m , t))) p }
  }
  where
    open Grades.Matrix.Nominal.Equivariant equivariant-boxes using (⟨⟩-ub)
    subst-⊕ : ∀ y → RealisableEntry y → RealisableEntry (Dioid._⊕_ boxes nothing y)
    subst-⊕ y q = q

-- the entries of the mode-time matrices

times : Dioid
times = Grades.Matrix.Restrict.restricted ℕ-names equivariant-boxes closed

equivariant-times : Grades.Matrix.Nominal.Equivariant ℕ-names times
equivariant-times = Grades.Matrix.Restrict.restricted-equivariant ℕ-names equivariant-boxes closed
