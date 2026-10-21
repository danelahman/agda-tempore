------------------------------------------------------------------------
-- Rigid timed regular grades in whole steps, as intervals.           --
--                                                                    --
-- A grade `[ L , U ]` pairs a lower bound with an upper bound that   --
-- are consistent: some letter word lies in both closed languages,    --
-- the encoding of an exact run fitting a word of each. Consistency   --
-- is closed upward and holds of the empty word and of every delay;   --
-- words concatenate. So consistent pairs are a sub-grade of the      --
-- product of the two grades (`Grades.Upward`), compared              --
-- componentwise, the word being data the order ignores. A delay      --
-- advances both components.                                          --
--                                                                    --
-- Consistency is decided: the two tables meet when the search of     --
-- their pairs of states reachable together finds a pair of final     --
-- states (`Regular.Meet`). A literal `[ L , U ]` checks it, the word --
-- the search finds witnessing it; `[ L , U ]⟨ r ⟩` names the run     --
-- instead, a sequence of operations and delays whose encoding the    --
-- two automata accept.                                               --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᴰ; ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Regular.TwoSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

import Data.Fin.Subset
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.Nat.Base using (zero; suc)
import Data.Nat.Base
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True; toWitness; map′)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)
open import Syntax.Grades.Upward using (Upward; _∣ᵍ_)
open import Syntax.Durations.Intervals ℕᵀ using (fin; ⁻; ⁺; ≤⇒⁻⊑⁻; ≤⇒⁺⊑⁺) renaming (_∣_ to _∣ᶜ_)

import Syntax.Grades.Example.Traces.Rigid.Regular.LeftSided Op n code name name-code code-name running as L
import Syntax.Grades.Example.Traces.Rigid.Regular.RightSided Op n code name name-code code-name running as U

open L public using (Closed; Lower; !≥_; !>_; ≥_; >_)
open U public using (Upper; !≤_; !<_; ≤_; <_; ≤∞)

open L using (lang; k; tick; encᶠ; ⌜_⌝′; ∈-⌜⌝′⁺; ≤ᶠ-refl; str; lower; upper; ‵_;
              steps; Word; Expr; op; ![_]; stretch; ⟦_⟧)
import Syntax.Grades.Regular.Automaton k as A
open import Syntax.Grades.Regular.Grade k tick using (table; wf′; ∈·⁺; ∈u⁺; ≾⇒⊆)
open import Syntax.Grades.Regular.Meet k using (meet?)
open L.C using (≾-lang)

private
  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {o} {o′} e = trans (sym (name-code o)) (trans (cong name e) (name-code o′))

open import Syntax.Grades.Exact.Hull ℕᵀ Op n code code-injective running
  using (Run; perform; delay) public
open RunningTimes.RunningTimes running using (rt-inhabited⁺)

------------------------------------------------------------------------
-- Consistency

-- membership of a word in the language of a table, kept from reducing:
-- a type of it is never evaluated to decide whether it is a unit

record Mem (D : A.DFA) (w : List (Fin k)) : Set where
  no-eta-equality
  constructor mem
  field get : w A.∈ D

open Mem

Consistent : Closed × Closed → Set
Consistent (l , u) = Σ[ w ∈ List (Fin k) ] Mem (table (lang l)) w × Mem (table (lang u)) w

-- consistency, decided

consistent? : ∀ lu → Dec (Consistent lu)
consistent? (l , u) =
  map′ (λ (w , wl , wu) → w , mem wl , mem wu) (λ (w , wl , wu) → w , get wl , get wu)
       (meet? {table (lang l)} {table (lang u)} (wf′ (lang l)) (wf′ (lang u)))

private
  below-refl : ∀ w → L.Belowᶠ w w
  below-refl []      = Pointwise.[]
  below-refl (a ∷ w) = ≤ᶠ-refl a Pointwise.∷ below-refl w

  -- the one-step delays, written out as the literals they are
  e≥ : Lower
  e≥ = str Data.Fin.Subset.⊥ (1 ∣ᶜ ⁻)

  e≤ : Upper
  e≤ = str Data.Fin.Subset.⊥ (fin (1 ∣ᶜ ⁺))

  i≥ : ∃ ⟦ e≥ ⟧
  i≥ = stretch Data.Fin.Subset.⊥ 1 , 1 , ≤⇒⁻⊑⁻ ℕ.≤-refl , refl

  i≤ : ∃ ⟦ e≤ ⟧
  i≤ = [] , 0 , ≤⇒⁺⊑⁺ Data.Nat.Base.z≤n , refl

  -- a word of an expression lies in its literal
  lit-∈ : ∀ {s} (e : L.Expr s) (i : ∃ ⟦ e ⟧) x → ⟦ e ⟧ x → Mem (table (lang (⌜ e ⌝′ i))) (encᶠ x)
  lit-∈ e i x x∈ = mem (∈-⌜⌝′⁺ e {i} (encᶠ x) (x , x∈ , below-refl (encᶠ x)))

  -- a step of waiting lies in both one-step delays
  step-≥ : Mem (table (lang (⌜ e≥ ⌝′ i≥))) (encᶠ (stretch Data.Fin.Subset.⊥ 1))
  step-≥ = lit-∈ e≥ i≥ (stretch Data.Fin.Subset.⊥ 1) (1 , ≤⇒⁻⊑⁻ ℕ.≤-refl , refl)

  step-≤ : Mem (table (lang (⌜ e≤ ⌝′ i≤))) (encᶠ (stretch Data.Fin.Subset.⊥ 1))
  step-≤ = lit-∈ e≤ i≤ (stretch Data.Fin.Subset.⊥ 1) (1 , ≤⇒⁺⊑⁺ ℕ.≤-refl , refl)

  steps-word : List (Fin k) → ℕ → List (Fin k)
  steps-word v zero    = []
  steps-word v (suc m) = v ++ steps-word v m

  steps-∈ : ∀ w v → Mem (table (lang w)) v → ∀ m → Mem (table (lang (steps w m))) (steps-word v m)
  steps-∈ w v s zero    = mem ∈u⁺
  steps-∈ w v s (suc m) =
    mem (∈·⁺ (lang w) (lang (steps w m)) v (steps-word v m) (get s) (get (steps-∈ w v s m)))

  -- the two grades, their delays the products of the literals above
  left-sided right-sided : Grade ℕᴰ
  left-sided  = L.C.WithDurations.closed-grade (steps (⌜ e≥ ⌝′ i≥)) refl
                  (λ {m} {n} → L.steps-plus (⌜ e≥ ⌝′ i≥) {m} {n})
  right-sided = L.C.WithDurations.closed-grade (steps (⌜ e≤ ⌝′ i≤)) refl
                  (λ {m} {n} → L.steps-plus (⌜ e≤ ⌝′ i≤) {m} {n})

consistent : Upward (left-sided ×ᵍ right-sided) Consistent
consistent = record
  { up       = λ {(l , u)} {(l′ , u′)} (p , q) (w , wl , wu) →
      w , mem (≾⇒⊆ (lang l) (lang l′) (≾-lang p) w (get wl)) ,
          mem (≾⇒⊆ (lang u) (lang u′) (≾-lang q) w (get wu))
  ; P-u      = [] , mem ∈u⁺ , mem ∈u⁺
  ; P-·      = λ {(l , u)} {(l′ , u′)} (w , wl , wu) (w′ , wl′ , wu′) →
      w ++ w′ , mem (∈·⁺ (lang l) (lang l′) w w′ (get wl) (get wl′)) ,
                mem (∈·⁺ (lang u) (lang u′) w w′ (get wu) (get wu′))
  ; P-of-dur = λ m → steps-word (encᶠ (stretch Data.Fin.Subset.⊥ 1)) m ,
                     steps-∈ (⌜ e≥ ⌝′ i≥) _ step-≥ m , steps-∈ (⌜ e≤ ⌝′ i≤) _ step-≤ m
  }

two-sided : Grade ℕᴰ
two-sided = (left-sided ×ᵍ right-sided) ∣ᵍ consistent

------------------------------------------------------------------------
-- Literals

-- a run of a sequence of operations and delays, each operation running
-- for a time it admits

word : Run → Word
word []              = []
word (perform o ∷ r) = op o (proj₁ (rt-inhabited⁺ o)) ∷ word r
word (delay τ ∷ r)   = ![ τ ] ++ word r

-- a pair of literals, decided consistent

[_,_] : (l u : Closed) → {c : True (consistent? (l , u))} → Grade.Carrier two-sided
[ l , u ] {c} = (l , u) , toWitness c

-- a pair of literals, consistent by the run `r`, the two memberships
-- found by running the automata

[_,_]⟨_⟩ : (l u : Closed) (r : Run)
         → {pl : encᶠ (word r) A.∈ table (lang l)} {pu : encᶠ (word r) A.∈ table (lang u)}
         → Grade.Carrier two-sided
[ l , u ]⟨ r ⟩ {pl} {pu} = (l , u) , encᶠ (word r) , mem pl , mem pu

-- an operation, at both endpoints

private
  iₒ : ∀ o → ∃ ⟦ ‵_ {upper} o ⟧
  iₒ o = op o (proj₁ (rt-inhabited⁺ o)) ∷ [] ,
         o , proj₁ (rt-inhabited⁺ o) , x∈⁅x⁆ (code o) , proj₂ (rt-inhabited⁺ o) , refl

‵ᵍ : Op → Closed
‵ᵍ o = ⌜ ‵_ {upper} o ⌝′ (iₒ o)

operation : Op → Grade.Carrier two-sided
operation o =
  (‵ᵍ o , ‵ᵍ o) , encᶠ (proj₁ (iₒ o)) ,
  lit-∈ (‵_ {upper} o) (iₒ o) (proj₁ (iₒ o)) (proj₂ (iₒ o)) ,
  lit-∈ (‵_ {upper} o) (iₒ o) (proj₁ (iₒ o)) (proj₂ (iₒ o))
