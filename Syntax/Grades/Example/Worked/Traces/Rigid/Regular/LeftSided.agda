------------------------------------------------------------------------
-- Worked rigid timed regular lower bounds, in whole steps.           --
--                                                                    --
-- A guarantee fixes the skeleton of a run: activity before, between  --
-- and after its letters only where a stretch admits it (`≥ 0`, the   --
-- flank), and a strict wait demands an undisturbed wait. Operations  --
-- count inside a budget at their running time; the stirs below take  --
-- at least three steps each.                                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Regular.LeftSided where

open import Data.Bool.Base using (T)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Nullary using (¬_)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)
open import Syntax.Durations.Intervals ℕᵀ using (⟪_,_⟫; fin; ⁻; ⁺; _⊑?_; 0⁺; lo)
  renaming (_∣_ to _∣ᶜ_)
open import Syntax.Grades.Traces.RunningTimes ℕᵀ using (RunningTimes; Bounded)
open import Syntax.Durations.Intervals.Dense ℕᵀ using (_∈ⁱ?_)
open import Data.Product using (_,_)
open import Relation.Nullary.Decidable using (toWitness)

data Op : Set where
  open′ close′ stir : Op

code : Op → Fin 3
code open′ = zero
code close′ = suc zero
code stir  = suc (suc zero)

name : Fin 3 → Op
name zero             = open′
name (suc zero)       = close′
name (suc (suc zero)) = stir

name-code : ∀ o → name (code o) ≡ o
name-code open′ = refl
name-code close′ = refl
name-code stir  = refl

code-name : ∀ c → code (name c) ≡ c
code-name zero             = refl
code-name (suc zero)       = refl
code-name (suc (suc zero)) = refl

running : RunningTimes Op
running = record
  { rt          = λ { open′ → ⟪ 1 ∣ᶜ ⁻ , fin (1 ∣ᶜ ⁺) ⟫ ; close′ → ⟪ 1 ∣ᶜ ⁻ , fin (1 ∣ᶜ ⁺) ⟫
                    ; stir → ⟪ 3 ∣ᶜ ⁻ , fin (4 ∣ᶜ ⁺) ⟫ }
  ; rt-bounded  = λ { open′ → Bounded.fin (1 ∣ᶜ ⁺) ; close′ → Bounded.fin (1 ∣ᶜ ⁺) ; stir → Bounded.fin (4 ∣ᶜ ⁺) }
  ; rt-positive = λ { open′ → toWitness {a? = 0⁺ ⊑? (1 ∣ᶜ ⁻)} _
                    ; close′ → toWitness {a? = 0⁺ ⊑? (1 ∣ᶜ ⁻)} _
                    ; stir  → toWitness {a? = 0⁺ ⊑? (3 ∣ᶜ ⁻)} _ }
  ; rt-inhabited = λ { open′  → 1 , toWitness {a? = 1 ∈ⁱ? ⟪ 1 ∣ᶜ ⁻ , fin (1 ∣ᶜ ⁺) ⟫} _
                     ; close′ → 1 , toWitness {a? = 1 ∈ⁱ? ⟪ 1 ∣ᶜ ⁻ , fin (1 ∣ᶜ ⁺) ⟫} _
                     ; stir   → 3 , toWitness {a? = 3 ∈ⁱ? ⟪ 3 ∣ᶜ ⁻ , fin (4 ∣ᶜ ⁺) ⟫} _ }
  }

open import Syntax.Grades.Example.Traces.Rigid.Regular.LeftSided Op 3 code name name-code code-name running

‵ᵍ_ : Op → Closed
‵ᵍ open′ = ⌜ ‵_ {lower} open′ ⌝
‵ᵍ close′ = ⌜ ‵_ {lower} close′ ⌝
‵ᵍ stir  = ⌜ ‵_ {lower} stir ⌝

infix 9 ‵ᵍ_

_·ᵍ_ : Closed → Closed → Closed
_·ᵍ_ = C._·_

infixl 7 _·ᵍ_

------------------------------------------------------------------------
-- The guarantees and runs compared below

settle settle-busy one-wait one-then-wait wait-1 wait-5 budget-5
  settled-run stirred-run interrupted-run open-then-stir anything twice : Closed
settle          = ⌜ ≥ 0 · ‵ open′ · idle ≥ 5 · ‵ close′ · ≥ 0 ⌝
settle-busy     = ⌜ ≥ 0 · ‵ open′ · ≥ 5 · ‵ close′ · ≥ 0 ⌝
one-wait        = ⌜ ≥ 1 · idle ≥ 2 ⌝
one-then-wait   = ⌜ ≥ 1 · idle ≥ 1 ⌝
wait-1          = ⌜ idle ≥ 1 ⌝
wait-5          = ⌜ idle ≥ 5 ⌝
budget-5        = ⌜ ≥ 5 ⌝
settled-run     = ‵ᵍ open′ ·ᵍ of-dur 5 ·ᵍ ‵ᵍ close′
stirred-run     = ‵ᵍ open′ ·ᵍ ‵ᵍ stir ·ᵍ ‵ᵍ stir ·ᵍ ‵ᵍ close′
interrupted-run = ‵ᵍ open′ ·ᵍ of-dur 2 ·ᵍ ‵ᵍ stir ·ᵍ of-dur 3 ·ᵍ ‵ᵍ close′
open-then-stir  = ‵ᵍ open′ ·ᵍ ‵ᵍ stir
anything        = ⌜ ≥ 0 ⌝
twice           = one-then-wait ·ᵍ one-then-wait

------------------------------------------------------------------------
-- The prototype's test (`strict_delays_lower_reject.tpe`): a strict
-- wait demands an undisturbed wait, which operations do not give,
-- while a budget counts them

settled : C._≾_ settled-run settle
settled = holds settled-run settle refl

stirred : ¬ C._≾_ stirred-run settle
stirred = fails stirred-run settle refl

stirred-budget : C._≾_ stirred-run settle-busy
stirred-budget = holds stirred-run settle-busy refl

-- an operation inside the wait leaves two waits, of two and three
-- steps, neither of five

interrupted : ¬ C._≾_ interrupted-run settle
interrupted = fails interrupted-run settle refl

------------------------------------------------------------------------
-- The kinds of stretch

strict-below-budget : C._≾_ wait-5 budget-5
strict-below-budget = holds wait-5 budget-5 refl

budget-not-below-strict : ¬ C._≾_ budget-5 wait-5
budget-not-below-strict = fails budget-5 wait-5 refl

------------------------------------------------------------------------
-- F4: the flanks are explicit, so a budget of one before a wait of one
-- does not fit a wait of one alone; and a run of two such fits no
-- budget of one before a wait of two

no-implicit-flank : ¬ C._≾_ one-then-wait wait-1
no-implicit-flank = fails one-then-wait wait-1 refl

twice-not-below : ¬ C._≾_ twice one-wait
twice-not-below = fails twice one-wait refl

------------------------------------------------------------------------
-- The flank admitting anything lies above every run; the empty word
-- does not

open-then-stir-anything : C._≾_ open-then-stir anything
open-then-stir-anything = holds open-then-stir anything refl

not-nothing : ¬ C._≾_ open-then-stir C.u
not-nothing = fails open-then-stir C.u refl

------------------------------------------------------------------------
-- A strict wait is made only from a budget letter: `idle ‵ stir` is
-- refused

stir-not-budget : ¬ T (budget? (‵_ {lower} stir))
stir-not-budget ()
