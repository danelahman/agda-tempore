------------------------------------------------------------------
-- Solver stages on hand-written constraints                    --
--                                                              --
-- Each test applies one stage of the solver to a hypothesis    --
-- set, a pair of grade expressions or a residual written out   --
-- by hand, and checks its answer by `refl`. The stages tested: --
--   * `canonᴴ`: an ordering with a join on its left is one     --
--     ordering per alternative. No example program depends on  --
--     it.                                                      --
--   * `walkᵈ`: a var-rule disjunction entailed by another is   --
--     pruned (also `Reports`).                                 --
--   * `canonᵣ`/`canonₑ`: a product with the top is the top     --
--     where the unit is least (also `Reports`).                --
--   * `decideᵣ`/`decideₑ` at `derive`: products compare as     --
--     multisets where `·` commutes. No example program depends --
--     on it.                                                   --
--   * `decideᵣ`/`decideₑ` at `full`: chains through compound   --
--     sides, a chain from the left side to a vertex below the  --
--     right side, and factor edges, with the evidence of the   --
--     unit below a co-factor reached from a constant above it. --
--   * `checkClosed`: closed sides joined by a chain of         --
--     orderings are compared (also `Boxes`); a disjunction     --
--     whose grade is below the unit from the orderings left is --
--     dropped.                                                 --
--   * `collapse`: a cycle of unknowns local to a clause is one --
--     unknown; without it, the clause's close is stuck.        --
--   * `retry`: a deferred condition is refuted at a candidate  --
--     value the grade supplies for its rigid.                  --
--   * `stepᵉ`, lowering: the value `B* · L · C*`, and its      --
--     closure, at each shape of cycle, with and without lower  --
--     bounds; the annotated `wait` of the prototype is refuted --
--     at the value.                                            --
--                                                              --
-- The grades differ in the properties the stages read,         --
-- `u-least?` and `·-comm?`: right-sided intervals (both hold), --
-- timed traces under the allowance order (the unit least, `·`  --
-- not commutative), left-sided intervals with an adjoined top  --
-- (`·` commutative, the unit not least, the top distinct from  --
-- the unit), both sides of time for the collapse, left-sided   --
-- time for the retry, and right-sided time and two-sided       --
-- intervals for lowering.                                      --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false; not; _∧_) renaming (Bool to 𝔹)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing; is-just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (does)

open import Util.Equality

open import Grades.Base
open import Language.Spec
import Grades.Examples.Worked.Operations.Grading as Grading

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.Outcome using (Outcome; stuck)
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Examples.Stages where

------------------------------------------------------------------
-- Right-sided intervals: the unit least, `·` commutative

module Deadline where

  open import Grades.Examples.Time.RightSided using ([0,_]; ↑_)
  open import OpenCalculus.Examples.Specs using (module Time-RightSided)
  open Time-RightSided using (spec)
  open LanguageSpec spec using (Grades)
  open GradeSystemInterface Grades using (⊤ᵣ; ⊤ₑ)

  open import OpenCalculus.Syntax.Grades                 spec
  open import OpenCalculus.Syntax.Types                  spec using (OVType; tvar)
  open import OpenCalculus.Hypotheses                    spec using (hyps; ∅ᴴ; ordᵣ; ordₑ; disj)
  open import OpenCalculus.Inference.SolverImpl.Canon    spec using (canonᴴ; canonᵣ; canonₑ)
  open import OpenCalculus.Inference.SolverImpl.Simplify spec using (walkᵈ)
  open import OpenCalculus.Inference.SolverImpl.Entail   spec
    using (decideₑ; decideᵣ; derive; full; checkClosed)

  Θ : Scope
  Θ = scope 1 4 4

  x y z w : RExp Θ
  x = rvar zero
  y = rvar (suc zero)
  z = rvar (suc (suc zero))
  w = rvar (suc (suc (suc zero)))

  a b c d : EExp Θ
  a = evar zero
  b = evar (suc zero)
  c = evar (suc (suc zero))
  d = evar (suc (suc (suc zero)))

  α : OVType Θ
  α = tvar zero

  ⌜_⌝ʳ : ℕ → RExp Θ
  ⌜ n ⌝ʳ = rconst [0, ↑ n ]

  ⌜_⌝ᵉ : ℕ → EExp Θ
  ⌜ n ⌝ᵉ = econst [0, ↑ n ]

  ----------------------------------------------------------------
  -- `canonᴴ`: an ordering with a join on its left is one
  -- ordering per alternative; a join on the right is kept

  split-left-r :
    ordᵣ (canonᴴ (hyps [] [] ((x ⊔̂ᵣ y , z) ∷ (z , x ⊔̂ᵣ y) ∷ []) [] [] []))
      ≡ (x , z) ∷ (y , z) ∷ (z , x ⊔̂ᵣ y) ∷ []
  split-left-r = refl

  split-left-e :
    ordₑ (canonᴴ (hyps [] [] [] ((a ⊔̂ₑ b , c) ∷ (c , a ⊔̂ₑ b) ∷ []) [] []))
      ≡ (a , c) ∷ (b , c) ∷ (c , a ⊔̂ₑ b) ∷ []
  split-left-e = refl

  ----------------------------------------------------------------
  -- `walkᵈ`: with `x ≾ y`, `eternal α ∨ y ≾ uᵣ` entails
  -- `eternal α ∨ x ≾ uᵣ`, which is pruned, as is the repeat

  prune-entailed :
    disj (walkᵈ (hyps [] [] ((x , y) ∷ []) []
                      ((α , x) ∷ (α , y) ∷ (α , y) ∷ (α , x ⊔̂ᵣ z) ∷ []) []))
      ≡ (α , y) ∷ (α , x ⊔̂ᵣ z) ∷ []
  prune-entailed = refl

  ----------------------------------------------------------------
  -- `canonᵣ`/`canonₑ`: a product with the top among its
  -- factors is the top, which absorbs the join

  top-product-r : canonᵣ (x ·̂ᵣ rconst ⊤ᵣ) ≡ rconst ⊤ᵣ
  top-product-r = refl

  top-product-e : canonₑ (a ·̂ₑ econst ⊤ₑ) ≡ econst ⊤ₑ
  top-product-e = refl

  top-product-join : canonᵣ (x ·̂ᵣ rconst ⊤ᵣ ⊔̂ᵣ y) ≡ rconst ⊤ᵣ
  top-product-join = refl

  ----------------------------------------------------------------
  -- `decideₑ`/`decideᵣ` at `derive`: products compare as multisets,
  -- matching the factors crosswise

  -- c ≾ b, d ≾ a ⊩ c · d ≾ a · b

  crossed-e :
    is-just (decideₑ derive (hyps [] [] [] ((c , b) ∷ (d , a) ∷ []) [] []) (c ·̂ₑ d) (a ·̂ₑ b))
      ≡ true
  crossed-e = refl

  crossed-e-∅ : is-just (decideₑ derive ∅ᴴ (c ·̂ₑ d) (a ·̂ₑ b)) ≡ false
  crossed-e-∅ = refl

  -- z ≾ y, w ≾ x ⊩ z · w ≾ x · y

  crossed-r :
    is-just (decideᵣ derive (hyps [] [] ((z , y) ∷ (w , x) ∷ []) [] [] []) (z ·̂ᵣ w) (x ·̂ᵣ y))
      ≡ true
  crossed-r = refl

  -- with images of effect variables: z ≾ ∣a∣, ∣b∣ ≾ x ⊩ z · ∣b∣ ≾ x · ∣a∣

  crossed-images :
    is-just (decideᵣ derive (hyps [] [] ((z , ∣ a ∣̂ᵉ) ∷ (∣ b ∣̂ᵉ , x) ∷ []) [] [] [])
                      (z ·̂ᵣ ∣ b ∣̂ᵉ) (x ·̂ᵣ ∣ a ∣̂ᵉ))
      ≡ true
  crossed-images = refl

  -- a constant: ⌜3⌝ ≾ b ⊩ ⌜3⌝ · a ≾ a · b

  crossed-constant :
    is-just (decideₑ derive (hyps [] [] [] ((⌜ 3 ⌝ᵉ , b) ∷ []) [] []) (⌜ 3 ⌝ᵉ ·̂ₑ a) (a ·̂ₑ b))
      ≡ true
  crossed-constant = refl

  crossed-constant-∅ : is-just (decideₑ derive ∅ᴴ (⌜ 3 ⌝ᵉ ·̂ₑ a) (a ·̂ₑ b)) ≡ false
  crossed-constant-∅ = refl

  ----------------------------------------------------------------
  -- `checkClosed`: two closed sides joined by a chain of
  -- orderings are compared, though no ordering of the set is closed

  chain-late : checkClosed (hyps [] [] ((⌜ 3 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [] []) ≡ nothing
  chain-late = refl

  chain-late-long :
    checkClosed (hyps [] [] [] ((⌜ 5 ⌝ᵉ , a) ∷ (b , ⌜ 4 ⌝ᵉ) ∷ (a , c) ∷ (c , b) ∷ []) [] []) ≡ nothing
  chain-late-long = refl

  chain-on-time :
    checkClosed (hyps [] [] ((⌜ 2 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [] [])
      ≡ just (hyps [] [] ((⌜ 2 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [] [])
  chain-on-time = refl

  -- a disjunction whose grade is below the unit from the orderings
  -- left is dropped: x ≾ y, y ≾ 0 ⊩ x ≾ 0

  drop-following :
    checkClosed (hyps [] [] ((x , y) ∷ (y , ⌜ 0 ⌝ʳ) ∷ []) [] ((α , x) ∷ []) [])
      ≡ just (hyps [] [] ((x , y) ∷ (y , ⌜ 0 ⌝ʳ) ∷ []) [] [] [])
  drop-following = refl

  ----------------------------------------------------------------
  -- `decideₑ` at `full`: a chain through a compound side,
  -- a ≾ b ⊔ d, b ⊔ d ≾ c ⊩ a ≾ c

  through-compound :
    is-just (decideₑ full (hyps [] [] [] ((a , b ⊔̂ₑ d) ∷ (b ⊔̂ₑ d , c) ∷ []) [] []) a c) ≡ true
  through-compound = refl

  through-compound-derive :
    is-just (decideₑ derive (hyps [] [] [] ((a , b ⊔̂ₑ d) ∷ (b ⊔̂ₑ d , c) ∷ []) [] []) a c)
      ≡ false
  through-compound-derive = refl

  -- along a chain from the left side: a · b ≾ c ⊩ a · b ≾ c ⊔ d

  along-vertex :
    is-just (decideₑ full (hyps [] [] [] ((a ·̂ₑ b , c) ∷ []) [] []) (a ·̂ₑ b) (c ⊔̂ₑ d)) ≡ true
  along-vertex = refl

  -- a factor edge, the unit least: a · b ≾ c ⊩ a ≾ c

  factor-least :
    is-just (decideₑ full (hyps [] [] [] ((a ·̂ₑ b , c) ∷ []) [] []) a c) ≡ true
  factor-least = refl

------------------------------------------------------------------
-- Timed traces on the right: the unit least, `·` not commutative

module Sequence where

  open import OpenCalculus.Examples.Specs using (module Traces-Timed-RightSided)
  open Traces-Timed-RightSided using (spec)

  open import OpenCalculus.Syntax.Grades               spec
  open import OpenCalculus.Hypotheses                  spec using (hyps)
  open import OpenCalculus.Inference.SolverImpl.Entail spec using (decideₑ; derive)

  Θ : Scope
  Θ = scope 0 0 4

  a b c d : EExp Θ
  a = evar zero
  b = evar (suc zero)
  c = evar (suc (suc zero))
  d = evar (suc (suc (suc zero)))

  -- `decideₑ` at `derive`: the factors match in order only

  crossed-in-order :
    is-just (decideₑ derive (hyps [] [] [] ((c , b) ∷ (d , a) ∷ []) [] []) (c ·̂ₑ d) (a ·̂ₑ b))
      ≡ false
  crossed-in-order = refl

  crossed-in-order-swapped :
    is-just (decideₑ derive (hyps [] [] [] ((c , b) ∷ (d , a) ∷ []) [] []) (d ·̂ₑ c) (a ·̂ₑ b))
      ≡ true
  crossed-in-order-swapped = refl

------------------------------------------------------------------
-- Left-sided intervals with a top: `·` commutative, the unit not
-- least, the top not the unit

module WithTop where

  open import Grades.Examples.Time.LeftSided
    using (untimed; timed_; [_,+∞⟩; left-sided-intervals-with-⊤; left-sided-witnesses-with-⊤)
  open import Language.Examples.SensorNode.Identity
    left-sided-intervals-with-⊤ (λ _ → timed [ 1 ,+∞⟩) left-sided-witnesses-with-⊤ using (spec)

  open import OpenCalculus.Syntax.Grades               spec
  open import OpenCalculus.Hypotheses                  spec using (hyps; ∅ᴴ)
  open import OpenCalculus.Inference.SolverImpl.Entail spec using (decideₑ; derive; full)
  open import OpenCalculus.Inference.SolverImpl.Canon  spec using (canonₑ)

  Θ : Scope
  Θ = scope 0 0 3

  a b c ⊤̂ : EExp Θ
  a  = evar zero
  b  = evar (suc zero)
  c  = evar (suc (suc zero))
  ⊤̂ = econst untimed

  ⌜_⌝ : ℕ → EExp Θ
  ⌜ n ⌝ = econst (timed [ n ,+∞⟩)

  -- `decideₑ` at `derive`: ⊩ a · b ≾ ⊤ · a, the top matching `b`
  -- after the factors are matched crosswise; the converse fails

  top-crossed : is-just (decideₑ derive ∅ᴴ (a ·̂ₑ b) (⊤̂ ·̂ₑ a)) ≡ true
  top-crossed = refl

  top-crossed-converse : is-just (decideₑ derive ∅ᴴ (⊤̂ ·̂ₑ a) (a ·̂ₑ b)) ≡ false
  top-crossed-converse = refl

  -- `canonₑ`: with the unit not least, a product with the
  -- top is kept

  top-product-kept : canonₑ (a ·̂ₑ ⊤̂) ≡ ⊤̂ ·̂ₑ a
  top-product-kept = refl

  -- `decideₑ` at `full`: a factor edge from `a` into `a · b` needs
  -- the unit below `b`, here reached from the constant unit `⌜0⌝`:
  -- ⌜0⌝ ≾ b, a · b ≾ c ⊩ a ≾ c. The constant `⌜3⌝` lies below the
  -- unit, so it gives no evidence, and neither does nothing.

  factor-evidence :
    is-just (decideₑ full (hyps [] [] [] ((⌜ 0 ⌝ , b) ∷ (a ·̂ₑ b , c) ∷ []) [] []) a c) ≡ true
  factor-evidence = refl

  factor-no-evidence :
    is-just (decideₑ full (hyps [] [] [] ((⌜ 3 ⌝ , b) ∷ (a ·̂ₑ b , c) ∷ []) [] []) a c) ≡ false
  factor-no-evidence = refl

  factor-none :
    is-just (decideₑ full (hyps [] [] [] ((a ·̂ₑ b , c) ∷ []) [] []) a c) ≡ false
  factor-none = refl

  factor-derive :
    is-just (decideₑ derive (hyps [] [] [] ((⌜ 0 ⌝ , b) ∷ (a ·̂ₑ b , c) ∷ []) [] []) a c) ≡ false
  factor-derive = refl

------------------------------------------------------------------
-- `collapse`: a cycle of unknowns local to a clause
--
-- A clause entered with the outer unknown `w` and the rigid `j`, its
-- local unknowns `m`, `t`, `e₂`, and the residual
--
--   R : m ≾ t, t ≾ m, m ≾ j, j ≾ m, m · e₂ ≾ t, w ≾ e₂
--
-- The collapse sends `m` and `t` to `j`; lowering `e₂ := w` then
-- leaves `Rc`, `j · w ≾ j`, which the close defers. Without the
-- collapse, lowering `m := t ⊔ j` (or `t := m ⊔ m · e₂`) and
-- `e₂ := w` leaves `Rm` (or `Rt`), with a self-referential lower
-- bound `t · w ≾ t` (or `m · w ≾ m`), and the close is stuck. At
-- right-sided time no step moves the bound; at left-sided time it holds
-- at every instance and bounds nothing. Checked at both sides of time.

module Cycle (S : LanguageSpec) (opEnum : OpEnum S) where

  open import OpenCalculus.Syntax.Grades                 S
  open import OpenCalculus.Syntax.Subst                  S using (Subst; wkˢᵉ; _⨟ˢ_; sE)
  open import OpenCalculus.Inference.SolverImpl.Resid    S using (Resid; resid)
  open import OpenCalculus.Inference.SolverImpl.Localise S using (collapse; Collapse; stepᵉ; module Find)
  open import OpenCalculus.Inference.SolverImpl.Solve    S opEnum using (splitᴿ)

  Θ Φ : Scope
  Θ = scope 0 0 1
  Φ = Θ +e +e +e +e

  -- the images of the outer unknown and the rigid

  O : Subst (Θ +e) Φ
  O = (wkˢᵉ ⨟ˢ wkˢᵉ) ⨟ˢ wkˢᵉ

  e₂ t m j w : EExp Φ
  e₂ = evar zero
  t  = evar (suc zero)
  m  = evar (suc (suc zero))
  j  = evar (suc (suc (suc zero)))
  w  = evar (suc (suc (suc (suc zero))))

  res : List (EExp Φ × EExp Φ) → Resid Φ
  res l = resid [] l [] [] [] []

  R Rc Rm Rt : Resid Φ
  R  = res ((m , t) ∷ (t , m) ∷ (m , j) ∷ (j , m) ∷ (m ·̂ₑ e₂ , t) ∷ (w , e₂) ∷ [])
  Rc = res ((j ·̂ₑ w , j) ∷ [])
  Rm = res ((t ·̂ₑ w , t) ∷ (j ·̂ₑ w , t) ∷ (t , j) ∷ (j , t) ∷ [])
  Rt = res ((m ·̂ₑ w , m) ∷ (m , j) ∷ (j , m) ∷ [])

  -- the collapse sends `m` and `t` to `j`

  collapses : 𝔹
  collapses = Collapse.cmove (collapse O R)
            ∧ does (sE (Collapse.cσ (collapse O R)) (suc (suc zero)) ≟ᵉ j)
            ∧ does (sE (Collapse.cσ (collapse O R)) (suc zero) ≟ᵉ j)

  -- whether the close is not stuck

  closes : Resid Φ → 𝔹
  closes R' = unstuck (splitᴿ (wkˢᵉ ⨟ˢ O) O (suc (suc (suc zero))) R')
    where
      unstuck : ∀ {X : Set} → Outcome X → 𝔹
      unstuck stuck = false
      unstuck _     = true

  -- whether an unknown is stuck: no value step, and no set raised

  blocked : Fin (nE Φ) → Resid Φ → 𝔹
  blocked k R' = not (is-just (stepᵉ k R')) ∧ not (is-just (Find.raise? O R' (suc (suc (suc zero)))))

  -- with the collapse the close goes through; without it, the close is
  -- stuck, and so are `t` in `Rm` and `m` in `Rt` where their
  -- self-referential bounds are not valid

  with-collapse : 𝔹
  with-collapse = collapses ∧ closes Rc

  without-collapse : 𝔹
  without-collapse = not (closes Rm) ∧ not (closes Rt)

  blocked-without : 𝔹
  blocked-without = blocked (suc zero) Rm ∧ blocked (suc (suc zero)) Rt

module Cycle-RightSided where
  open import OpenCalculus.Examples.Specs using (module Time-RightSided)
  open Cycle Time-RightSided.spec Time-RightSided.enum

  with-collapse-closes : with-collapse ≡ true
  with-collapse-closes = refl

  without-collapse-stuck : without-collapse ≡ true
  without-collapse-stuck = refl

  without-collapse-blocked : blocked-without ≡ true
  without-collapse-blocked = refl

-- At left-sided time `t · w ≾ t` and `m · w ≾ m` hold at every
-- instance and bound nothing, so `t` and `m` are lowered; the close is
-- stuck all the same

module Cycle-LeftSided where
  open import OpenCalculus.Examples.Specs using (module Time-LeftSided)
  open Cycle Time-LeftSided.spec Time-LeftSided.enum

  with-collapse-closes : with-collapse ≡ true
  with-collapse-closes = refl

  without-collapse-stuck : without-collapse ≡ true
  without-collapse-stuck = refl

  without-collapse-unblocked : blocked-without ≡ false
  without-collapse-unblocked = refl

------------------------------------------------------------------
-- `retry`: a deferred condition refuted at a candidate the grade
-- supplies
--
-- At left-sided time, `∀ j. 3 ≾ 3 · j` holds only at `j = 0`, which is
-- both the unit and the top. The candidates for its constants are the
-- bounds `0, …, 7` (`left-sided-witnesses`); at `j = 1` the condition
-- fails, and the entry is refuted. The unit and the top alone leave it
-- undecided.

module Witness where

  open import Grades.Examples.Time.LeftSided using (𝕀; [_,+∞⟩)
  open import OpenCalculus.Examples.Specs using (module Time-LeftSided)
  open Time-LeftSided using (spec; enum)
  open LanguageSpec spec using (Grades)
  open GradeSystemInterface Grades using (uₑ; ⊤ₑ)

  open import OpenCalculus.Syntax.Grades                 spec
  open import OpenCalculus.Hypotheses                    spec using (Hyps; ∅ᴴ; _+eⁿ_; ords; qord)
  open import OpenCalculus.Syntax.Subst                  spec using (Subst)
  open import OpenCalculus.Inference.SolverImpl.Deferred spec using (grid; candidatesₑ)
  open import OpenCalculus.Inference.SolverImpl.Solve    spec enum
    using (Retried; refutedᵈ; keptᵈ; retryᵈ; Verdict; settled; refuted; undecided; witnessᵉ)

  Ψ : Scope
  Ψ = scope 0 0 0

  j : EExp (Ψ +eⁿ 1)
  j = evar zero

  ⌜_⌝ : ℕ → EExp (Ψ +eⁿ 1)
  ⌜ n ⌝ = econst [ n ,+∞⟩

  refutedᴿ : ∀ {H E} → Retried {Ψ} H E → 𝔹
  refutedᴿ (refutedᵈ _)   = true
  refutedᴿ (keptᵈ _ _ _) = false

  undecidedⱽ : ∀ {X : Set} {H : Hyps Ψ} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set} {a : X}
             → Verdict H P a → 𝔹
  undecidedⱽ undecided = true
  undecidedⱽ _         = false

  candidates-0…7 :
    candidatesₑ ⌜ 3 ⌝ (⌜ 3 ⌝ ·̂ₑ j)
      ≡ [ 0 ,+∞⟩ ∷ [ 1 ,+∞⟩ ∷ [ 2 ,+∞⟩ ∷ [ 3 ,+∞⟩ ∷ [ 4 ,+∞⟩ ∷ [ 5 ,+∞⟩ ∷ [ 6 ,+∞⟩ ∷ [ 7 ,+∞⟩ ∷ []
  candidates-0…7 = refl

  refuted-at-one :
    refutedᴿ (retryᵈ ∅ᴴ (qord nothing 1 (ords [] ((⌜ 3 ⌝ , ⌜ 3 ⌝ ·̂ₑ j) ∷ [])))) ≡ true
  refuted-at-one = refl

  unit-top-undecided :
    undecidedⱽ (witnessᵉ {H = ∅ᴴ} 1 ⌜ 3 ⌝ (⌜ 3 ⌝ ·̂ₑ j) (grid (uₑ ∷ ⊤ₑ ∷ []) 1)) ≡ true
  unit-top-undecided = refl

------------------------------------------------------------------
-- `stepᵉ`, lowering: the value `V = B* · L · C*`, and its closure
-- `(B* · L · C*)⁺` where there is a cycle `v · v ≾ v`. `L` is the
-- join of the lower bounds, or the unit where there is none and it
-- is least; `B` and `C` are the joins of the left and right
-- multipliers of the cycles `b · v ≾ v` and `v · c ≾ v`, and
-- `X* · y` is `y ⊔ X⁺ · y`. Each instance is shown by its value.

module Lowering where

  open import Data.Maybe.Base using (Maybe) renaming (map to mapᴹ)
  open import Data.Product using (proj₁)

  module Values (S : LanguageSpec) where

    open import OpenCalculus.Syntax.Grades                 S
    open import OpenCalculus.Inference.SolverImpl.Resid    S using (resid)
    open import OpenCalculus.Inference.SolverImpl.Localise S using (stepᵉ)

    Θ : Scope
    Θ = scope 0 0 1

    v : EExp Θ
    v = evar zero

    -- the value the first unknown is sent to

    value : List (EExp Θ × EExp Θ) → Maybe (EExp Θ)
    value l = mapᴹ proj₁ (stepᵉ zero (resid [] l [] [] [] []))

  -- right-sided intervals: the closure of a non-zero bound is the top

  module RightSided where

    open import Grades.Examples.Time.RightSided using ([0,_]; ↑_; ∞)
    open import OpenCalculus.Examples.Specs using (module Time-RightSided)
    open Time-RightSided using (spec)

    open import OpenCalculus.Syntax.Grades               spec
    open import OpenCalculus.Hypotheses                  spec using (hyps)
    open import OpenCalculus.Inference.SolverImpl.Entail spec using (checkClosed)
    open Values spec

    ⌜_⌝ : ℕ → EExp Θ
    ⌜ n ⌝ = econst [0, ↑ n ]

    ∞̂ : EExp Θ
    ∞̂ = econst [0, ∞ ]

    -- no cycle: `L`

    no-cycle : value ((⌜ 2 ⌝ , v) ∷ (⌜ 3 ⌝ , v) ∷ []) ≡ just (⌜ 2 ⌝ ⊔̂ₑ ⌜ 3 ⌝)
    no-cycle = refl

    -- `v · v ≾ v` only: `L⁺`

    quadratic : value ((⌜ 1 ⌝ , v) ∷ (v ·̂ₑ v , v) ∷ []) ≡ just ∞̂
    quadratic = refl

    -- `d · v ≾ v` only: `L ⊔ D⁺ · L`

    left-linear : value ((⌜ 1 ⌝ , v) ∷ (⌜ 2 ⌝ ·̂ₑ v , v) ∷ []) ≡ just (⌜ 1 ⌝ ⊔̂ₑ ∞̂ ·̂ₑ ⌜ 1 ⌝)
    left-linear = refl

    -- `v · d ≾ v` only: `L ⊔ L · D⁺`

    right-linear : value ((⌜ 1 ⌝ , v) ∷ (v ·̂ₑ ⌜ 2 ⌝ , v) ∷ []) ≡ just (⌜ 1 ⌝ ⊔̂ₑ ⌜ 1 ⌝ ·̂ₑ ∞̂)
    right-linear = refl

    -- a multiplier leaving `L`: `L`

    left-stays : value ((⌜ 1 ⌝ , v) ∷ (⌜ 0 ⌝ ·̂ₑ v , v) ∷ []) ≡ just ⌜ 1 ⌝
    left-stays = refl

    -- the annotated `wait`, `1 · ε ≾ ε ∧ 1 · ε ≾ 1`: no lower bound,
    -- the unit least, so `u ⊔ 1⁺ · u`, the top; `1 · ⊤ ≾ 1` is then
    -- closed and false

    wait-value : value ((⌜ 1 ⌝ ·̂ₑ v , v) ∷ (⌜ 1 ⌝ ·̂ₑ v , ⌜ 1 ⌝) ∷ []) ≡ just (ûₑ ⊔̂ₑ ∞̂ ·̂ₑ ûₑ)
    wait-value = refl

    wait-refuted :
      checkClosed (hyps [] [] [] ((⌜ 1 ⌝ ·̂ₑ (ûₑ ⊔̂ₑ ∞̂ ·̂ₑ ûₑ) , ⌜ 1 ⌝) ∷ []) [] []) ≡ nothing
    wait-refuted = refl

    -- its mirror, `ε · 1 ≾ ε ∧ ε · 1 ≾ 1`: `u ⊔ u · 1⁺`

    wait-mirror-value :
      value ((v ·̂ₑ ⌜ 1 ⌝ , v) ∷ (v ·̂ₑ ⌜ 1 ⌝ , ⌜ 1 ⌝) ∷ []) ≡ just (ûₑ ⊔̂ₑ ûₑ ·̂ₑ ∞̂)
    wait-mirror-value = refl

    wait-mirror-refuted :
      checkClosed (hyps [] [] [] (((ûₑ ⊔̂ₑ ûₑ ·̂ₑ ∞̂) ·̂ₑ ⌜ 1 ⌝ , ⌜ 1 ⌝) ∷ []) [] []) ≡ nothing
    wait-mirror-refuted = refl

    -- left-linear and quadratic: `(L ⊔ D⁺ · L)⁺`, here its own closure

    mixed : value ((⌜ 1 ⌝ , v) ∷ (⌜ 2 ⌝ ·̂ₑ v , v) ∷ (v ·̂ₑ v , v) ∷ [])
              ≡ just (⌜ 1 ⌝ ⊔̂ₑ ∞̂ ·̂ₑ ⌜ 1 ⌝)
    mixed = refl

  -- two-sided intervals: the closure keeps the lower endpoint

  module TwoSided where

    open import Grades.Examples.Time.TwoSidedWithInfinity
      using (↑_; ∞; two-sided-intervals-with-∞) renaming ([_,_] to ⌈_,_⌉)
    open Grading.Time-TwoSided using (opTime)
    open import Grades.Examples.System.Identity using (noWitnesses)
    open import Language.Examples.SensorNode.Identity
      two-sided-intervals-with-∞ opTime noWitnesses using (spec)

    open import OpenCalculus.Syntax.Grades               spec
    open import OpenCalculus.Hypotheses                  spec using (hyps)
    open import OpenCalculus.Inference.SolverImpl.Entail spec using (checkClosed)
    open Values spec

    -- `1 ≾ v ∧ v · v ≾ v ∧ v ≾ [1,∞]`: `v = [1,1]⁺ = [1,∞]`, and the
    -- upper bound holds there

    one : EExp Θ
    one = econst ⌈ 1 , ↑ 1 ⌉

    one-∞ : EExp Θ
    one-∞ = econst ⌈ 1 , ∞ ⌉

    interval-value : value ((one , v) ∷ (v ·̂ₑ v , v) ∷ (v , one-∞) ∷ []) ≡ just one-∞
    interval-value = refl

    interval-holds :
      checkClosed (hyps [] [] [] ((one-∞ , one-∞) ∷ []) [] []) ≡ just (hyps [] [] [] [] [] [])
    interval-holds = refl

    -- left-linear and quadratic: `(L ⊔ D⁺ · L)⁺`, here its own
    -- closure, `[1,∞]`

    two : EExp Θ
    two = econst ⌈ 2 , ↑ 2 ⌉

    mixed : value ((one , v) ∷ (two ·̂ₑ v , v) ∷ (v ·̂ₑ v , v) ∷ [])
              ≡ just (one ⊔̂ₑ econst ⌈ 2 , ∞ ⌉ ·̂ₑ one)
    mixed = refl
