------------------------------------------------------------------
-- Solver stages on hand-written constraints                      --
--                                                                --
-- Each test calls one stage of the solver on a hypothesis set, a --
-- pair of grade expressions or a residual written out by hand,   --
-- and checks its answer by `refl`. The stages, and the commits   --
-- whose steps they guard:                                        --
--                                                                --
--   `canonᴴ` (b91638f): an ordering with a join on its left is   --
--     one ordering per alternative. No example program depends   --
--     on it.                                                     --
--   `walkᵈ` (b91638f): a var-rule disjunction entailed by        --
--     another is pruned (also `Reports`).                        --
--   `canonᵣ`/`canonₑ` (b91638f): a product with the top is the   --
--     top where the unit is least (also `Reports`).              --
--   `decide≾ᵣ`/`decide≾ₑ` (391579f): products compare as         --
--     multisets where `·` commutes. No example program depends   --
--     on it.                                                     --
--   `closedᴴ` (dca615d): closed sides joined by a chain of       --
--     orderings are compared (also `Boxes`).                     --
--   `collapse` (6733339): a cycle of unknowns local to a clause  --
--     is one unknown, without which the clause's close is stuck. --
--                                                                --
-- The grades differ in what the stages read, `u-least?` and      --
-- `·-comm?`: right-sided intervals (both), timed traces on the   --
-- right (the unit least, `·` not commutative), left-sided        --
-- intervals with an adjoined top (`·` commutative, the unit not  --
-- least, the top not the unit), and both sides of time for the   --
-- collapse.                                                      --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false; not; _∧_) renaming (Bool to 𝔹)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing; is-just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (does)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.Scopes
open import TypeInference.Outcome using (Outcome; stuck)
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Stages where

------------------------------------------------------------------
-- Right-sided intervals: the unit least, `·` commutative

module Deadline where

  open import Syntax.Grades.Example.Time.RightSided using ([0,_]; ↑_)
  open import TypeInference.Examples.Specs using (module Time-RightSided)
  open Time-RightSided using (spec)
  open LanguageSpec spec using (Grades)
  open GradeSystemInterface Grades using (⊤ᵣ; ⊤ₑ)

  open import TypeInference.OpenSyntax.Grades   spec
  open import TypeInference.OpenSyntax.Types    spec using (OVType; tvar)
  open import TypeInference.OpenSyntax.Hyps     spec using (hyps; ∅ᴴ; ordᵣ; ordₑ; disj)
  open import TypeInference.SolverImpl.Canon    spec using (canonᴴ; canonᵣ; canonₑ)
  open import TypeInference.SolverImpl.Simplify spec using (walkᵈ)
  open import TypeInference.SolverImpl.Normal   spec using (decide≾ₑ; decide≾ᵣ)
  open import TypeInference.SolverImpl.Closed   spec using (closedᴴ)

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
  -- `canonᴴ` (b91638f): an ordering with a join on its left is one
  -- ordering per alternative; a join on the right is kept

  split-left-r :
    ordᵣ (canonᴴ (hyps [] [] ((x ⊔̂ᵣ y , z) ∷ (z , x ⊔̂ᵣ y) ∷ []) [] []))
      ≡ (x , z) ∷ (y , z) ∷ (z , x ⊔̂ᵣ y) ∷ []
  split-left-r = refl

  split-left-e :
    ordₑ (canonᴴ (hyps [] [] [] ((a ⊔̂ₑ b , c) ∷ (c , a ⊔̂ₑ b) ∷ []) []))
      ≡ (a , c) ∷ (b , c) ∷ (c , a ⊔̂ₑ b) ∷ []
  split-left-e = refl

  ----------------------------------------------------------------
  -- `walkᵈ` (b91638f): with `x ≾ y`, `eternal α ∨ y ≾ uᵣ` entails
  -- `eternal α ∨ x ≾ uᵣ`, which is pruned, as is the repeat

  prune-entailed :
    disj (walkᵈ (hyps [] [] ((x , y) ∷ []) []
                      ((α , x) ∷ (α , y) ∷ (α , y) ∷ (α , x ⊔̂ᵣ z) ∷ [])))
      ≡ (α , y) ∷ (α , x ⊔̂ᵣ z) ∷ []
  prune-entailed = refl

  ----------------------------------------------------------------
  -- `canonᵣ`/`canonₑ` (b91638f): a product with the top among its
  -- factors is the top, which absorbs the join

  top-product-r : canonᵣ (x ·̂ᵣ rconst ⊤ᵣ) ≡ rconst ⊤ᵣ
  top-product-r = refl

  top-product-e : canonₑ (a ·̂ₑ econst ⊤ₑ) ≡ econst ⊤ₑ
  top-product-e = refl

  top-product-join : canonᵣ (x ·̂ᵣ rconst ⊤ᵣ ⊔̂ᵣ y) ≡ rconst ⊤ᵣ
  top-product-join = refl

  ----------------------------------------------------------------
  -- `decide≾ₑ`/`decide≾ᵣ` (391579f): products compare as multisets,
  -- matching the factors crosswise

  -- c ≾ b, d ≾ a ⊩ c · d ≾ a · b

  crossed-e :
    is-just (decide≾ₑ {Q = hyps [] [] [] ((c , b) ∷ (d , a) ∷ []) []} (c ·̂ₑ d) (a ·̂ₑ b))
      ≡ true
  crossed-e = refl

  crossed-e-∅ : is-just (decide≾ₑ {Q = ∅ᴴ} (c ·̂ₑ d) (a ·̂ₑ b)) ≡ false
  crossed-e-∅ = refl

  -- z ≾ y, w ≾ x ⊩ z · w ≾ x · y

  crossed-r :
    is-just (decide≾ᵣ {Q = hyps [] [] ((z , y) ∷ (w , x) ∷ []) [] []} (z ·̂ᵣ w) (x ·̂ᵣ y))
      ≡ true
  crossed-r = refl

  -- with images of effect variables: z ≾ ∣a∣, ∣b∣ ≾ x ⊩ z · ∣b∣ ≾ x · ∣a∣

  crossed-images :
    is-just (decide≾ᵣ {Q = hyps [] [] ((z , ∣ a ∣̂ᵉ) ∷ (∣ b ∣̂ᵉ , x) ∷ []) [] []}
                      (z ·̂ᵣ ∣ b ∣̂ᵉ) (x ·̂ᵣ ∣ a ∣̂ᵉ))
      ≡ true
  crossed-images = refl

  -- a constant: ⌜3⌝ ≾ b ⊩ ⌜3⌝ · a ≾ a · b

  crossed-constant :
    is-just (decide≾ₑ {Q = hyps [] [] [] ((⌜ 3 ⌝ᵉ , b) ∷ []) []} (⌜ 3 ⌝ᵉ ·̂ₑ a) (a ·̂ₑ b))
      ≡ true
  crossed-constant = refl

  crossed-constant-∅ : is-just (decide≾ₑ {Q = ∅ᴴ} (⌜ 3 ⌝ᵉ ·̂ₑ a) (a ·̂ₑ b)) ≡ false
  crossed-constant-∅ = refl

  ----------------------------------------------------------------
  -- `closedᴴ` (dca615d): two closed sides joined by a chain of
  -- orderings are compared, though no ordering of the set is closed

  chain-late : closedᴴ (hyps [] [] ((⌜ 3 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] []) ≡ nothing
  chain-late = refl

  chain-late-long :
    closedᴴ (hyps [] [] [] ((⌜ 5 ⌝ᵉ , a) ∷ (b , ⌜ 4 ⌝ᵉ) ∷ (a , c) ∷ (c , b) ∷ []) []) ≡ nothing
  chain-late-long = refl

  chain-on-time :
    closedᴴ (hyps [] [] ((⌜ 2 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [])
      ≡ just (hyps [] [] ((⌜ 2 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [])
  chain-on-time = refl

------------------------------------------------------------------
-- Timed traces on the right: the unit least, `·` not commutative

module Sequence where

  open import TypeInference.Examples.Specs using (module Traces-Timed-RightSided)
  open Traces-Timed-RightSided using (spec)

  open import TypeInference.OpenSyntax.Grades spec
  open import TypeInference.OpenSyntax.Hyps   spec using (hyps)
  open import TypeInference.SolverImpl.Normal spec using (decide≾ₑ)

  Θ : Scope
  Θ = scope 0 0 4

  a b c d : EExp Θ
  a = evar zero
  b = evar (suc zero)
  c = evar (suc (suc zero))
  d = evar (suc (suc (suc zero)))

  -- `decide≾ₑ` (391579f): the factors match in order only

  crossed-in-order :
    is-just (decide≾ₑ {Q = hyps [] [] [] ((c , b) ∷ (d , a) ∷ []) []} (c ·̂ₑ d) (a ·̂ₑ b))
      ≡ false
  crossed-in-order = refl

  crossed-in-order-swapped :
    is-just (decide≾ₑ {Q = hyps [] [] [] ((c , b) ∷ (d , a) ∷ []) []} (d ·̂ₑ c) (a ·̂ₑ b))
      ≡ true
  crossed-in-order-swapped = refl

------------------------------------------------------------------
-- Left-sided intervals with a top: `·` commutative, the unit not
-- least, the top not the unit

module WithTop where

  open import Syntax.Grades.Example.Time.LeftSided
    using (untimed; timed_; [_,+∞⟩; left-sided-intervals-with-⊤)
  open import Syntax.Grades.Example.Worked.Typing.Core
    left-sided-intervals-with-⊤ (λ _ → timed [ 1 ,+∞⟩) using (spec)

  open import TypeInference.OpenSyntax.Grades spec
  open import TypeInference.OpenSyntax.Hyps   spec using (∅ᴴ)
  open import TypeInference.SolverImpl.Normal spec using (decide≾ₑ)
  open import TypeInference.SolverImpl.Canon  spec using (canonₑ)

  Θ : Scope
  Θ = scope 0 0 2

  a b ⊤̂ : EExp Θ
  a  = evar zero
  b  = evar (suc zero)
  ⊤̂ = econst untimed

  -- `decide≾ₑ` (391579f): ⊩ a · b ≾ ⊤ · a, the top matching `b`
  -- after the factors are matched crosswise; the converse fails

  top-crossed : is-just (decide≾ₑ {Q = ∅ᴴ} (a ·̂ₑ b) (⊤̂ ·̂ₑ a)) ≡ true
  top-crossed = refl

  top-crossed-converse : is-just (decide≾ₑ {Q = ∅ᴴ} (⊤̂ ·̂ₑ a) (a ·̂ₑ b)) ≡ false
  top-crossed-converse = refl

  -- `canonₑ` (b91638f): with the unit not least, a product with the
  -- top is kept

  top-product-kept : canonₑ (a ·̂ₑ ⊤̂) ≡ ⊤̂ ·̂ₑ a
  top-product-kept = refl

------------------------------------------------------------------
-- `collapse` (6733339): a cycle of unknowns local to a clause
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
-- bound `t · w ≾ t` (or `m · w ≾ m`) that no step moves, and the
-- close is stuck. Checked at both sides of time.

module Cycle (S : LanguageSpec) (opEnum : OpEnum S) where

  open import TypeInference.OpenSyntax.Grades   S
  open import TypeInference.OpenSyntax.Subst    S using (Subst; wkˢᵉ; _⨟ˢ_; sE)
  open import TypeInference.SolverImpl.Resid    S using (Resid; resid)
  open import TypeInference.SolverImpl.Localise S using (collapse; Collapse; stepᵉ; module Find)
  open import TypeInference.SolverImpl.Solve    S opEnum using (splitᴿ)

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

  -- with the collapse the close goes through; without it, `t` in `Rm`
  -- and `m` in `Rt` are stuck, and so is the close

  with-collapse : 𝔹
  with-collapse = collapses ∧ closes Rc

  without-collapse : 𝔹
  without-collapse = blocked (suc zero) Rm ∧ not (closes Rm)
                   ∧ blocked (suc (suc zero)) Rt ∧ not (closes Rt)

module Cycle-RightSided where
  open import TypeInference.Examples.Specs using (module Time-RightSided)
  open Cycle Time-RightSided.spec Time-RightSided.enum

  with-collapse-closes : with-collapse ≡ true
  with-collapse-closes = refl

  without-collapse-stuck : without-collapse ≡ true
  without-collapse-stuck = refl

module Cycle-LeftSided where
  open import TypeInference.Examples.Specs using (module Time-LeftSided)
  open Cycle Time-LeftSided.spec Time-LeftSided.enum

  with-collapse-closes : with-collapse ≡ true
  with-collapse-closes = refl

  without-collapse-stuck : without-collapse ≡ true
  without-collapse-stuck = refl
