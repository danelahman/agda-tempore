------------------------------------------------------------------
-- Solver stages on hand-written constraints                    --
--                                                              --
-- Each test applies one solver stage to hand-written           --
-- hypotheses, grade expressions or a residual, and checks its  --
-- answer by `refl`: `canonᴴ`, `walkᵈ`, `canonᵣ`/`canonₑ`,      --
-- `decideᵣ`/`decideₑ` at `derive` and `full`, `checkClosed`,   --
-- `collapse`, `retry` and lowering (`stepᵉ`). The grades are   --
-- chosen for the hint properties the stages read, `u-least?`   --
-- and `·-comm?`.                                               --
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
open import Grades.Hints using (SystemHints)
import Grades.Examples.Worked.Operations.Grading as Grading

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.Outcome using (Outcome; stuck)
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Stages where

------------------------------------------------------------------
-- Right-sided intervals: the unit least, `·` commutative

module Deadline where

  open import Grades.Examples.Time.RightSided using ([0,_]; ↑_)
  open import PolymorphicCalculus.Examples.Specs using (module Time-RightSided)
  open Time-RightSided using (spec; hints)
  open LanguageSpec spec using (Grades)
  open GradeSystemInterface Grades using (⊤ᵣ; ⊤ₑ)

  open import PolymorphicCalculus.Syntax.Grades                 spec
  open import PolymorphicCalculus.Syntax.Types                  spec using (OVType; tvar)
  open import PolymorphicCalculus.Hypotheses                    spec using (hyps; ∅ᴴ; ordᵣ; ordₑ; disj)
  open import PolymorphicCalculus.Inference.SolverImpl.Canon    spec hints using (canonᴴ; canonᵣ; canonₑ)
  open import PolymorphicCalculus.Inference.SolverImpl.Simplify spec hints using (walkᵈ)
  open import PolymorphicCalculus.Inference.SolverImpl.Entail   spec hints
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
  -- `canonᴴ`, tested only here: a join on the left splits into one
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
  -- `canonᵣ`/`canonₑ`: a product with the top as a factor is the top

  top-product-r : canonᵣ (x ·̂ᵣ rconst ⊤ᵣ) ≡ rconst ⊤ᵣ
  top-product-r = refl

  top-product-e : canonₑ (a ·̂ₑ econst ⊤ₑ) ≡ econst ⊤ₑ
  top-product-e = refl

  top-product-join : canonᵣ (x ·̂ᵣ rconst ⊤ᵣ ⊔̂ᵣ y) ≡ rconst ⊤ᵣ
  top-product-join = refl

  ----------------------------------------------------------------
  -- `decideₑ`/`decideᵣ` at `derive`, tested only here: products compare
  -- as multisets, matching the factors crosswise

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
  -- `checkClosed`: closed sides joined by a chain of orderings are
  -- compared

  chain-late : checkClosed (hyps [] [] ((⌜ 3 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [] []) ≡ nothing
  chain-late = refl

  chain-late-long :
    checkClosed (hyps [] [] [] ((⌜ 5 ⌝ᵉ , a) ∷ (b , ⌜ 4 ⌝ᵉ) ∷ (a , c) ∷ (c , b) ∷ []) [] []) ≡ nothing
  chain-late-long = refl

  chain-on-time :
    checkClosed (hyps [] [] ((⌜ 2 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [] [])
      ≡ just (hyps [] [] ((⌜ 2 ⌝ʳ , x) ∷ (x , ⌜ 2 ⌝ʳ) ∷ []) [] [] [])
  chain-on-time = refl

  -- a disjunct entailed by the orderings is dropped: x ≾ y, y ≾ 0 ⊩ x ≾ 0

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

  open import PolymorphicCalculus.Examples.Specs using (module Traces-Timed-RightSided)
  open Traces-Timed-RightSided using (spec; hints)

  open import PolymorphicCalculus.Syntax.Grades               spec
  open import PolymorphicCalculus.Hypotheses                  spec using (hyps)
  open import PolymorphicCalculus.Inference.SolverImpl.Entail spec hints using (decideₑ; derive)

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
    using (untimed; timed_; [_,+∞⟩; left-sided-intervals-with-⊤; left-sided-intervals-with-⊤ʰ;
           left-sided-witnesses-with-⊤)
  open import Grades.Examples.System.Identity using (identityʰ)
  open import Language.Examples.SensorNode.Identity
    left-sided-intervals-with-⊤ (λ _ → timed [ 1 ,+∞⟩) using (spec)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ left-sided-intervals-with-⊤ʰ left-sided-witnesses-with-⊤

  open import PolymorphicCalculus.Syntax.Grades               spec
  open import PolymorphicCalculus.Hypotheses                  spec using (hyps; ∅ᴴ)
  open import PolymorphicCalculus.Inference.SolverImpl.Entail spec hints using (decideₑ; derive; full)
  open import PolymorphicCalculus.Inference.SolverImpl.Canon  spec hints using (canonₑ)

  Θ : Scope
  Θ = scope 0 0 3

  a b c ⊤̂ : EExp Θ
  a  = evar zero
  b  = evar (suc zero)
  c  = evar (suc (suc zero))
  ⊤̂ = econst untimed

  ⌜_⌝ : ℕ → EExp Θ
  ⌜ n ⌝ = econst (timed [ n ,+∞⟩)

  -- `decideₑ` at `derive`: ⊩ a · b ≾ ⊤ · a crosswise; the converse fails

  top-crossed : is-just (decideₑ derive ∅ᴴ (a ·̂ₑ b) (⊤̂ ·̂ₑ a)) ≡ true
  top-crossed = refl

  top-crossed-converse : is-just (decideₑ derive ∅ᴴ (⊤̂ ·̂ₑ a) (a ·̂ₑ b)) ≡ false
  top-crossed-converse = refl

  -- `canonₑ`: with the unit not least, a product with the top is kept

  top-product-kept : canonₑ (a ·̂ₑ ⊤̂) ≡ ⊤̂ ·̂ₑ a
  top-product-kept = refl

  -- `decideₑ` at `full`: a factor edge needs the unit below `b`:
  -- ⌜0⌝ ≾ b, a · b ≾ c ⊩ a ≾ c; `⌜3⌝ ≾ b`, or nothing, is no evidence

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
-- Outer unknown `w`, rigid `j`, local unknowns `m`, `t`, `e₂`:
--
--   R : m ≾ t, t ≾ m, m ≾ j, j ≾ m, m · e₂ ≾ t, w ≾ e₂
--
-- Collapsing `m`, `t` to `j` leaves `j · w ≾ j`, deferred. Without it,
-- lowering leaves a self-referential bound (`Rm`, `Rt`) and the close is
-- stuck. Checked at both sides of time.

module Cycle (S : LanguageSpec) (hints : SystemHints (LanguageSpec.Grades S))
             (opEnum : OpEnum S) where

  open import PolymorphicCalculus.Syntax.Grades                 S
  open import PolymorphicCalculus.Syntax.GradeSubstitution      S using (Subst; wkˢᵉ; _⨟ˢ_; sE)
  open import PolymorphicCalculus.Inference.SolverImpl.Resid    S using (Resid; resid)
  open import PolymorphicCalculus.Inference.SolverImpl.Localise S hints using (collapse; Collapse; stepᵉ; module Find)
  open import PolymorphicCalculus.Inference.SolverImpl.Solve    S hints opEnum using (splitᴿ)

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

  -- with the collapse the close goes through; without it, it is stuck

  with-collapse : 𝔹
  with-collapse = collapses ∧ closes Rc

  without-collapse : 𝔹
  without-collapse = not (closes Rm) ∧ not (closes Rt)

  blocked-without : 𝔹
  blocked-without = blocked (suc zero) Rm ∧ blocked (suc (suc zero)) Rt

module Cycle-RightSided where
  open import PolymorphicCalculus.Examples.Specs using (module Time-RightSided)
  open Cycle Time-RightSided.spec Time-RightSided.hints Time-RightSided.enum

  with-collapse-closes : with-collapse ≡ true
  with-collapse-closes = refl

  without-collapse-stuck : without-collapse ≡ true
  without-collapse-stuck = refl

  without-collapse-blocked : blocked-without ≡ true
  without-collapse-blocked = refl

-- At left-sided time the self-referential bounds hold everywhere, so
-- `t` and `m` are lowered; the close is stuck all the same

module Cycle-LeftSided where
  open import PolymorphicCalculus.Examples.Specs using (module Time-LeftSided)
  open Cycle Time-LeftSided.spec Time-LeftSided.hints Time-LeftSided.enum

  with-collapse-closes : with-collapse ≡ true
  with-collapse-closes = refl

  without-collapse-stuck : without-collapse ≡ true
  without-collapse-stuck = refl

  without-collapse-unblocked : blocked-without ≡ false
  without-collapse-unblocked = refl

------------------------------------------------------------------
-- `retry`: at left-sided time `∀ j. 3 ≾ 3 · j` holds at the unit (also
-- the top) but fails at the candidate `j = 1` (`left-sided-witnesses`);
-- the unit and the top alone leave it undecided.

module Witness where

  open import Grades.Examples.Time.LeftSided using (𝕀; [_,+∞⟩)
  open import PolymorphicCalculus.Examples.Specs using (module Time-LeftSided)
  open Time-LeftSided using (spec; hints; enum)
  open LanguageSpec spec using (Grades)
  open GradeSystemInterface Grades using (uₑ; ⊤ₑ)

  open import PolymorphicCalculus.Syntax.Grades                 spec
  open import PolymorphicCalculus.Hypotheses                    spec using (Hyps; ∅ᴴ; _+eⁿ_; ords; qord)
  open import PolymorphicCalculus.Syntax.GradeSubstitution      spec using (Subst)
  open import PolymorphicCalculus.Inference.SolverImpl.Deferred spec hints using (grid; candidatesₑ)
  open import PolymorphicCalculus.Inference.SolverImpl.Solve    spec hints enum
    using (Retried; refutedᵈ; keptᵈ; retryᵈ; Verdict; settled; refuted; undecided; witnessᵉ)

  Ω : Scope
  Ω = scope 0 0 0

  j : EExp (Ω +eⁿ 1)
  j = evar zero

  ⌜_⌝ : ℕ → EExp (Ω +eⁿ 1)
  ⌜ n ⌝ = econst [ n ,+∞⟩

  refutedᴿ : ∀ {H E} → Retried {Ω} H E → 𝔹
  refutedᴿ (refutedᵈ _)   = true
  refutedᴿ (keptᵈ _ _ _) = false

  undecidedⱽ : ∀ {X : Set} {H : Hyps Ω} {P : ∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set} {a : X}
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
-- `stepᵉ`, lowering: `B* · L · C*`, closed under `⁺` given `v · v ≾ v`.
-- `L` joins the lower bounds (the unit if none and it is least); `B`,
-- `C` join the multipliers of `b · v ≾ v`, `v · c ≾ v`; `X* · y` is
-- `y ⊔ X⁺ · y`.

module Lowering where

  open import Data.Maybe.Base using (Maybe) renaming (map to mapᴹ)
  open import Data.Product using (proj₁)

  module Values (S : LanguageSpec) (hints : SystemHints (LanguageSpec.Grades S)) where

    open import PolymorphicCalculus.Syntax.Grades                 S
    open import PolymorphicCalculus.Inference.SolverImpl.Resid    S using (resid)
    open import PolymorphicCalculus.Inference.SolverImpl.Localise S hints using (stepᵉ)

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
    open import PolymorphicCalculus.Examples.Specs using (module Time-RightSided)
    open Time-RightSided using (spec; hints)

    open import PolymorphicCalculus.Syntax.Grades               spec
    open import PolymorphicCalculus.Hypotheses                  spec using (hyps)
    open import PolymorphicCalculus.Inference.SolverImpl.Entail spec hints using (checkClosed)
    open Values spec hints

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

    -- Tempore's annotated `wait`, `1 · ε ≾ ε ∧ 1 · ε ≾ 1`: the top, and
    -- `1 · ⊤ ≾ 1` is false

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
      using (↑_; ∞; two-sided-intervals-with-∞; two-sided-intervals-with-∞ʰ)
      renaming ([_,_] to ⌈_,_⌉)
    open Grading.Time-TwoSided using (opTime)
    open import Grades.Examples.System.Identity using (identityʰ; noWitnesses)
    open import Language.Examples.SensorNode.Identity
      two-sided-intervals-with-∞ opTime using (spec)

    hints : SystemHints (LanguageSpec.Grades spec)
    hints = identityʰ two-sided-intervals-with-∞ʰ noWitnesses

    open import PolymorphicCalculus.Syntax.Grades               spec
    open import PolymorphicCalculus.Hypotheses                  spec using (hyps)
    open import PolymorphicCalculus.Inference.SolverImpl.Entail spec hints using (checkClosed)
    open Values spec hints

    -- `1 ≾ v ∧ v · v ≾ v ∧ v ≾ [1,∞]`: `v = [1,1]⁺ = [1,∞]`, within bound

    one : EExp Θ
    one = econst ⌈ 1 , ↑ 1 ⌉

    one-∞ : EExp Θ
    one-∞ = econst ⌈ 1 , ∞ ⌉

    interval-value : value ((one , v) ∷ (v ·̂ₑ v , v) ∷ (v , one-∞) ∷ []) ≡ just one-∞
    interval-value = refl

    interval-holds :
      checkClosed (hyps [] [] [] ((one-∞ , one-∞) ∷ []) [] []) ≡ just (hyps [] [] [] [] [] [])
    interval-holds = refl

    -- left-linear and quadratic: `(L ⊔ D⁺ · L)⁺ = [1,∞]`

    two : EExp Θ
    two = econst ⌈ 2 , ↑ 2 ⌉

    mixed : value ((one , v) ∷ (two ·̂ₑ v , v) ∷ (v ·̂ₑ v , v) ∷ [])
              ≡ just (one ⊔̂ₑ econst ⌈ 2 , ∞ ⌉ ·̂ₑ one)
    mixed = refl
