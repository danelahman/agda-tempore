------------------------------------------------------------------------
-- Grade literals: extended regular expressions with non-empty         --
-- languages.                                                          --
--                                                                     --
-- `⌊ e ⌋` is the grade of the expression `e`. Its argument that the   --
-- language is non-empty is implicit, the `True` of a decision, so at  --
-- a concrete expression it is found by computation, and an empty     --
-- literal is rejected when the program is checked.                    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)

module Syntax.Grades.Regular.Literal (k : ℕ) (tick : Fin k) where

open import Function.Bundles using (_⇔_)
open import Relation.Nullary.Decidable using (True; toWitness)

open import Syntax.Grades.Regular.Automaton k using (_∈_)
open import Syntax.Grades.Regular.Decide k using (nonempty?)
open import Syntax.Grades.Regular.Expression k
open import Syntax.Grades.Regular.Grade k tick using (Regular; regular; table)

⌊_⌋ : (e : Expr) → {True (nonempty? (elab e) (elab-wf e))} → Regular
⌊ e ⌋ {ne} = regular (elab e) (elab-wf e) (elab-canonical e) (toWitness ne)

∈-⌊⌋ : ∀ e {ne} w → w ∈ table (⌊ e ⌋ {ne}) ⇔ ⟦ e ⟧ w
∈-⌊⌋ e w = elab-correct e w
