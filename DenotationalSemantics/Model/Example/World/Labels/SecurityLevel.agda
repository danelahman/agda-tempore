------------------------------------------------------------------------
-- A Kripke frame for security levels: worlds are labels.              --
--                                                                     --
-- A world is the label reached so far. It floats upward, and a grade  --
-- `ℓ` raises it by at most `ℓ`:                                       --
--                                                                     --
--   w ⊑ˡ[ ℓ ] w'   iff   w ⊑ w'   and   w' ⊑ w ∨ ℓ                    --
--                                                                     --
-- It is the action frame of the level grade restricted to forward     --
-- moves: the least level is the unit, so without `w ⊑ w'` the unit    --
-- grade would lower the label. At the unit grade the label stays put. --
--                                                                     --
-- Generic in the lattice; instances at `Low < High` and at taint      --
-- sets over `Fin n`, where a world is the set of labels touched.      --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Labels.SecurityLevel where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_)

open import Syntax.Grades.Example.SecurityLevel
  using (LevelLattice; module LevelLattice; level-grade;
         low-high; two-point-levels; taint-lattice; taint-sets)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Action using (action; forward)

-- The frame, at a lattice of levels.

module _ (L : LevelLattice) where

  open LevelLattice L

  labels : World (level-grade L)
  labels = forward (action (level-grade L)) _⊑_ ⊑-refl ⊑-trans ⊑-irrelevant

  open World labels public using () renaming (_⊑[_]_ to _⊑ˡ[_]_)

  -- the relation it states

  ⊑ˡ-def : ∀ {w ℓ w'} → (w ⊑ˡ[ ℓ ] w') ≡ ((w ⊑ w') × (w' ⊑ w ∨ ℓ))
  ⊑ˡ-def = refl

-- at `Low < High`

two-point-labels : World two-point-levels
two-point-labels = labels low-high

-- at taint sets over `Fin n`

taint-labels : (n : ℕ) → World (taint-sets n)
taint-labels n = labels (taint-lattice n)
