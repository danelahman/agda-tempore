------------------------------------------------------------------------
-- The power of a Kripke frame, for the power of a grade.             --
--                                                                    --
-- A frame for `G` gives one for `power n`, the `n` counters each     --
-- graded by `G`: a world is a vector of `n` worlds, one per counter, --
-- and accessibility holds on each counter separately:                --
--                                                                    --
--   ws ⊑ⱽ[ ρs ] ws'   iff   ws i ⊑[ ρs i ] ws' i   for every i       --
--                                                                    --
-- Every law holds pointwise, with no condition on the frame.         --
------------------------------------------------------------------------

open import Syntax.Grades using (Grade)

module DenotationalSemantics.Model.Example.World.Tallies.Counts.Power (G : Grade) where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Data.Vec.Base using (Vec; []; _∷_)

open import Syntax.Grades.Example.Counts.Power G using (power)

open import Util.Equality

open import DenotationalSemantics.Model.World

open Grade G using () renaming (Carrier to C)

module _ (F : World G) where

  open World F

  infix 5 _⊑ⱽ[_]_

  _⊑ⱽ[_]_ : ∀ {n} → Vec W n → Vec C n → Vec W n → Set
  []       ⊑ⱽ[ []     ] []         = 𝟙
  (w ∷ ws) ⊑ⱽ[ ρ ∷ ρs ] (w' ∷ ws') = (w ⊑[ ρ ] w') × (ws ⊑ⱽ[ ρs ] ws')

  ⊑ⱽ-refl : ∀ {n} {ws : Vec W n} → ws ⊑ⱽ[ Grade.u (power n) ] ws
  ⊑ⱽ-refl {ws = []}    = tt
  ⊑ⱽ-refl {ws = _ ∷ _} = ⊑-refl , ⊑ⱽ-refl

  ⊑ⱽ-trans : ∀ {n} {ρs σs : Vec C n} {ws ws' ws'' : Vec W n}
           → ws ⊑ⱽ[ ρs ] ws' → ws' ⊑ⱽ[ σs ] ws''
           → ws ⊑ⱽ[ Grade._·_ (power n) ρs σs ] ws''
  ⊑ⱽ-trans {ρs = []}    {[]}    {[]}    {[]}    {[]}    _ _ = tt
  ⊑ⱽ-trans {ρs = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) (q , qs) =
    ⊑-trans p q , ⊑ⱽ-trans ps qs

  ⊑ⱽ-mono : ∀ {n} {ρs σs : Vec C n} {ws ws' : Vec W n}
          → Grade._≾_ (power n) ρs σs → ws ⊑ⱽ[ ρs ] ws' → ws ⊑ⱽ[ σs ] ws'
  ⊑ⱽ-mono {ρs = []}    {[]}    {[]}    {[]}    _ _ = tt
  ⊑ⱽ-mono {ρs = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (r , rs) (p , ps) =
    ⊑-mono r p , ⊑ⱽ-mono rs ps

  ⊑ⱽ-irrelevant : ∀ {n} {ρs : Vec C n} {ws ws' : Vec W n}
                → (p q : ws ⊑ⱽ[ ρs ] ws') → p ≡ q
  ⊑ⱽ-irrelevant {ρs = []}    {[]}    {[]}    tt tt = refl
  ⊑ⱽ-irrelevant {ρs = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) (q , qs) =
    cong₂ _,_ (⊑-irrelevant p q) (⊑ⱽ-irrelevant ps qs)

  -- The frame.

  infixl 8 _^_

  _^_ : (n : ℕ) → World (power n)
  _^_ n = record
    { W            = Vec W n
    ; _⊑[_]_       = _⊑ⱽ[_]_
    ; ⊑-refl       = ⊑ⱽ-refl
    ; ⊑-trans      = ⊑ⱽ-trans
    ; ⊑-mono       = ⊑ⱽ-mono
    ; ⊑-irrelevant = ⊑ⱽ-irrelevant
    }
