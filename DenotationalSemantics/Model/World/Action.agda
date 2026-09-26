-------------------------------------------------------------------------
-- The action frame of a grade, and frames restricted to forward       --
-- moves.                                                              --
--                                                                     --
-- A grade acts on itself by right multiplication, a lax,              --
-- order-enriched action. Taking the grades as worlds, `ρ` reaches     --
-- whatever is below `c · ρ`:                                          --
--                                                                     --
--   c ⊑[ ρ ] c'   iff   c' ≾ c · ρ                                    --
--                                                                     --
-- Reindexed along a map of points into the carrier (`reindexʷ`), it   --
-- is a tick frame: a world is how much has accumulated, and a grade   --
-- bounds how much more may. `Ticks.Time.*` state this relation at the --
-- points `of-nat`, up to the order of a sum.                          --
--                                                                     --
-- At a grade whose unit is least, `c' ≾ c` holds at the unit grade,   --
-- so the accumulated amount may shrink. `forward` intersects a frame  --
-- with a preorder on its worlds, and with the order of accumulation   --
-- it confines moves to the forward ones.                              --
-------------------------------------------------------------------------

module DenotationalSemantics.Model.World.Action where

open import Data.Product using (_×_; _,_)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- The action frame

action : (G : Grade) → World G
action G = record
  { W            = Carrier
  ; _⊑[_]_       = λ c ρ c' → c' ≾ c · ρ
  ; ⊑-refl       = λ {c} → ≾-reflexive (sym (·-identityʳ c))
  ; ⊑-trans      = λ {ρ₁} {ρ₂} {c} p q →
                     ≾-trans q (≾-trans (·-monoˡ-≾ p)
                                        (≾-reflexive (·-assoc c ρ₁ ρ₂)))
  ; ⊑-mono       = λ r p → ≾-trans p (·-monoʳ-≾ r)
  ; ⊑-irrelevant = ≾-irrelevant
  }
  where open Grade G

------------------------------------------------------------------------
-- Forward moves along a proof-irrelevant preorder on the worlds

forward : {G : Grade} (F : World G) (_≼_ : World.W F → World.W F → Set)
        → (∀ {w} → w ≼ w)
        → (∀ {w w' w''} → w ≼ w' → w' ≼ w'' → w ≼ w'')
        → (∀ {w w'} (p q : w ≼ w') → p ≡ q)
        → World G
forward F _≼_ ≼-refl ≼-trans ≼-irrelevant = record
  { W            = W
  ; _⊑[_]_       = λ w ρ w' → (w ≼ w') × (w ⊑[ ρ ] w')
  ; ⊑-refl       = ≼-refl , ⊑-refl
  ; ⊑-trans      = λ (a , p) (b , q) → ≼-trans a b , ⊑-trans p q
  ; ⊑-mono       = λ r (a , p) → a , ⊑-mono r p
  ; ⊑-irrelevant = λ (a , p) (b , q) →
                     cong₂ _,_ (≼-irrelevant a b) (⊑-irrelevant p q)
  }
  where open World F
