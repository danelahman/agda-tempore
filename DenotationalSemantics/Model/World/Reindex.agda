------------------------------------------------------------------------
-- Reindexing a Kripke frame, along the grades or along the worlds.    --
--                                                                     --
-- A frame reads only a grade's carrier, unit, product and order, so a --
-- map `g` of grades that is monotone and lax monoidal,                --
--                                                                     --
--   u ≾ g u        g a · g b ≾ g (a · b)                              --
--                                                                     --
-- carries a frame for the target back to one for the source, with     --
-- `w ⊑[ ρ ] w'` read as `w ⊑[ g ρ ] w'`. A grade morphism is such a   --
-- map, strictly (`strict`); so is a map that disagrees with `of-nat`, --
-- `⊤` or the joins, which a frame never sees.                         --
--                                                                     --
-- Every law of a frame is universal in the worlds, so any function    --
-- into the worlds carries a frame back as well (`reindexʷ`).          --
------------------------------------------------------------------------

module DenotationalSemantics.Model.World.Reindex where

open import Syntax.Grades using (Grade; _→ᵍ_)

open import Util.Equality

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Lax monotone monoid maps of grades

record LaxMap (G H : Grade) : Set where
  private
    module G = Grade G
    module H = Grade H
  field
    map      : G.Carrier → H.Carrier
    monotone : ∀ {a b} → a G.≾ b → map a H.≾ map b
    lax-u    : H.u H.≾ map G.u
    lax-·    : ∀ {a b} → map a H.· map b H.≾ map (a G.· b)

-- a grade morphism, strictly

strict : {G H : Grade} → G →ᵍ H → LaxMap G H
strict {H = H} f = record
  { map      = map
  ; monotone = map-monotone
  ; lax-u    = ≾-reflexive (sym map-u)
  ; lax-·    = ≾-reflexive (sym map-·)
  }
  where
    open _→ᵍ_ f
    open Grade H using (≾-reflexive)

------------------------------------------------------------------------
-- Reindexing along the grades

reindexᵍ : {G H : Grade} → LaxMap G H → World H → World G
reindexᵍ g F = record
  { W            = W
  ; _⊑[_]_       = λ w ρ w' → w ⊑[ map ρ ] w'
  ; ⊑-refl       = ⊑-mono lax-u ⊑-refl
  ; ⊑-trans      = λ p q → ⊑-mono lax-· (⊑-trans p q)
  ; ⊑-mono       = λ r p → ⊑-mono (monotone r) p
  ; ⊑-irrelevant = ⊑-irrelevant
  }
  where
    open World F
    open LaxMap g

------------------------------------------------------------------------
-- Reindexing along the worlds

reindexʷ : {G : Grade} {V : Set} (F : World G) → (V → World.W F) → World G
reindexʷ {V = V} F f = record
  { W            = V
  ; _⊑[_]_       = λ v ρ v' → f v ⊑[ ρ ] f v'
  ; ⊑-refl       = ⊑-refl
  ; ⊑-trans      = ⊑-trans
  ; ⊑-mono       = ⊑-mono
  ; ⊑-irrelevant = ⊑-irrelevant
  }
  where open World F
