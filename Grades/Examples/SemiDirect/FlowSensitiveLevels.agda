------------------------------------------------------------------------
-- Flow-sensitive levels: a level and the level of each output.       --
--                                                                    --
-- A grade `(l , W)` is "touches nothing above `l`, and writes each   --
-- sink `s` at most at the level `W s`", where `W s` is in `L⊥`, the  --
-- levels with a new least element `⊥`, "not written". It is the      --
-- semidirect product of the levels with the outputs, the level       --
-- touched raising each output written after it:                      --
--                                                                    --
--   (l , W) · (l' , W')  =  (l ∨ l' , W ∨ raise l W')                --
--                                                                    --
-- where `raise l` sends `⊥` to `⊥` and a level `l'` to `l ∨ l'`.     --
-- Keeping `⊥` apart from "written at the least level" makes `raise   --
-- l` preserve `⊥`, and every `raise l` reflects it. The unit         --
-- `(bot , ⊥)`, with `bot` the least level, is least, as its hints    --
-- declare; they do not declare `_·_` commutative. A level is its own --
-- closure, and the hints declare the closure                         --
--                                                                    --
--   (l , W)⁺  =  (l , W ∨ raise l W) .                               --
--                                                                    --
-- Delays touch no level. Sinks are named by natural numbers.         --
------------------------------------------------------------------------

module Grades.Examples.SemiDirect.FlowSensitiveLevels where

open import Data.Empty using (⊥-elim) renaming (⊥ to 𝟘)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt) renaming (⊤ to 𝟙)

open import Relation.Nullary using (yes; no)

open import Grades.Durations using (Duration)
open import Grades.Base using (Grade; plus-self)
open import Grades.Hints using (GradeHints)
open import Grades.Examples.Lattice
  using (LevelLattice; level-grade; level-gradeʰ; low-high-lattice; LowHigh; Low; High)
open import Grades.Indexed using (ℕ-names; module Maps)
open Maps ℕ-names using (indexedˢ; indexedᵃ; indexed⁺; Map)
open import Grades.SemiDirect
  using (Semilattice; Action; ActionPlus; semidirect; semidirect⁺ʰ)

open import Util.Equality

module Over (L : LevelLattice) where

  private module L = LevelLattice L
  open L using (_∨_)

  ----------------------------------------------------------------------
  -- The levels with a new least element

  infix 4 _⊑⊥_

  _⊑⊥_ : Maybe L.Carrier → Maybe L.Carrier → Set
  nothing ⊑⊥ _       = 𝟙
  just _  ⊑⊥ nothing = 𝟘
  just a  ⊑⊥ just b  = a L.⊑ b

  _∨⊥_ : Maybe L.Carrier → Maybe L.Carrier → Maybe L.Carrier
  nothing ∨⊥ w       = w
  just a  ∨⊥ nothing = just a
  just a  ∨⊥ just b  = just (a ∨ b)

  written-at : Semilattice
  written-at = record
    { Carrier      = Maybe L.Carrier
    ; _⊑_          = _⊑⊥_
    ; bot          = nothing
    ; top          = just L.top
    ; _∨_          = _∨⊥_
    ; ⊑-refl       = λ { {nothing} → tt ; {just a} → L.⊑-refl }
    ; ⊑-trans      = λ { {nothing} _ _ → tt
                       ; {just _} {just _} {just _} p q → L.⊑-trans p q }
    ; ⊑-irrelevant = λ { {nothing} _ _ → refl
                       ; {just _} {just _} p q → L.⊑-irrelevant p q }
    ; _⊑?_         = λ { nothing _ → yes tt
                       ; (just _) nothing → no λ ()
                       ; (just a) (just b) → a L.⊑? b }
    ; bot-⊑        = λ _ → tt
    ; ⊑-top        = λ { nothing → tt ; (just a) → L.⊑-top a }
    ; ∨-ubˡ        = λ { nothing _ → tt ; (just a) nothing → L.⊑-refl
                       ; (just a) (just b) → L.∨-ubˡ a b }
    ; ∨-ubʳ        = λ { nothing w → refl⊥ w ; (just a) nothing → tt
                       ; (just a) (just b) → L.∨-ubʳ a b }
    ; ∨-lub        = λ { {nothing} _ q → q
                       ; {just _} {nothing} p _ → p
                       ; {just _} {just _} {just _} p q → L.∨-lub p q }
    }
    where
      refl⊥ : ∀ w → w ⊑⊥ w
      refl⊥ nothing  = tt
      refl⊥ (just a) = L.⊑-refl

  -- the outputs: the level each sink is written at

  outputs : Semilattice
  outputs = indexedˢ written-at

  ----------------------------------------------------------------------
  -- The levels raise what is written after them

  raise : L.Carrier → Maybe L.Carrier → Maybe L.Carrier
  raise l = Maybe.map (l ∨_)

  private
    ∨-mono : ∀ {a a' b b'} → a L.⊑ a' → b L.⊑ b' → a ∨ b L.⊑ a' ∨ b'
    ∨-mono {a' = a'} {b' = b'} p q =
      L.∨-lub (L.⊑-trans p (L.∨-ubˡ a' b')) (L.⊑-trans q (L.∨-ubʳ a' b'))

  raise-action : {D : Duration} → Action (level-grade L {D}) written-at
  raise-action = record
    { act              = raise
    ; act-identity     = λ { nothing → tt , tt
                           ; (just a) → L.∨-lub (L.bot-⊑ a) L.⊑-refl , L.∨-ubʳ L.bot a }
    ; act-comp         = λ { l l' nothing → tt , tt
                           ; l l' (just a) →
                               L.∨-lub (∨-mono L.⊑-refl (L.∨-ubˡ l' a))
                                       (L.⊑-trans (L.∨-ubʳ l' a) (L.∨-ubʳ l (l' ∨ a)))
                             , L.∨-lub (L.⊑-trans (L.∨-ubˡ l l') (L.∨-ubˡ (l ∨ l') a))
                                       (∨-mono (L.∨-ubʳ l l') L.⊑-refl) }
    ; act-bot          = λ _ → tt
    ; act-∨            = λ { l nothing w → refl⊥ (raise l w)
                           ; l (just a) nothing → L.⊑-refl
                           ; l (just a) (just b) →
                               L.∨-lub (L.⊑-trans (L.∨-ubˡ l a) (L.∨-ubˡ (l ∨ a) (l ∨ b)))
                                       (∨-mono (L.∨-ubʳ l a) (L.∨-ubʳ l b)) }
    ; act-⊔            = λ { l l' nothing → tt
                           ; l l' (just a) →
                               L.∨-lub (∨-mono (L.∨-ubˡ l a) (L.∨-ubˡ l' a))
                                       (L.⊑-trans (L.∨-ubʳ l a) (L.∨-ubˡ (l ∨ a) (l' ∨ a))) }
    ; act-monoˡ        = λ { {n = nothing} _ → tt ; {n = just a} p → ∨-mono p L.⊑-refl }
    ; act-monoʳ        = λ { {n = nothing} _ → tt
                           ; {n = just _} {just _} q → ∨-mono L.⊑-refl q }
    ; act-reflects-bot = λ { {n = nothing} _ _ → tt ; {n = just _} _ () }
    }
    where
      refl⊥ : ∀ w → w ⊑⊥ w
      refl⊥ nothing  = tt
      refl⊥ (just a) = L.⊑-refl

  ----------------------------------------------------------------------
  -- The grade

  flow-sensitive-levels : {D : Duration} → Grade D
  flow-sensitive-levels {D} =
    semidirect (level-grade L) outputs (indexedᵃ (raise-action {D}))

  -- a level is its own closure

  level-plus : {D : Duration} (l : L.Carrier)
             → ActionPlus (indexedᵃ (raise-action {D})) l
  level-plus {D} l = indexed⁺ (raise-action {D}) record
    { closure = plus-self L.⊑-refl (L.∨-lub L.⊑-refl L.⊑-refl)
    ; act-⁺   = λ q → q
    }

  -- its hints by copatterns, so that `flow-sensitive-levels` is not
  -- compared as a record value

  private
    module H {D : Duration} =
      GradeHints (semidirect⁺ʰ (level-gradeʰ L) outputs (indexedᵃ (raise-action {D}))
                               (λ l → just (level-plus l)))

  flow-sensitive-levelsʰ : {D : Duration} → GradeHints (flow-sensitive-levels {D})
  GradeHints.𝟏-least? (flow-sensitive-levelsʰ {D}) = H.𝟏-least? {D}
  GradeHints.·-comm?  (flow-sensitive-levelsʰ {D}) = H.·-comm? {D}
  GradeHints.plus?    (flow-sensitive-levelsʰ {D}) = H.plus? {D}

------------------------------------------------------------------------
-- At the two-point lattice `Low < High`

open Over low-high-lattice public
  using (written-at; outputs; raise; raise-action)
  renaming ( flow-sensitive-levels  to two-point-flow-sensitive-levels
           ; flow-sensitive-levelsʰ to two-point-flow-sensitive-levelsʰ )
