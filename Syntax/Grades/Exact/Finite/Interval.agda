------------------------------------------------------------------------
-- Finite expressions as interval grades, in any dense time domain.   --
--                                                                    --
-- A grade `[ L , U ]` pairs a lower bound `L` with an upper bound    --
-- `U` that are consistent: some exact word fits a word of each,      --
--                                                                    --
--   Σ[ x ] (Σ[ y ∈ ⟦ L ⟧ ] x ⊑ y) × (Σ[ z ∈ ⟦ U ⟧ ] x ⊑ z)           --
--                                                                    --
-- Consistent pairs are a sub-grade of the product of the two grades  --
-- (`Exact.Interval`), compared componentwise, the word being data    --
-- the order ignores.                                                 --
--                                                                    --
-- A literal names the consistency run as a sequence of operations    --
-- and delays: `[ L , U ]⟨ r ⟩` checks, by the reader, that the hull  --
-- of `r` on each side (`Exact.Hull`) lies below the endpoint.        --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Finite.Interval
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Bool.Base using () renaming (T to IsTrue)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (⁅_⁆)
import Data.Fin.Subset
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)
open import Syntax.Grades.Upward using (Upward; _∣ᵍ_)
open import Syntax.Durations.Monus T using (Carrier; 0ᴰ; _<ᴰ_; _<ᴰ?_)
open import Syntax.Durations.Intervals T using (fin; ⁻; ⁺) renaming (_∣_ to _∣ᶜ_; ⊑-refl to ⊑ᶜ-refl)

open import Syntax.Grades.Exact.Base T Op n code code-injective using (Word; op; ![_]; stretch; stretch-zero)
open import Syntax.Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-refl; ⊑-trans)
open import Syntax.Grades.Exact.Lift T Op n code code-injective
  using (Lang; uᴸ; _·ᴸ_; ⊑-++) renaming (_≾_ to _≾ᴸ_)
open import Syntax.Grades.Exact.Expression T Op n code code-injective running
  using (lower; upper; ‵_; ⟦_⟧)
open import Syntax.Grades.Exact.Finite T Op n code code-injective name code-name running
  dense κ κ-pos using (members; nonEmpty; Proper)
open import Syntax.Grades.Exact.Finite.Grades T Op n code code-injective name code-name running
  dense κ κ-pos
open RunningTimes.RunningTimes running using (rt-inhabited⁺)

------------------------------------------------------------------------
-- Consistency, and the interval grade (`Exact.Interval`)

private
  -- a wait lies in both its hulls
  wait-∈ᴸ : ∀ τ → ⟦ expr (waitᴸ τ) ⟧ ![ τ ]
  wait-∈ᴸ τ = case (0ᴰ <ᴰ? τ)
    where
      case : (d : Dec (0ᴰ <ᴰ τ)) → ⟦ expr (at-least′ τ d) ⟧ ![ τ ]
      case (yes _) = τ , ⊑ᶜ-refl , refl
      case (no ¬p) = stretch-zero Data.Fin.Subset.⊥ τ ¬p

  wait-∈ᵁ : ∀ τ → ⟦ expr (waitᵁ τ) ⟧ ![ τ ]
  wait-∈ᵁ τ = τ , ⊑ᶜ-refl , refl

open import Syntax.Grades.Exact.Interval T Op n code code-injective running lowerᵍ upperᵍ
  (λ c → ⟦ expr c ⟧) (λ c → ⟦ expr c ⟧)
  (λ le → toWitness (by-reader le)) (λ le → toWitness (by-reader le))
  refl refl
  (λ x∈ y∈ → _ , _ , refl , x∈ , y∈) (λ x∈ y∈ → _ , _ , refl , x∈ , y∈)
  wait-∈ᴸ wait-∈ᵁ public

------------------------------------------------------------------------
-- Literals

-- a pair of literals, consistent by the run `r`

[_,_]⟨_⟩ : (L : Proper′ lower) (U : Proper′ upper) (r : Run)
         → {pl : Proper (hullᴸ r)} {pu : Proper (hullᵁ r)}
         → {cl : True (⌜ hullᴸ r ⌝ {pl} ≾ᵉ? L)} {cu : True (⌜ hullᵁ r ⌝ {pu} ≾ᵉ? U)}
         → Grade.Carrier intervalᵍ
[ L , U ]⟨ r ⟩ {pl} {pu} {cl} {cu} =
  (L , U) , run-consistent r L U (toWitness cl) (toWitness cu)

-- an operation, at both endpoints

private
  nonEmpty-map : ∀ {A B : Set} (f : A → B) (xs : List A)
               → IsTrue (nonEmpty xs) → IsTrue (nonEmpty (map f xs))
  nonEmpty-map f (_ ∷ _) _ = tt

  members-⁅⁆ : ∀ {m} (c : Fin m) → IsTrue (nonEmpty (members ⁅ c ⁆))
  members-⁅⁆ zero    = tt
  members-⁅⁆ (suc c) = nonEmpty-map suc _ (members-⁅⁆ c)

‵ᵍ : ∀ {s} → Op → Proper′ s
‵ᵍ o = ⌜ ‵ o ⌝ {nonEmpty-map _ _ (members-⁅⁆ (code o))}

-- the pair of two grades of an operation is consistent

operation′ : ∀ o (l : Proper′ lower) (u : Proper′ upper) → expr l ≡ ‵ o → expr u ≡ ‵ o
           → Grade.Carrier intervalᵍ
operation′ o l u el eu =
  (l , u) , op o d ∷ [] , fits-∈ (subst (λ e → ⟦ e ⟧ (op o d ∷ [])) (sym el) (o∈ {lower})) ,
                          fits-∈ (subst (λ e → ⟦ e ⟧ (op o d ∷ [])) (sym eu) (o∈ {upper}))
  where
    d = proj₁ (rt-inhabited⁺ o)
    o∈ : ∀ {s} → ⟦ ‵_ {s} o ⟧ (op o d ∷ [])
    o∈ = o , d , x∈⁅x⁆ (code o) , proj₂ (rt-inhabited⁺ o) , refl

operation : Op → Grade.Carrier intervalᵍ
operation o = operation′ o (‵ᵍ o) (‵ᵍ o) refl refl
