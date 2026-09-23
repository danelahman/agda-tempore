------------------------------------------------------------------
-- Polarity of an unknown in a residual or a hypothesis set       --
--                                                                --
-- A demand bounds an unknown above, below, both, or not at all.  --
-- An ordering reads left to right; a type is traversed with the  --
-- variance of the slot, an arrow domain and a box grade flipping --
-- it. An eternality demand and the type side of a var-rule       --
-- disjunction read only the skeleton, so they bound nothing.     --
--                                                                --
-- The analysis directs the closer's choice of default and is not --
-- part of its soundness. At the reporting boundary it is         --
-- load-bearing instead: lowering an unknown with no occurrence   --
-- below preserves every hypothesis.                              --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; not; _∧_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.Scopes

module TypeInference.SolverImpl.Polarity (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Resid S

record Pol : Set where
  constructor pol
  field
    above : 𝔹                    -- some demand bounds the unknown above
    below : 𝔹                    -- some demand bounds the unknown below

open Pol public

infixr 5 _∪ᴾ_

noᴾ : Pol
noᴾ = pol false false

_∪ᴾ_ : Pol → Pol → Pol
p ∪ᴾ q = pol (above p ∨ above q) (below p ∨ below q)

-- Which side of an ordering the traversed position sits on

data Sign : Set where
  ⁺ ⁻ : Sign

flipˢ : Sign → Sign
flipˢ ⁺ = ⁻
flipˢ ⁻ = ⁺

atˢ : Sign → 𝔹 → Pol
atˢ ⁺ b = pol b false
atˢ ⁻ b = pol false b

-- Occurrences of one resource-grade unknown

polᵣ-r : ∀ {Ψ} → RVar Ψ → Sign → RExp Ψ → Pol
polᵣ-r i s (rvar j)   = atˢ s ⌊ i ≟ᶠ j ⌋
polᵣ-r i s (rconst _) = noᴾ
polᵣ-r i s (ρ ·̂ᵣ ρ')  = polᵣ-r i s ρ ∪ᴾ polᵣ-r i s ρ'
polᵣ-r i s (ρ ⊔̂ᵣ ρ')  = polᵣ-r i s ρ ∪ᴾ polᵣ-r i s ρ'
polᵣ-r i s ∣ _ ∣̂ᵉ     = noᴾ

mutual

  polᵣ-v : ∀ {Ψ} → RVar Ψ → Sign → OVType Ψ → Pol
  polᵣ-v i s (tvar _)  = noᴾ
  polᵣ-v i s (Base _)  = noᴾ
  polᵣ-v i s Unit      = noᴾ
  polᵣ-v i s Bool      = noᴾ
  polᵣ-v i s (A |×| B) = polᵣ-v i s A ∪ᴾ polᵣ-v i s B
  polᵣ-v i s Empty     = noᴾ
  polᵣ-v i s (A ⇒ C)   = polᵣ-v i (flipˢ s) A ∪ᴾ polᵣ-c i s C
  polᵣ-v i s ([ ρ ] A) = polᵣ-r i (flipˢ s) ρ ∪ᴾ polᵣ-v i s A

  polᵣ-c : ∀ {Ψ} → RVar Ψ → Sign → OCType Ψ → Pol
  polᵣ-c i s (A ‼ _) = polᵣ-v i s A

-- Occurrences of one effect-grade unknown; a resource expression
-- reaches them through the monotone `∣_∣̂ᵉ`

polₑ-e : ∀ {Ψ} → EVar Ψ → Sign → EExp Ψ → Pol
polₑ-e i s (evar j)   = atˢ s ⌊ i ≟ᶠ j ⌋
polₑ-e i s (econst _) = noᴾ
polₑ-e i s (ε ·̂ₑ ε')  = polₑ-e i s ε ∪ᴾ polₑ-e i s ε'
polₑ-e i s (ε ⊔̂ₑ ε')  = polₑ-e i s ε ∪ᴾ polₑ-e i s ε'

polₑ-r : ∀ {Ψ} → EVar Ψ → Sign → RExp Ψ → Pol
polₑ-r i s (rvar _)   = noᴾ
polₑ-r i s (rconst _) = noᴾ
polₑ-r i s (ρ ·̂ᵣ ρ')  = polₑ-r i s ρ ∪ᴾ polₑ-r i s ρ'
polₑ-r i s (ρ ⊔̂ᵣ ρ')  = polₑ-r i s ρ ∪ᴾ polₑ-r i s ρ'
polₑ-r i s ∣ ε ∣̂ᵉ     = polₑ-e i s ε

mutual

  polₑ-v : ∀ {Ψ} → EVar Ψ → Sign → OVType Ψ → Pol
  polₑ-v i s (tvar _)  = noᴾ
  polₑ-v i s (Base _)  = noᴾ
  polₑ-v i s Unit      = noᴾ
  polₑ-v i s Bool      = noᴾ
  polₑ-v i s (A |×| B) = polₑ-v i s A ∪ᴾ polₑ-v i s B
  polₑ-v i s Empty     = noᴾ
  polₑ-v i s (A ⇒ C)   = polₑ-v i (flipˢ s) A ∪ᴾ polₑ-c i s C
  polₑ-v i s ([ ρ ] A) = polₑ-r i (flipˢ s) ρ ∪ᴾ polₑ-v i s A

  polₑ-c : ∀ {Ψ} → EVar Ψ → Sign → OCType Ψ → Pol
  polₑ-c i s (A ‼ ε) = polₑ-v i s A ∪ᴾ polₑ-e i s ε

-- The residual's components

polsᵣ-ord : ∀ {Ψ} → RVar Ψ → List (RExp Ψ × RExp Ψ) → Pol
polsᵣ-ord i []             = noᴾ
polsᵣ-ord i ((ρ , ρ') ∷ l) = polᵣ-r i ⁺ ρ ∪ᴾ polᵣ-r i ⁻ ρ' ∪ᴾ polsᵣ-ord i l

polsᵣ-sub : ∀ {Ψ} → RVar Ψ → List (OVType Ψ × OVType Ψ) → Pol
polsᵣ-sub i []            = noᴾ
polsᵣ-sub i ((A , B) ∷ l) = polᵣ-v i ⁺ A ∪ᴾ polᵣ-v i ⁻ B ∪ᴾ polsᵣ-sub i l

polsᵣ-disj : ∀ {Ψ} → RVar Ψ → List (OVType Ψ × RExp Ψ) → Pol
polsᵣ-disj i []            = noᴾ
polsᵣ-disj i ((_ , ρ) ∷ l) = polᵣ-r i ⁺ ρ ∪ᴾ polsᵣ-disj i l

polsₑ-ordᵣ : ∀ {Ψ} → EVar Ψ → List (RExp Ψ × RExp Ψ) → Pol
polsₑ-ordᵣ i []             = noᴾ
polsₑ-ordᵣ i ((ρ , ρ') ∷ l) = polₑ-r i ⁺ ρ ∪ᴾ polₑ-r i ⁻ ρ' ∪ᴾ polsₑ-ordᵣ i l

polsₑ-ordₑ : ∀ {Ψ} → EVar Ψ → List (EExp Ψ × EExp Ψ) → Pol
polsₑ-ordₑ i []             = noᴾ
polsₑ-ordₑ i ((ε , ε') ∷ l) = polₑ-e i ⁺ ε ∪ᴾ polₑ-e i ⁻ ε' ∪ᴾ polsₑ-ordₑ i l

polsₑ-sub : ∀ {Ψ} → EVar Ψ → List (OVType Ψ × OVType Ψ) → Pol
polsₑ-sub i []            = noᴾ
polsₑ-sub i ((A , B) ∷ l) = polₑ-v i ⁺ A ∪ᴾ polₑ-v i ⁻ B ∪ᴾ polsₑ-sub i l

polsₑ-disj : ∀ {Ψ} → EVar Ψ → List (OVType Ψ × RExp Ψ) → Pol
polsₑ-disj i []            = noᴾ
polsₑ-disj i ((_ , ρ) ∷ l) = polₑ-r i ⁺ ρ ∪ᴾ polsₑ-disj i l

polᵣ : ∀ {Ψ} → Resid Ψ → RVar Ψ → Pol
polᵣ R i = polsᵣ-ord i (rs R) ∪ᴾ polsᵣ-sub i (ss R) ∪ᴾ polsᵣ-disj i (ds R)

polₑ : ∀ {Ψ} → Resid Ψ → EVar Ψ → Pol
polₑ R i = polsₑ-ordᵣ i (rs R) ∪ᴾ polsₑ-ordₑ i (es R)
             ∪ᴾ polsₑ-sub i (ss R) ∪ᴾ polsₑ-disj i (ds R)

-- Occurrences in reported types, each read as the left side of a
-- subtyping

polsᵣ-ty : ∀ {Ψ} → RVar Ψ → List (OCType Ψ) → Pol
polsᵣ-ty i []      = noᴾ
polsᵣ-ty i (X ∷ l) = polᵣ-c i ⁺ X ∪ᴾ polsᵣ-ty i l

polsₑ-ty : ∀ {Ψ} → EVar Ψ → List (OCType Ψ) → Pol
polsₑ-ty i []      = noᴾ
polsₑ-ty i (X ∷ l) = polₑ-c i ⁺ X ∪ᴾ polsₑ-ty i l

-- An unknown pushed only upwards is the one the greatest grade suits

onlyBelow : Pol → 𝔹
onlyBelow p = below p ∧ not (above p)

-- Occurrences of one type variable. An eternality atom and the type
-- side of a var-rule disjunction read only the skeleton, which a
-- subtyping hypothesis preserves, so neither bounds the variable.

mutual

  polₜ-v : ∀ {Ψ} → TyVar Ψ → Sign → OVType Ψ → Pol
  polₜ-v α s (tvar β)  = atˢ s ⌊ α ≟ᶠ β ⌋
  polₜ-v α s (Base _)  = noᴾ
  polₜ-v α s Unit      = noᴾ
  polₜ-v α s Bool      = noᴾ
  polₜ-v α s (A |×| B) = polₜ-v α s A ∪ᴾ polₜ-v α s B
  polₜ-v α s Empty     = noᴾ
  polₜ-v α s (A ⇒ C)   = polₜ-v α (flipˢ s) A ∪ᴾ polₜ-c α s C
  polₜ-v α s ([ ρ ] A) = polₜ-v α s A

  polₜ-c : ∀ {Ψ} → TyVar Ψ → Sign → OCType Ψ → Pol
  polₜ-c α s (A ‼ ε) = polₜ-v α s A

polsₜ-sub : ∀ {n} → Fin n → List (Fin n × Fin n) → Pol
polsₜ-sub α []            = noᴾ
polsₜ-sub α ((β , γ) ∷ l) =
  atˢ ⁺ ⌊ α ≟ᶠ β ⌋ ∪ᴾ atˢ ⁻ ⌊ α ≟ᶠ γ ⌋ ∪ᴾ polsₜ-sub α l

-- The same over a hypothesis set. Its eternality and subtyping atoms
-- carry no grade.

polᵣᴴ : ∀ {Ψ} → Hyps Ψ → RVar Ψ → Pol
polᵣᴴ Q i = polsᵣ-ord i (ordᵣ Q) ∪ᴾ polsᵣ-disj i (disj Q)

polₑᴴ : ∀ {Ψ} → Hyps Ψ → EVar Ψ → Pol
polₑᴴ Q i = polsₑ-ordᵣ i (ordᵣ Q) ∪ᴾ polsₑ-ordₑ i (ordₑ Q)
              ∪ᴾ polsₑ-disj i (disj Q)

polₜᴴ : ∀ {Ψ} → Hyps Ψ → TyVar Ψ → Pol
polₜᴴ Q α = polsₜ-sub α (subᵥ Q)
