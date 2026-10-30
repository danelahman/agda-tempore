------------------------------------------------------------------
-- Polarity of an unknown in a hypothesis set                   --
--                                                              --
-- A demand bounds an unknown above, below, both, or not at     --
-- all. An ordering is read left to right; a type along the     --
-- variance table (`Former`), a contravariant position          --
-- reversing the sign, an invariant one reading both.           --
-- Eternality demands and the type side of var-rule             --
-- disjunctions read only the skeleton and bound nothing.       --
-- Lowering an unknown no demand bounds below keeps every       --
-- hypothesis.                                                  --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_)

open import Induction.WellFounded using (Acc; acc; WfRec)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Polarity (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades S
open import PolymorphicCalculus.Syntax.Types  S
open import PolymorphicCalculus.Hypotheses    S

open import PolymorphicCalculus.Inference.SolverImpl.Former S

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

-- A position of a variance, read at a sign

atVar : Variance → Sign → (Sign → Pol) → Pol
atVar co     s f = f s
atVar contra s f = f (flipˢ s)
atVar inv    s f = f s ∪ᴾ f (flipˢ s)

unionᴾ : ∀ {X : Set} → (xs : List X) → (∀ {x} → x ∈ xs → Pol) → Pol
unionᴾ []       f = noᴾ
unionᴾ (x ∷ xs) f = f (here refl) ∪ᴾ unionᴾ xs (λ m → f (there m))

-- The occurrences at the leaves of a value type, each at the sign of its
-- position, and at the parts of a former

polᵛᵃ : ∀ {Ψ} → (Sign → TyVar Ψ → Pol) → (Sign → RExp Ψ → Pol) → (Sign → EExp Ψ → Pol)
      → Sign → (A : OVType Ψ) → Acc _≺_ A → Pol
polᴾ : ∀ {Ψ} → (Sign → TyVar Ψ → Pol) → (Sign → RExp Ψ → Pol) → (Sign → EExp Ψ → Pol)
     → Sign → {A B : OVType Ψ} {ps : List (Part Ψ)} → Decomp A B ps
     → WfRec _≺_ (Acc _≺_) A → ∀ {p} → p ∈ ps → Pol

polᵛᵃ lt lr le s A (acc r) with self A
... | var α       = lt s α
... | form ps g _ = unionᴾ ps (polᴾ lt lr le s g r)

polᴾ lt lr le s g r {ty v X _} m = atVar v s (λ s' → polᵛᵃ lt lr le s' X (r (left g m)))
polᴾ lt lr le s g r {rg v ρ _} m = atVar v s (λ s' → lr s' ρ)
polᴾ lt lr le s g r {eg v ε _} m = atVar v s (λ s' → le s' ε)

polᵛ : ∀ {Ψ} → (Sign → TyVar Ψ → Pol) → (Sign → RExp Ψ → Pol) → (Sign → EExp Ψ → Pol)
     → Sign → OVType Ψ → Pol
polᵛ lt lr le s A = polᵛᵃ lt lr le s A (≺-wf A)

-- Occurrences of one resource-grade unknown

polᵣ-r : ∀ {Ψ} → RVar Ψ → Sign → RExp Ψ → Pol
polᵣ-r i s (rvar j)   = atˢ s ⌊ i ≟ᶠ j ⌋
polᵣ-r i s (rconst _) = noᴾ
polᵣ-r i s (ρ ·̂ᵣ ρ')  = polᵣ-r i s ρ ∪ᴾ polᵣ-r i s ρ'
polᵣ-r i s (ρ ⊔̂ᵣ ρ')  = polᵣ-r i s ρ ∪ᴾ polᵣ-r i s ρ'
polᵣ-r i s ∣ _ ∣̂ᵉ     = noᴾ

polᵣ-v : ∀ {Ψ} → RVar Ψ → Sign → OVType Ψ → Pol
polᵣ-v i = polᵛ (λ _ _ → noᴾ) (polᵣ-r i) (λ _ _ → noᴾ)

polᵣ-c : ∀ {Ψ} → RVar Ψ → Sign → OCType Ψ → Pol
polᵣ-c i s (A ‼ _) = polᵣ-v i s A

-- Occurrences of one effect-grade unknown, reached in resource expressions
-- through the monotone `∣_∣̂ᵉ`

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

polₑ-v : ∀ {Ψ} → EVar Ψ → Sign → OVType Ψ → Pol
polₑ-v i = polᵛ (λ _ _ → noᴾ) (polₑ-r i) (polₑ-e i)

polₑ-c : ∀ {Ψ} → EVar Ψ → Sign → OCType Ψ → Pol
polₑ-c i s (A ‼ ε) = polₑ-v i s A ∪ᴾ polₑ-e i s ε

-- Orderings and var-rule disjunctions, listed

polsᵣ-disj : ∀ {Ψ} → RVar Ψ → List (OVType Ψ × RExp Ψ) → Pol
polsᵣ-disj i []            = noᴾ
polsᵣ-disj i ((_ , ρ) ∷ l) = polᵣ-r i ⁺ ρ ∪ᴾ polsᵣ-disj i l

polsₑ-ordᵣ : ∀ {Ψ} → EVar Ψ → List (RExp Ψ × RExp Ψ) → Pol
polsₑ-ordᵣ i []             = noᴾ
polsₑ-ordᵣ i ((ρ , ρ') ∷ l) = polₑ-r i ⁺ ρ ∪ᴾ polₑ-r i ⁻ ρ' ∪ᴾ polsₑ-ordᵣ i l

polsₑ-disj : ∀ {Ψ} → EVar Ψ → List (OVType Ψ × RExp Ψ) → Pol
polsₑ-disj i []            = noᴾ
polsₑ-disj i ((_ , ρ) ∷ l) = polₑ-r i ⁺ ρ ∪ᴾ polsₑ-disj i l

-- Occurrences of one type variable; eternality atoms and the type side of
-- var-rule disjunctions read only the skeleton, so bound nothing

polₜ-v : ∀ {Ψ} → TyVar Ψ → Sign → OVType Ψ → Pol
polₜ-v α = polᵛ (λ s β → atˢ s ⌊ α ≟ᶠ β ⌋) (λ _ _ → noᴾ) (λ _ _ → noᴾ)

polₜ-c : ∀ {Ψ} → TyVar Ψ → Sign → OCType Ψ → Pol
polₜ-c α s (A ‼ ε) = polₜ-v α s A

polsₜ-sub : ∀ {n} → Fin n → List (Fin n × Fin n) → Pol
polsₜ-sub α []            = noᴾ
polsₜ-sub α ((β , γ) ∷ l) =
  atˢ ⁺ ⌊ α ≟ᶠ β ⌋ ∪ᴾ atˢ ⁻ ⌊ α ≟ᶠ γ ⌋ ∪ᴾ polsₜ-sub α l
