------------------------------------------------------------------------
-- The lock at two-sided time, `ρ = [1,2]`, which is not above the    --
-- unit `[0,0]`. With `σ = [0,1]` and `σ' = [1,1]`, `σ ⋦ 𝟏`, `σ' ≾ ρ` --
-- and `σ · σ' ≾ ρ`, so `L_[1,2]` is not a parametric right adjoint   --
-- (`not-PRA-[1,2]`); it has no left adjoint either                   --
-- (`no-left-adjoint-[1,2]`). The grade's own `_≾?_` decides the side --
-- conditions.                                                        --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import Grades.Base
open import Grades.Examples.Time.TwoSidedWithInfinity
open import Grades.Examples.System.Identity using (identityGradeSystem)
open import Language.BaseTypes using (noBaseTypes)
open import Language.Spec
import Language.Operations as Ops

module MonomorphicCalculus.Examples.Lock.TwoSided where

G : GradeSystem
G = identityGradeSystem two-sided-intervals-with-∞

ops : Ops.Operations G noBaseTypes
ops = record
  { Op = ⊥ ; _≟ₒ_ = λ () ; param = λ () ; arity = λ () ; op-grade = λ () }

spec : LanguageSpec
spec = withoutBaseTypes G ops

open GradeSystemInterface G

open import MonomorphicCalculus.Syntax.Contexts      spec using ([])
open import MonomorphicCalculus.Syntax.Renaming.Lock spec

ρ σ σ' : R
ρ  = [ 1 , ↑ 2 ]
σ  = [ 0 , ↑ 1 ]
σ' = [ 1 , ↑ 1 ]

σ≰𝟏 : ¬ (σ ≾ᵣ 𝟏ᵣ)
σ≰𝟏 = toWitnessFalse {a? = σ ≾ᵣ? 𝟏ᵣ} tt

σ'≾ρ : σ' ≾ᵣ ρ
σ'≾ρ = toWitness {a? = σ' ≾ᵣ? ρ} tt

σσ'≾ρ : σ ·ᵣ σ' ≾ᵣ ρ
σσ'≾ρ = toWitness {a? = (σ ·ᵣ σ') ≾ᵣ? ρ} tt

𝟏≰ρ : ¬ (𝟏ᵣ ≾ᵣ ρ)
𝟏≰ρ = toWitnessFalse {a? = 𝟏ᵣ ≾ᵣ? ρ} tt

not-PRA-[1,2] : ¬ PRA ρ
not-PRA-[1,2] = Counterexample.not-PRA σ≰𝟏 σ'≾ρ σσ'≾ρ

no-left-adjoint-[1,2] : ¬ LeftAdjoint ρ
no-left-adjoint-[1,2] la = no-object-at-[] 𝟏≰ρ (proj₁ (la []))
