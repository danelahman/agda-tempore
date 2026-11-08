------------------------------------------------------------------------
-- The context modality at intervals of time                          --
--                                                                    --
-- At `ρ = [1,2]` the grade `g = [2,2]` lies below `⊤ · ρ = [1,∞]`    --
-- but has no residual by `ρ`: both `g ≾ [0,0] · ρ` and               --
-- `g ≾ [1,1] · ρ`, and no grade lies below both `[0,0]` and `[1,1]`  --
-- (`no-residual`). So `L_[1,2]` has no left adjoint                  --
-- (`no-left-adjoint-[1,2]`) and is not a parametric right adjoint    --
-- (`not-PRA-[1,2]`). The grade's own `_≾?_` decides the side         --
-- conditions.                                                        --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)

open import Grades.Base
open import Grades.Examples.Time.Interval
open import Grades.Examples.System.Identity using (identity-grade-system)
open import Language.BaseTypes using (noBaseTypes)
open import Language.Spec
import Language.Operations as Ops

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Examples.ContextModality.Interval where

G : GradeSystem
G = identity-grade-system interval

ops : Ops.Operations G noBaseTypes
ops = record
  { Op = ⊥ ; _≟ₒ_ = λ () ; param = λ () ; arity = λ () ; op-grade = λ () }

spec : LanguageSpec
spec = withoutBaseTypes G ops

open GradeSystemInterface G

open import PolymorphicCalculus.Syntax.Grades                   spec using (rconst)
open import PolymorphicCalculus.Hypotheses                      spec using (∅ᴴ)
open import PolymorphicCalculus.Typing.Renaming.ContextModality spec

ρ g : R
ρ = [ 1 , ↑ 2 ]
g = [ 2 , ↑ 2 ]

g≾⊤ρ : g ≾ᵣ ⊤ᵣ ·ᵣ ρ
g≾⊤ρ = toWitness {a? = g ≾ᵣ? (⊤ᵣ ·ᵣ ρ)} tt

g≾[0,0]ρ : g ≾ᵣ [ 0 , ↑ 0 ] ·ᵣ ρ
g≾[0,0]ρ = toWitness {a? = g ≾ᵣ? ([ 0 , ↑ 0 ] ·ᵣ ρ)} tt

g≾[1,1]ρ : g ≾ᵣ [ 1 , ↑ 1 ] ·ᵣ ρ
g≾[1,1]ρ = toWitness {a? = g ≾ᵣ? ([ 1 , ↑ 1 ] ·ᵣ ρ)} tt

-- a residual `e` would lie below `[0,0]` and `[1,1]`

no-residual : ¬ Residual ρ g
no-residual (e , r)
  with ≤-trans (proj₁ (⇒res r [ 1 , ↑ 1 ] g≾[1,1]ρ))
               (≤∞-trans {↑ min e} {max e} {↑ 0} (min≤max e)
                         (proj₂ (⇒res r [ 0 , ↑ 0 ] g≾[0,0]ρ)))
... | ()

no-left-adjoint-[1,2] : ¬ LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ)
no-left-adjoint-[1,2] la = no-residual (left-adjoint⇒residual la g g≾⊤ρ)

not-PRA-[1,2] : ¬ PRA {∅ˢ} ∅ᴴ (rconst ρ)
not-PRA-[1,2] pra = no-left-adjoint-[1,2] (PRA⇒LeftAdjoint ∅ᴴ pra)
