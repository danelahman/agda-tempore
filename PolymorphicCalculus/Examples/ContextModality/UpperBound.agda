------------------------------------------------------------------------
-- The context modality at upper bounds on time                       --
--                                                                    --
-- Every grade `g` has a residual by every `ρ`, `g ⊖ ρ`, truncated    --
-- subtraction of the bounds (`residual`). A lowering subtracts `ρ`   --
-- from the modalities from the right (`lower`), so `L_ρ` has a left  --
-- adjoint at every grade (`left-adjoint`) and is a parametric right  --
-- adjoint (`PRA-everywhere`); in particular at `[0,2]`, which is not --
-- equivalent to `𝟏` (`left-adjoint-[0,2]`, `PRA-[0,2]`).             --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (0∸n≡0; +-suc; +-identityʳ; +-comm; m≤n+o⇒m∸n≤o)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Grades.Base
open import Grades.Examples.Time.UpperBound
open import Grades.Examples.System.Identity using (identity-grade-system)
open import Language.BaseTypes using (noBaseTypes)
open import Language.Spec
import Language.Operations as Ops

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Examples.ContextModality.UpperBound where

G : GradeSystem
G = identity-grade-system upper-bound

ops : Ops.Operations G noBaseTypes
ops = record
  { Op = ⊥ ; _≟ₒ_ = λ () ; param = λ () ; arity = λ () ; op-grade = λ () }

spec : LanguageSpec
spec = withoutBaseTypes G ops

open GradeSystemInterface G

open import PolymorphicCalculus.Syntax.Grades                   spec
open import PolymorphicCalculus.Syntax.Contexts                 spec
open import PolymorphicCalculus.Hypotheses                      spec using (∅ᴴ)
open import PolymorphicCalculus.Typing.Renaming.ContextModality spec

------------------------------------------------------------------------
-- Truncated subtraction

_∸∞_ : ℕ∞ → ℕ∞ → ℕ∞
(↑ a) ∸∞ (↑ r) = ↑ (a ∸ r)
(↑ a) ∸∞ ∞     = ↑ 0
∞     ∸∞ (↑ r) = ∞
∞     ∸∞ ∞     = ↑ 0

-- what is left of `r` after `a`

rest : ℕ∞ → ℕ∞ → ℕ∞
rest (↑ r) (↑ a) = ↑ (r ∸ a)
rest (↑ r) ∞     = ↑ 0
rest ∞     a     = ∞

_⊖_ : R → R → R
[0, a ] ⊖ [0, r ] = [0, a ∸∞ r ]

restᵣ : R → R → R
restᵣ [0, r ] [0, a ] = [0, rest r a ]

-- a subtraction from a sum, split over its summands

split-ℕ : ∀ g a r → (g ∸ (r ∸ a)) + (a ∸ r) ≡ (g + a) ∸ r
split-ℕ g zero    r       = trans (cong ((g ∸ r) +_) (0∸n≡0 r))
                             (trans (+-identityʳ (g ∸ r)) (cong (_∸ r) (sym (+-identityʳ g))))
split-ℕ g (suc a) zero    = refl
split-ℕ g (suc a) (suc r) = trans (split-ℕ g a r) (cong (_∸ suc r) (sym (+-suc g a)))

split∞ : ∀ g a r → (g ∸∞ rest r a) +∞ (a ∸∞ r) ≡ (g +∞ a) ∸∞ r
split∞ (↑ g) (↑ a) (↑ r) = cong ↑_ (split-ℕ g a r)
split∞ (↑ g) (↑ a) ∞     = refl
split∞ (↑ g) ∞     (↑ r) = refl
split∞ (↑ g) ∞     ∞     = refl
split∞ ∞     (↑ a) (↑ r) = refl
split∞ ∞     (↑ a) ∞     = refl
split∞ ∞     ∞     (↑ r) = refl
split∞ ∞     ∞     ∞     = refl

split : ∀ g x ρ → (g ⊖ restᵣ ρ x) ·ᵣ (x ⊖ ρ) ≡ (g ·ᵣ x) ⊖ ρ
split [0, g ] [0, a ] [0, r ] = cong [0,_] (split∞ g a r)

𝟏⊖ : ∀ ρ → 𝟏ᵣ ≡ 𝟏ᵣ ⊖ ρ
𝟏⊖ [0, ↑ r ] = cong (λ n → [0, ↑ n ]) (sym (0∸n≡0 r))
𝟏⊖ [0, ∞ ]   = refl

------------------------------------------------------------------------
-- Residuals

m∸n≤o⇒m≤o+n : ∀ m n o → m ∸ n ≤ o → m ≤ o + n
m∸n≤o⇒m≤o+n m       zero    o le = subst (m ≤_) (sym (+-identityʳ o)) le
m∸n≤o⇒m≤o+n zero    (suc n) o le = z≤n
m∸n≤o⇒m≤o+n (suc m) (suc n) o le =
  subst (suc m ≤_) (sym (+-suc o n)) (s≤s (m∸n≤o⇒m≤o+n m n o le))

m≤o+n⇒m∸n≤o : ∀ m n o → m ≤ o + n → m ∸ n ≤ o
m≤o+n⇒m∸n≤o m n o le = m≤n+o⇒m∸n≤o m n (subst (m ≤_) (+-comm o n) le)

res→ : ∀ g r d → (g ∸∞ r) ≤∞ d → g ≤∞ d +∞ r
res→ (↑ m) (↑ r) (↑ n) le = m∸n≤o⇒m≤o+n m r n le
res→ (↑ m) (↑ r) ∞     le = tt
res→ (↑ m) ∞     (↑ n) le = tt
res→ (↑ m) ∞     ∞     le = tt
res→ ∞     (↑ r) ∞     le = tt
res→ ∞     ∞     (↑ n) le = tt
res→ ∞     ∞     ∞     le = tt

res← : ∀ g r d → g ≤∞ d +∞ r → (g ∸∞ r) ≤∞ d
res← (↑ m) (↑ r) (↑ n) le = m≤o+n⇒m∸n≤o m r n le
res← (↑ m) (↑ r) ∞     le = tt
res← (↑ m) ∞     (↑ n) le = z≤n
res← (↑ m) ∞     ∞     le = tt
res← ∞     (↑ r) ∞     le = tt
res← ∞     ∞     (↑ n) le = z≤n
res← ∞     ∞     ∞     le = tt

⊖-residual : ∀ ρ g → IsResidual ρ g (g ⊖ ρ)
⊖-residual [0, r ] [0, g ] = record
  { res⇒ = λ { [0, d ] → res→ g r d }
  ; ⇒res = λ { [0, d ] → res← g r d }
  }

residual : ∀ ρ g → Residual ρ g
residual ρ g = g ⊖ ρ , ⊖-residual ρ g

------------------------------------------------------------------------
-- Lowerings

lower : ∀ {n} → OCtx ∅ˢ n → R → OCtx ∅ˢ n
lower []        ρ = []
lower (Δ ▶ s)   ρ = Δ ▶ s
lower (Γ ∷ A)   ρ = lower Γ ρ ∷ A
lower (Γ ⟨ x ⟩) ρ = lower Γ (restᵣ ρ (valʳ x)) ⟨ rconst (valʳ x ⊖ ρ) ⟩

lower-ty : ∀ {n} → (Γ : OCtx ∅ˢ n) → (ρ : R) → (j : Fin n)
         → lookup-ty (lower Γ ρ) j ≡ lookup-ty Γ j
lower-ty (Γ ∷ A)   ρ zero    = refl
lower-ty (Γ ∷ A)   ρ (suc j) = lower-ty Γ ρ j
lower-ty (Γ ⟨ x ⟩) ρ j       = lower-ty Γ (restᵣ ρ (valʳ x)) j

lower-dfs : ∀ {n} → (Γ : OCtx ∅ˢ n) → (ρ : R) → defs (lower Γ ρ) ≡ defs Γ
lower-dfs []        ρ = refl
lower-dfs (Δ ▶ s)   ρ = refl
lower-dfs (Γ ∷ A)   ρ = lower-dfs Γ ρ
lower-dfs (Γ ⟨ x ⟩) ρ = lower-dfs Γ (restᵣ ρ (valʳ x))

lower-gr : ∀ {n} → (Γ : OCtx ∅ˢ n) → (ρ : R) → (j : Fin n)
         → valʳ (lookup-gr (lower Γ ρ) j) ≡ valʳ (lookup-gr Γ j) ⊖ ρ
lower-gr (Γ ∷ A)   ρ zero    = 𝟏⊖ ρ
lower-gr (Γ ∷ A)   ρ (suc j) = lower-gr Γ ρ j
lower-gr (Γ ⟨ x ⟩) ρ j       =
  trans (cong (_·ᵣ (valʳ x ⊖ ρ)) (lower-gr Γ (restᵣ ρ (valʳ x)) j))
        (split (valʳ (lookup-gr Γ j)) (valʳ x) ρ)

lowering : (ρ : R) → ∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ
lowering ρ {n} Γ = record
  { size     = n
  ; ctx      = lower Γ ρ
  ; emb      = λ i → i
  ; back     = λ j _ → j
  ; emb-back = λ _ _ → refl
  ; back-emb = λ _ _ → refl
  ; ctx-ty   = lower-ty Γ ρ
  ; ctx-dfs  = lower-dfs Γ ρ
  ; ctx-res  = λ i → subst (IsResidual ρ (valʳ (lookup-gr Γ i))) (sym (lower-gr Γ ρ i))
                           (⊖-residual ρ (valʳ (lookup-gr Γ i)))
  }

------------------------------------------------------------------------
-- Left adjoints

left-adjoint : (ρ : R) → LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ)
left-adjoint ρ = lowering⇒left-adjoint (lowering ρ)

PRA-everywhere : (ρ : R) → PRA {∅ˢ} ∅ᴴ (rconst ρ)
PRA-everywhere ρ = LeftAdjoint⇒PRA ∅ᴴ (left-adjoint ρ)

[0,2]≰𝟏 : ¬ ([0, ↑ 2 ] ≾ᵣ 𝟏ᵣ)
[0,2]≰𝟏 = toWitnessFalse {a? = [0, ↑ 2 ] ≾ᵣ? 𝟏ᵣ} tt

left-adjoint-[0,2] : LeftAdjoint {∅ˢ} ∅ᴴ (rconst [0, ↑ 2 ]) × ¬ ([0, ↑ 2 ] ≃ᵣ 𝟏ᵣ)
left-adjoint-[0,2] = left-adjoint [0, ↑ 2 ] , λ e → [0,2]≰𝟏 (proj₁ e)

PRA-[0,2] : PRA {∅ˢ} ∅ᴴ (rconst [0, ↑ 2 ])
PRA-[0,2] = PRA-everywhere [0, ↑ 2 ]
