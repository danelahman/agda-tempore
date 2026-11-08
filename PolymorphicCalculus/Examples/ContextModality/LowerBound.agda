------------------------------------------------------------------------
-- The context modality at lower bounds on time                       --
--                                                                    --
-- `⊤ = 𝟏`, so a grade `g` lies below `⊤ · ρ` exactly when its bound  --
-- is at least that of `ρ`, and then its residual by `ρ` is the       --
-- difference of the bounds (`residual`); otherwise it has none       --
-- (`no-residual`). A lowering subtracts `ρ` from the modalities from --
-- the right and drops the variables it reaches first (`cut`), so     --
-- `L_ρ` has a left adjoint at every grade (`left-adjoint`) and is a  --
-- parametric right adjoint (`PRA-everywhere`); in particular at      --
-- `[1,∞⟩`, which is not equivalent to `𝟏` (`left-adjoint-[1,∞⟩`).    --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (0∸n≡0; +-suc; +-identityʳ; +-comm; m≤n+o⇒m∸n≤o; m∸n+n≡m; m+n∸n≡m;
         ∸-monoˡ-≤; +-monoˡ-≤)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Grades.Base
open import Grades.Examples.Time.LowerBound
open import Grades.Examples.System.Identity using (identity-grade-system)
open import Language.BaseTypes using (noBaseTypes)
open import Language.Spec
import Language.Operations as Ops

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Examples.ContextModality.LowerBound where

G : GradeSystem
G = identity-grade-system lower-bound

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
-- Bounds and their truncated subtraction

bd : R → ℕ
bd [ n ,+∞⟩ = n

bd-· : ∀ y x → bd (y ·ᵣ x) ≡ bd y + bd x
bd-· [ m ,+∞⟩ [ n ,+∞⟩ = refl

_⊖_ : R → ℕ → R
[ a ,+∞⟩ ⊖ r = [ a ∸ r ,+∞⟩

-- a subtraction from a sum, split over its summands

split-ℕ : ∀ g a r → (g ∸ (r ∸ a)) + (a ∸ r) ≡ (g + a) ∸ r
split-ℕ g zero    r       = trans (cong ((g ∸ r) +_) (0∸n≡0 r))
                             (trans (+-identityʳ (g ∸ r)) (cong (_∸ r) (sym (+-identityʳ g))))
split-ℕ g (suc a) zero    = refl
split-ℕ g (suc a) (suc r) = trans (split-ℕ g a r) (cong (_∸ suc r) (sym (+-suc g a)))

split : ∀ y x r → (y ⊖ (r ∸ bd x)) ·ᵣ (x ⊖ r) ≡ (y ·ᵣ x) ⊖ r
split [ g ,+∞⟩ [ a ,+∞⟩ r = cong [_,+∞⟩ (split-ℕ g a r)

m∸n≤o⇒m≤o+n : ∀ m n o → m ∸ n ≤ o → m ≤ o + n
m∸n≤o⇒m≤o+n m       zero    o le = subst (m ≤_) (sym (+-identityʳ o)) le
m∸n≤o⇒m≤o+n zero    (suc n) o le = z≤n
m∸n≤o⇒m≤o+n (suc m) (suc n) o le =
  subst (suc m ≤_) (sym (+-suc o n)) (s≤s (m∸n≤o⇒m≤o+n m n o le))

------------------------------------------------------------------------
-- Residuals

below-⊤ρ : ∀ y ρ → y ≾ᵣ ⊤ᵣ ·ᵣ ρ → bd ρ ≤ bd y
below-⊤ρ [ a ,+∞⟩ [ r ,+∞⟩ le = le

⊖-residual : ∀ ρ y → bd ρ ≤ bd y → IsResidual ρ y (y ⊖ bd ρ)
⊖-residual [ r ,+∞⟩ [ a ,+∞⟩ r≤a = record
  { res⇒ = λ { [ n ,+∞⟩ le →
               subst (n + r ≤_) (m∸n+n≡m r≤a) (+-monoˡ-≤ r le) }
  ; ⇒res = λ { [ n ,+∞⟩ le →
               subst (_≤ a ∸ r) (m+n∸n≡m n r) (∸-monoˡ-≤ r le) }
  }

residual : ∀ ρ g → g ≾ᵣ ⊤ᵣ ·ᵣ ρ → Residual ρ g
residual ρ g le = g ⊖ bd ρ , ⊖-residual ρ g (below-⊤ρ g ρ le)

no-residual : ∀ ρ g → ¬ (g ≾ᵣ ⊤ᵣ ·ᵣ ρ) → ¬ Residual ρ g
no-residual ρ g n res = n (residual-bounded res)

------------------------------------------------------------------------
-- Cuts: the variables of `Γ` at bounds `≥ r`, with `r` subtracted

record Cut (r : ℕ) {n : ℕ} (Γ : OCtx ∅ˢ n) : Set where
  field
    size     : ℕ
    ctx      : OCtx ∅ˢ size
    emb      : Fin size → Fin n
    back     : (j : Fin n) → r ≤ bd (valʳ (lookup-gr Γ j)) → Fin size
    emb-back : ∀ j p → emb (back j p) ≡ j
    back-emb : ∀ i p → back (emb i) p ≡ i
    ctx-ty   : ∀ i → lookup-ty ctx i ≡ lookup-ty Γ (emb i)
    ctx-dfs  : defs ctx ≡ defs Γ
    ctx-gr   : ∀ i → valʳ (lookup-gr ctx i) ≡ valʳ (lookup-gr Γ (emb i)) ⊖ r
    emb-kept : ∀ i → r ≤ bd (valʳ (lookup-gr Γ (emb i)))

cut : (r : ℕ) → ∀ {n} → (Γ : OCtx ∅ˢ n) → Cut r Γ
cut r [] = record
  { size = 0 ; ctx = [] ; emb = λ () ; back = λ () ; emb-back = λ () ; back-emb = λ ()
  ; ctx-ty = λ () ; ctx-dfs = refl ; ctx-gr = λ () ; emb-kept = λ () }
cut r (Δ ▶ s) = record
  { size = 0 ; ctx = Δ ▶ s ; emb = λ () ; back = λ () ; emb-back = λ () ; back-emb = λ ()
  ; ctx-ty = λ () ; ctx-dfs = refl ; ctx-gr = λ () ; emb-kept = λ () }
cut zero (Γ ∷ A) = record
  { size     = suc size
  ; ctx      = ctx ∷ A
  ; emb      = λ { zero → zero ; (suc i) → suc (emb i) }
  ; back     = λ { zero _ → zero ; (suc j) p → suc (back j p) }
  ; emb-back = λ { zero _ → refl ; (suc j) p → cong suc (emb-back j p) }
  ; back-emb = λ { zero _ → refl ; (suc i) p → cong suc (back-emb i p) }
  ; ctx-ty   = λ { zero → refl ; (suc i) → ctx-ty i }
  ; ctx-dfs  = ctx-dfs
  ; ctx-gr   = λ { zero → refl ; (suc i) → ctx-gr i }
  ; emb-kept = λ { zero → z≤n ; (suc i) → emb-kept i }
  }
  where open Cut (cut zero Γ)
cut (suc r) (Γ ∷ A) = record
  { size     = size
  ; ctx      = ctx
  ; emb      = λ i → suc (emb i)
  ; back     = λ { zero () ; (suc j) p → back j p }
  ; emb-back = λ { zero () ; (suc j) p → cong suc (emb-back j p) }
  ; back-emb = back-emb
  ; ctx-ty   = ctx-ty
  ; ctx-dfs  = ctx-dfs
  ; ctx-gr   = ctx-gr
  ; emb-kept = emb-kept
  }
  where open Cut (cut (suc r) Γ)
cut r (Γ ⟨ x ⟩) = record
  { size     = size
  ; ctx      = ctx ⟨ rconst (valʳ x ⊖ r) ⟩
  ; emb      = emb
  ; back     = λ j p → back j (kept j p)
  ; emb-back = λ j p → emb-back j (kept j p)
  ; back-emb = λ i p → back-emb i (kept (emb i) p)
  ; ctx-ty   = ctx-ty
  ; ctx-dfs  = ctx-dfs
  ; ctx-gr   = λ i →
      trans (cong (_·ᵣ (valʳ x ⊖ r)) (ctx-gr i)) (split (valʳ (lookup-gr Γ (emb i))) (valʳ x) r)
  ; emb-kept = λ i →
      subst (r ≤_) (sym (bd-· (valʳ (lookup-gr Γ (emb i))) (valʳ x)))
            (m∸n≤o⇒m≤o+n r (bd (valʳ x)) _ (emb-kept i))
  }
  where
  open Cut (cut (r ∸ bd (valʳ x)) Γ)

  kept : (j : Fin _) → r ≤ bd (valʳ (lookup-gr Γ j) ·ᵣ valʳ x)
       → r ∸ bd (valʳ x) ≤ bd (valʳ (lookup-gr Γ j))
  kept j p = m≤n+o⇒m∸n≤o r (bd (valʳ x))
               (subst (r ≤_) (trans (bd-· (valʳ (lookup-gr Γ j)) (valʳ x))
                                    (+-comm (bd (valʳ (lookup-gr Γ j))) (bd (valʳ x)))) p)

lowering : (ρ : R) → ∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ
lowering ρ Γ = record
  { size     = size
  ; ctx      = ctx
  ; emb      = emb
  ; back     = λ j p → back j (below-⊤ρ _ ρ p)
  ; emb-back = λ j p → emb-back j _
  ; back-emb = λ i p → back-emb i _
  ; ctx-ty   = ctx-ty
  ; ctx-dfs  = ctx-dfs
  ; ctx-res  = λ i → subst (IsResidual ρ (valʳ (lookup-gr Γ (emb i)))) (sym (ctx-gr i))
                           (⊖-residual ρ _ (emb-kept i))
  }
  where open Cut (cut (bd ρ) Γ)

------------------------------------------------------------------------
-- Left adjoints

left-adjoint : (ρ : R) → LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ)
left-adjoint ρ = lowering⇒left-adjoint (lowering ρ)

PRA-everywhere : (ρ : R) → PRA {∅ˢ} ∅ᴴ (rconst ρ)
PRA-everywhere ρ = LeftAdjoint⇒PRA ∅ᴴ (left-adjoint ρ)

[1,∞⟩≴𝟏 : ¬ (𝟏ᵣ ≾ᵣ [ 1 ,+∞⟩)
[1,∞⟩≴𝟏 = toWitnessFalse {a? = 𝟏ᵣ ≾ᵣ? [ 1 ,+∞⟩} tt

left-adjoint-[1,∞⟩ : LeftAdjoint {∅ˢ} ∅ᴴ (rconst [ 1 ,+∞⟩) × ¬ ([ 1 ,+∞⟩ ≃ᵣ 𝟏ᵣ)
left-adjoint-[1,∞⟩ = left-adjoint [ 1 ,+∞⟩ , λ e → [1,∞⟩≴𝟏 (proj₂′ e)
  where
  proj₂′ : ∀ {a b : R} → a ≃ᵣ b → b ≾ᵣ a
  proj₂′ (_ , q) = q
