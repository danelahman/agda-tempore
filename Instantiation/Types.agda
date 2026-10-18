------------------------------------------------------------------
-- Declarative instances and the meaning of open types          --
--                                                              --
-- A declarative instance `σ : DInst Θ` sends the type          --
-- variables of `Θ` to arbitrary closed value types and its     --
-- resource-grade and effect-grade variables to arbitrary       --
-- grades. Open types and contexts are interpreted at `σ`       --
-- structurally (`⟦_⟧ᵛ`, `⟦_⟧ᶜ`, `⟦_⟧ᶜᵗˣ`): a variable is       --
-- looked up in `σ`, each former goes to its closed             --
-- counterpart, and a grade expression is evaluated in the      --
-- carrier (`⟦_⟧ʳ`, `⟦_⟧ᵉ`).                                    --
------------------------------------------------------------------

open import Data.Fin using (zero; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module Instantiation.Types (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types    S
open import Syntax.Contexts S

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S

------------------------------------------------------------------------
-- Declarative instances

record DInst (Θ : Scope) : Set where
  constructor dinst
  field
    ty  : TyVar Θ → VType                  -- type variables to closed types
    res : RVar Θ → R                       -- resource-grade variables
    eff : EVar Θ → E                       -- effect-grade variables

open DInst public

-- Extension by an effect grade for the newly bound variable

infixl 30 _,ᵉᴰ_

_,ᵉᴰ_ : ∀ {Θ} → DInst Θ → E → DInst (Θ +e)
σ ,ᵉᴰ c = dinst (ty σ) (res σ) (λ { zero → c ; (suc i) → eff σ i })

------------------------------------------------------------------------
-- Interpretation

⟦_⟧ᵉ : ∀ {Θ} → EExp Θ → DInst Θ → E
⟦ evar i ⟧ᵉ    σ = eff σ i
⟦ econst c ⟧ᵉ  σ = c
⟦ ε ·̂ₑ ε' ⟧ᵉ   σ = ⟦ ε ⟧ᵉ σ ·ₑ ⟦ ε' ⟧ᵉ σ
⟦ ε ⊔̂ₑ ε' ⟧ᵉ   σ = ⟦ ε ⟧ᵉ σ ⊔ₑ ⟦ ε' ⟧ᵉ σ

⟦_⟧ʳ : ∀ {Θ} → RExp Θ → DInst Θ → R
⟦ rvar i ⟧ʳ    σ = res σ i
⟦ rconst c ⟧ʳ  σ = c
⟦ ρ ·̂ᵣ ρ' ⟧ʳ   σ = ⟦ ρ ⟧ʳ σ ·ᵣ ⟦ ρ' ⟧ʳ σ
⟦ ρ ⊔̂ᵣ ρ' ⟧ʳ   σ = ⟦ ρ ⟧ʳ σ ⊔ᵣ ⟦ ρ' ⟧ʳ σ
⟦ ∣ ε ∣̂ᵉ ⟧ʳ    σ = mapᵉ (⟦ ε ⟧ᵉ σ)

mutual

  ⟦_⟧ᵛ : ∀ {Θ} → OVType Θ → DInst Θ → VType
  ⟦ tvar α ⟧ᵛ   σ = ty σ α
  ⟦ Base b ⟧ᵛ   σ = Base b
  ⟦ Unit ⟧ᵛ     σ = Unit
  ⟦ Bool ⟧ᵛ     σ = Bool
  ⟦ Nat ⟧ᵛ      σ = Nat
  ⟦ A |×| B ⟧ᵛ  σ = ⟦ A ⟧ᵛ σ |×| ⟦ B ⟧ᵛ σ
  ⟦ A |+| B ⟧ᵛ  σ = ⟦ A ⟧ᵛ σ |+| ⟦ B ⟧ᵛ σ
  ⟦ |List| A ⟧ᵛ σ = |List| (⟦ A ⟧ᵛ σ)
  ⟦ Empty ⟧ᵛ    σ = Empty
  ⟦ A ⇒ C ⟧ᵛ    σ = ⟦ A ⟧ᵛ σ ⇒ ⟦ C ⟧ᶜ σ
  ⟦ [ ρ ] A ⟧ᵛ  σ = [ ⟦ ρ ⟧ʳ σ ] ⟦ A ⟧ᵛ σ

  ⟦_⟧ᶜ : ∀ {Θ} → OCType Θ → DInst Θ → CType
  ⟦ A ‼ ε ⟧ᶜ σ = ⟦ A ⟧ᵛ σ ‼ ⟦ ε ⟧ᵉ σ

⟦_⟧ᶜᵗˣ : ∀ {Θ n} → OCtx Θ n → DInst Θ → Ctx
⟦ [] ⟧ᶜᵗˣ      σ = []
⟦ Γ ∷ A ⟧ᶜᵗˣ   σ = ⟦ Γ ⟧ᶜᵗˣ σ ∷ ⟦ A ⟧ᵛ σ
⟦ Γ ⟨ ρ ⟩ ⟧ᶜᵗˣ σ = ⟦ Γ ⟧ᶜᵗˣ σ ⟨ ⟦ ρ ⟧ʳ σ ⟩

-- Ground types mean their closed images

⟦⌜_⌝ᵍ⟧ : ∀ {Θ} → (g : GType) → (σ : DInst Θ) → ⟦ ⌜ g ⌝ᵍ ⟧ᵛ σ ≡ type-of-gtype g
⟦⌜ Base b ⌝ᵍ⟧ σ    = refl
⟦⌜ Unit ⌝ᵍ⟧ σ      = refl
⟦⌜ Bool ⌝ᵍ⟧ σ      = refl
⟦⌜ Empty ⌝ᵍ⟧ σ     = refl
⟦⌜ A |×|ᵍ B ⌝ᵍ⟧ σ  = cong₂ _|×|_ (⟦⌜ A ⌝ᵍ⟧ σ) (⟦⌜ B ⌝ᵍ⟧ σ)
⟦⌜ [ ρ ]ᵍ A ⌝ᵍ⟧ σ  = cong ([ ρ ]_) (⟦⌜ A ⌝ᵍ⟧ σ)

------------------------------------------------------------------------
-- Weakening by an effect-grade variable, at an extended instance

module _ {Θ} (σ : DInst Θ) (c : E) where

  ⟦wkᵉ⟧ᵉ : (ε : EExp Θ) → ⟦ wkᵉ-e ε ⟧ᵉ (σ ,ᵉᴰ c) ≡ ⟦ ε ⟧ᵉ σ
  ⟦wkᵉ⟧ᵉ (evar i)   = refl
  ⟦wkᵉ⟧ᵉ (econst e) = refl
  ⟦wkᵉ⟧ᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦wkᵉ⟧ᵉ ε) (⟦wkᵉ⟧ᵉ ε')
  ⟦wkᵉ⟧ᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦wkᵉ⟧ᵉ ε) (⟦wkᵉ⟧ᵉ ε')

  ⟦wkᵉ⟧ʳ : (ρ : RExp Θ) → ⟦ wkᵉ-r ρ ⟧ʳ (σ ,ᵉᴰ c) ≡ ⟦ ρ ⟧ʳ σ
  ⟦wkᵉ⟧ʳ (rvar i)   = refl
  ⟦wkᵉ⟧ʳ (rconst r) = refl
  ⟦wkᵉ⟧ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦wkᵉ⟧ʳ ρ) (⟦wkᵉ⟧ʳ ρ')
  ⟦wkᵉ⟧ʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦wkᵉ⟧ʳ ρ) (⟦wkᵉ⟧ʳ ρ')
  ⟦wkᵉ⟧ʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦wkᵉ⟧ᵉ ε)

  mutual

    ⟦wkᵉ⟧ᵛ : (A : OVType Θ) → ⟦ wkᵉ-v A ⟧ᵛ (σ ,ᵉᴰ c) ≡ ⟦ A ⟧ᵛ σ
    ⟦wkᵉ⟧ᵛ (tvar α)   = refl
    ⟦wkᵉ⟧ᵛ (Base b)   = refl
    ⟦wkᵉ⟧ᵛ Unit       = refl
    ⟦wkᵉ⟧ᵛ Bool       = refl
    ⟦wkᵉ⟧ᵛ Nat        = refl
    ⟦wkᵉ⟧ᵛ (A |×| B)  = cong₂ _|×|_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᵛ B)
    ⟦wkᵉ⟧ᵛ (A |+| B)  = cong₂ _|+|_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᵛ B)
    ⟦wkᵉ⟧ᵛ (|List| A) = cong |List| (⟦wkᵉ⟧ᵛ A)
    ⟦wkᵉ⟧ᵛ Empty      = refl
    ⟦wkᵉ⟧ᵛ (A ⇒ C)    = cong₂ _⇒_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᶜ C)
    ⟦wkᵉ⟧ᵛ ([ ρ ] A)  = cong₂ [_]_ (⟦wkᵉ⟧ʳ ρ) (⟦wkᵉ⟧ᵛ A)

    ⟦wkᵉ⟧ᶜ : (C : OCType Θ) → ⟦ wkᵉ-c C ⟧ᶜ (σ ,ᵉᴰ c) ≡ ⟦ C ⟧ᶜ σ
    ⟦wkᵉ⟧ᶜ (A ‼ ε) = cong₂ _‼_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᵉ ε)

  ⟦wkᵉ⟧ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → ⟦ wkᵉ-ctx Γ ⟧ᶜᵗˣ (σ ,ᵉᴰ c) ≡ ⟦ Γ ⟧ᶜᵗˣ σ
  ⟦wkᵉ⟧ᶜᵗˣ []        = refl
  ⟦wkᵉ⟧ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ (⟦wkᵉ⟧ᶜᵗˣ Γ) (⟦wkᵉ⟧ᵛ A)
  ⟦wkᵉ⟧ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (⟦wkᵉ⟧ᶜᵗˣ Γ) (⟦wkᵉ⟧ʳ ρ)
