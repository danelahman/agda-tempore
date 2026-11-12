----------------------------------------------------------------------------
-- Interpretation of the operational semantics' states, and of the        --
-- configurations built from them.                                        --
--                                                                        --
-- A state `𝕊 : State []` is a telescope of modalities and cells:         --
-- `_⟨ ρ ⟩ₛ` records that `ρ` worth of time has passed, and `_∷ₛ_ 𝕊 V`    --
-- allocates a cell together with the value `V` stored in it. A state     --
-- thus carries all of its data: it is not a store threaded through a     --
-- state monad, but an environment for its own context `toCtx 𝕊`.         --
--                                                                        --
-- The modalities `⟨ ρ ⟩` need not have global points (`⟨ ρ ⟩ᵒ X` is a    --
-- Kripke possibility, and near time 0 there is no `ρ`-past to be found), --
-- so the state supplies only the cells. `⟦ 𝕊 ⟧ˢ` is a morphism out of    --
-- the state's history `hist 𝕊`, the modality-only residue of `toCtx 𝕊`,  --
-- and the passage of time enters from outside it (in the operational     --
-- semantics, via `DELAY`).                                               --
--                                                                        --
-- The cell clause of `⟦_⟧ˢ` is the morphism that `⟦ box V M ⟧ᶜᵗ`         --
-- precomposes with: allocating a resource and extending the store are    --
-- the same map, so `BOX` is an equation rather than a state transition.  --
----------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.DenotationalSemantics.Interpretation.State
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Types     S
open import MonomorphicCalculus.Syntax.Contexts  S
open import MonomorphicCalculus.Syntax.Terms     S
open import MonomorphicCalculus.Syntax.Renaming  S

open import Data.Product using (_,_; _×_)
open import Data.Unit using (⊤; tt)

open import MonomorphicCalculus.OperationalSemantics.State S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣)
open Monad Mon using (Tᵒ)

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE

-- The history of a state: the modalities it has accumulated, with the cells
-- dropped. This is the part of `toCtx 𝕊` that the state cannot itself
-- supply, and hence the domain of its interpretation.

hist : ∀ {Γ} → State Γ → Ctx
hist ∅         = []
hist (𝕊 ⟨ ρ ⟩ₛ) = hist 𝕊 ⟨ ρ ⟩
hist (𝕊 ∷ₛ V)  = hist 𝕊

-- Parametricity of the values a state stores: `⟦_⟧ˢ` interprets them, so it
-- needs their certificates, one per cell.

Paramˢ : ∀ {Γ} → State Γ → Set
Paramˢ ∅         = ⊤
Paramˢ (𝕊 ⟨ ρ ⟩ₛ) = Paramˢ 𝕊
Paramˢ (𝕊 ∷ₛ V)  = Paramˢ 𝕊 × Paramᵛ V

-- The state as an environment for its own context.
--
--   * a modality is passed through by the context modality's functorial action;
--   * a cell is filled by the value stored in it, boxed up by the
--     adjunction unit (`[ ρ ]ᶠ ⟦ V ⟧ ∘ᵐ η⊣`, the `box` morphism).
--
-- The stored value lives in `[] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩`, so it is first
-- reindexed along the left unit of context concatenation.

⟦_⟧ˢ : (𝕊 : State []) → Paramˢ 𝕊 → ⟦ hist 𝕊 ⟧ᶜᵗˣ →ᵐ ⟦ toCtx 𝕊 ⟧ᶜᵗˣ
⟦ ∅ ⟧ˢ         _  = idᵐ
⟦ 𝕊 ⟨ ρ ⟩ₛ ⟧ˢ  p  = ⟨ ρ ⟩ᶠ (⟦ 𝕊 ⟧ˢ p)
⟦ _∷ₛ_ {A} {ρ} 𝕊 V ⟧ˢ (pS , pV) =
  ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ {toCtx 𝕊 ⟨ ρ ⟩}) ⟧ʳ) ∘ᵐ η⊣ ⟩ᵐ
  ∘ᵐ ⟦ 𝕊 ⟧ˢ pS

-- The values a state stores are exactly what a resource lookup returns, so a
-- state's certificate hands one out for every cell.

resource-lookupᴾ : ∀ {Γ ρ ρ' A} → (𝕊 : State Γ) → (x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊)
                 → Paramˢ 𝕊 → Paramᵛ (resource-lookup 𝕊 x)
resource-lookupᴾ (𝕊 ⟨ _ ⟩ₛ) (Tl-⟨⟩ x) pS        = resource-lookupᴾ 𝕊 x pS
resource-lookupᴾ (𝕊 ∷ₛ V)   Hd        (_ , pV)  = pV
resource-lookupᴾ (𝕊 ∷ₛ _)   (Tl-∷ x)  (pS , _)  = resource-lookupᴾ 𝕊 x pS
