------------------------------------------------------------------
-- Closed contexts in the mirrored language                      --
--                                                                --
-- The context-level counterpart of `⌜_⌝ᵛ`: an original context   --
-- embeds into a mirrored context of any scope, with its types    --
-- embedded and its locks read as grade constants. No barrier     --
-- former is produced — `_ᴱ` is a function on original contexts,  --
-- not a former.                                                  --
--                                                                --
-- `skel Γ` is the number of variables of `Γ`, which is the index --
-- the mirrored context carries.                                  --
------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.Open.ClosedContexts (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts S
open import Syntax.Types    S

open import Inference.Open.Grades    S
open import Inference.Open.Types     S
open import Inference.Open.Contexts  S
open import Inference.Open.Subst     S
open import Inference.Open.Grounding S

--------------------------------------------------------------
-- The number of variables of an original context            --
--------------------------------------------------------------

skel : Ctx → ℕ
skel []        = 0
skel (Γ ∷ A)   = suc (skel Γ)
skel (Γ ⟨ ρ ⟩) = skel Γ

--------------------------------------------------------------
-- The embedding                                             --
--------------------------------------------------------------

⌜_⌝ᶜᵗˣ : ∀ {Θ} → (Γ : Ctx) → OCtx Θ (skel Γ)
⌜ []      ⌝ᶜᵗˣ = []
⌜ Γ ∷ A   ⌝ᶜᵗˣ = ⌜ Γ ⌝ᶜᵗˣ ∷ ⌜ A ⌝ᵛ
⌜ Γ ⟨ ρ ⟩ ⌝ᶜᵗˣ = ⌜ Γ ⌝ᶜᵗˣ ⟨ rconst ρ ⟩

--------------------------------------------------------------
-- An embedded context has no variables to substitute for,   --
-- and grounds back to itself                                --
--------------------------------------------------------------

⌜⌝ᶜᵗˣ-subst : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (Γ : Ctx)
            → ⌜ Γ ⌝ᶜᵗˣ [ σ ]ᶜᵗˣ ≡ ⌜ Γ ⌝ᶜᵗˣ
⌜⌝ᶜᵗˣ-subst σ []        = refl
⌜⌝ᶜᵗˣ-subst σ (Γ ∷ A)   = cong₂ _∷_ (⌜⌝ᶜᵗˣ-subst σ Γ) (⌜⌝ᵛ-subst σ A)
⌜⌝ᶜᵗˣ-subst σ (Γ ⟨ ρ ⟩) = cong (_⟨ rconst ρ ⟩) (⌜⌝ᶜᵗˣ-subst σ Γ)

⌜⌝ᶜᵗˣ-ground : ∀ {Θ} → (θ : Grounding Θ) → (Γ : Ctx)
             → ⟦ ⌜ Γ ⌝ᶜᵗˣ ⟧ᶜᵗˣ θ ≡ Γ
⌜⌝ᶜᵗˣ-ground θ []        = refl
⌜⌝ᶜᵗˣ-ground θ (Γ ∷ A)   = cong₂ _∷_ (⌜⌝ᶜᵗˣ-ground θ Γ) (⌜⌝ᵛ-ground A)
⌜⌝ᶜᵗˣ-ground θ (Γ ⟨ ρ ⟩) = cong (_⟨ ρ ⟩) (⌜⌝ᶜᵗˣ-ground θ Γ)
