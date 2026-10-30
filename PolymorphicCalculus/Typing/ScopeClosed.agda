------------------------------------------------------------------
-- Scope-closed typing of run-time terms                        --
--                                                              --
-- `Γ ⊢ᵛ V ⦂ X` and `Γ ⊢ᶜ M ⦂ C`: a derivation over the empty    --
-- scope whose run-time erasure is the term, under no           --
-- hypotheses (`∅ᴴ`). Handler clauses in it are typed over the  --
-- scope of their own variable, an ordering at it entailed by   --
-- rule Truth, the theory of the grade system.                  --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax)

open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.ScopeClosed (S : LanguageSpec) where

open import PolymorphicCalculus.Syntax.Types    S
open import PolymorphicCalculus.Syntax.Contexts S
open import PolymorphicCalculus.Hypotheses      S
open import PolymorphicCalculus.Typing          S
open import PolymorphicCalculus.Typing.Renaming S using (∥_∥ᵛ; ∥_∥ᶜ)
open import PolymorphicCalculus.Syntax.Run      S

infix 4 _⊢ᵛ_⦂_ _⊢ᶜ_⦂_

_⊢ᵛ_⦂_ : ∀ {n} → OCtx ∅ˢ n → RunV n → OVType ∅ˢ → Set
Γ ⊢ᵛ V ⦂ X = Σ[ D ∈ ∅ᴴ ∣ Γ ⊢V⦂ X ] ∥ D ∥ᵛ ≡ V

_⊢ᶜ_⦂_ : ∀ {n} → OCtx ∅ˢ n → RunC n → OCType ∅ˢ → Set
Γ ⊢ᶜ M ⦂ C = Σ[ D ∈ ∅ᴴ ∣ Γ ⊢C⦂ C ] ∥ D ∥ᶜ ≡ M
