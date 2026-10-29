------------------------------------------------------------------
-- Scope-closed typing of run-time terms                        --
--                                                              --
-- `Γ ⊢ᵛ V ⦂ X` and `Γ ⊢ᶜ M ⦂ C`: a derivation over the empty    --
-- scope whose run-time erasure is the term, its hypotheses the --
-- closed quantified orderings that hold (`⊤ᴴ`). Handler        --
-- clauses in it are typed over the scope of their own          --
-- variable, an ordering at it entailed by an instance of one   --
-- of those hypotheses.                                         --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax)

open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.ScopeClosed (S : LanguageSpec) where

open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Hypotheses      S
open import OpenCalculus.Typing          S
open import OpenCalculus.Typing.Renaming S using (∥_∥ᵛ; ∥_∥ᶜ)
open import OpenCalculus.Syntax.Run      S

infix 4 _⊢ᵛ_⦂_ _⊢ᶜ_⦂_

_⊢ᵛ_⦂_ : ∀ {n} → OCtx ∅ˢ n → RunV n → OVType ∅ˢ → Set
Γ ⊢ᵛ V ⦂ X = Σ[ D ∈ ⊤ᴴ ∣ Γ ⊢V⦂ X ] ∥ D ∥ᵛ ≡ V

_⊢ᶜ_⦂_ : ∀ {n} → OCtx ∅ˢ n → RunC n → OCType ∅ˢ → Set
Γ ⊢ᶜ M ⦂ C = Σ[ D ∈ ⊤ᴴ ∣ Γ ⊢C⦂ C ] ∥ D ∥ᶜ ≡ M
