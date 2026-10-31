------------------------------------------------------------------------
-- The syntactic equivalence is contained in the equational theory.   --
-- The converse fails: the equational theory has further βη axioms.   --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.EquationalTheory.Alignment (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Substitution    S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Terms.Equivalence S

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

≡→≡ᵗʰᵛ : ∀ {Γ A} {V V' : Γ ⊢ᵛ⦂ A} → V ≡ V' → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
≡→≡ᵗʰᵛ refl = V-refl

≡→≡ᵗʰᶜ : ∀ {Γ C} {M M' : Γ ⊢ᶜ⦂ C} → M ≡ M' → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
≡→≡ᵗʰᶜ refl = C-refl
