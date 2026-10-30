------------------------------------------------------------------------
-- The syntactic equivalence is contained in the equational theory.    --
-- The converse fails: the equational theory has further βη axioms.    --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module ClosedCalculus.EquationalTheory.Alignment (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import ClosedCalculus.Syntax.Contexts        S
open import ClosedCalculus.Syntax.Terms           S
open import ClosedCalculus.Syntax.Renaming.Action S
open import ClosedCalculus.Syntax.Renaming        S
open import ClosedCalculus.Syntax.Substitution    S
open import ClosedCalculus.Syntax.Types           S

open import ClosedCalculus.Syntax.Terms.Equivalence S

open import ClosedCalculus.EquationalTheory.EquationalTheory S

≡→==ᵛ : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≡ V' → Γ ⊢V⦂ V == V'
≡→==ᵛ refl = V-refl

≡→==ᶜ : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≡ M' → Γ ⊢C⦂ M == M'
≡→==ᶜ refl = C-refl
